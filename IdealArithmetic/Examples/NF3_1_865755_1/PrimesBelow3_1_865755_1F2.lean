
import IdealArithmetic.Examples.NF3_1_865755_1.RI3_1_865755_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-54, -17, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-54, -17, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![29, 66, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-54, -17, 1], ![245, -32, -86], ![-4839, -615, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -66, 83]], ![![-1, -1, 1], ![33, 68, -86], ![-59, -9, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [22, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 82], [0, 1]]
 g := ![![[63, 49], [], [9], [30], [0, 44], [1]], ![[43, 34], [], [9], [30], [21, 39], [1]]]
 h' := ![![[25, 82], [0, 7], [67], [4, 3], [0, 14], [61, 25], [0, 1]], ![[0, 1], [9, 76], [67], [79, 80], [18, 69], [22, 58], [25, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [73, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [22, 58, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3098, 1876, 705]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-209, -538, 705]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![3, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![3, 1, 0]] 
 ![![83, 0, 0], ![3, 1, 0], ![81, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![3, 1, 0], ![2, 4, 5], ![279, 39, 2]]]
  hmulB := by decide  
  f := ![![![-447, -896, -1120], ![0, 18592, 0]], ![![-16, -32, -40], ![1, 664, 0]], ![![-438, -875, -1093], ![49, 18144, 0]]]
  g := ![![![1, 0, 0], ![-3, 83, 0], ![-81, 0, 83]], ![![0, 1, 0], ![-5, 4, 5], ![0, 39, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-54, -17, 1]] ![![83, 0, 0], ![3, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![249, 83, 0]], ![![-4482, -1411, 83], ![83, -83, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![3, 1, 0]]], ![![![-54, -17, 1]], ![![1, -1, -1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-67, -31, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-67, -31, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![22, 58, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-67, -31, 1], ![217, -59, -156], ![-8745, -1161, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -58, 89]], ![![-1, -1, 1], ![41, 101, -156], ![-99, -15, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [39, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 88], [0, 1]]
 g := ![![[82, 16], [64], [79], [41, 40], [15, 36], [1]], ![[0, 73], [64], [79], [14, 49], [53, 53], [1]]]
 h' := ![![[6, 88], [65, 4], [43, 8], [3, 41], [38, 29], [50, 6], [0, 1]], ![[0, 1], [0, 85], [2, 81], [71, 48], [34, 60], [86, 83], [6, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [40, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [39, 83, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15745, 8112, 7800]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2105, -4992, 7800]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-22, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-22, 1, 0]] 
 ![![89, 0, 0], ![67, 1, 0], ![86, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-22, 1, 0], ![2, -21, 5], ![279, 39, -23]]]
  hmulB := by decide  
  f := ![![![-299, 3610, -860], ![178, 15308, 0]], ![![-235, 2708, -645], ![90, 11481, 0]], ![![-282, 3488, -831], ![200, 14792, 0]]]
  g := ![![![1, 0, 0], ![-67, 89, 0], ![-86, 0, 89]], ![![-1, 1, 0], ![11, -21, 5], ![-4, 39, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-67, -31, 1]] ![![89, 0, 0], ![-22, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1958, 89, 0]], ![![-5963, -2759, 89], ![1691, 623, -178]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-22, 1, 0]]], ![![![-67, -31, 1]], ![![19, 7, -2]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-63, 29, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-63, 29, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![34, 29, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-63, 29, 1], ![337, 5, 144], ![7995, 1179, -53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -29, 97]], ![![-1, 0, 1], ![-47, -43, 144], ![101, 28, -53]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [62, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 96], [0, 1]]
 g := ![![[86, 36], [22], [2], [72], [93], [3, 1]], ![[0, 61], [22], [2], [72], [93], [6, 96]]]
 h' := ![![[3, 96], [79, 6], [52, 33], [51, 83], [21, 13], [8, 44], [0, 1]], ![[0, 1], [0, 91], [54, 64], [9, 14], [60, 84], [43, 53], [3, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [84, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [62, 94, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3057958, 1519536, 698381]
  a := ![-66, -64, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-213268, -193129, 698381]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-47, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-47, 1, 0]] 
 ![![97, 0, 0], ![50, 1, 0], ![53, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-47, 1, 0], ![2, -46, 5], ![279, 39, -48]]]
  hmulB := by decide  
  f := ![![![3994, -127479, 13860], ![-3201, -268884, 0]], ![![2058, -65671, 7140], ![-1648, -138516, 0]], ![![2207, -69654, 7573], ![-1698, -146916, 0]]]
  g := ![![![1, 0, 0], ![-50, 97, 0], ![-53, 0, 97]], ![![-1, 1, 0], ![21, -46, 5], ![9, 39, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-63, 29, 1]] ![![97, 0, 0], ![-47, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-4559, 97, 0]], ![![-6111, 2813, 97], ![3298, -1358, 97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-47, 1, 0]]], ![![![-63, 29, 1]], ![![34, -14, 1]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [55, 48, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 78, 55], [76, 22, 46], [0, 1]]
 g := ![![[66, 81, 95], [97, 22], [12, 95, 23], [46, 43], [15, 58], [1]], ![[35, 4, 27, 48], [61, 77], [12, 4, 20, 12], [20, 13], [16, 77], [70, 19, 15, 28]], ![[11, 23, 30, 93], [73, 1], [58, 5, 18, 61], [38, 24], [67, 88], [50, 33, 0, 73]]]
 h' := ![![[6, 78, 55], [5, 12, 87], [47, 26, 74], [75, 90, 86], [79, 57, 12], [46, 53, 82], [0, 1]], ![[76, 22, 46], [92, 22, 49], [66, 20, 28], [90, 24, 75], [33, 64, 66], [2, 80, 73], [6, 78, 55]], ![[0, 1], [20, 67, 66], [55, 55, 100], [31, 88, 41], [0, 81, 23], [7, 69, 47], [76, 22, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 80], []]
 b := ![[], [3, 72, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [55, 48, 19, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26791260, -8946883, -3107669]
  a := ![-5, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-265260, -88583, -30769]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![48, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![48, 1, 0]] 
 ![![103, 0, 0], ![48, 1, 0], ![45, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![48, 1, 0], ![2, 49, 5], ![279, 39, 47]]]
  hmulB := by decide  
  f := ![![![3841, 129330, 13200], ![3090, -271920, 0]], ![![1788, 60256, 6150], ![1443, -126690, 0]], ![![1659, 56503, 5767], ![1391, -118800, 0]]]
  g := ![![![1, 0, 0], ![-48, 103, 0], ![-45, 0, 103]], ![![0, 1, 0], ![-25, 49, 5], ![-36, 39, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-42, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-42, 1, 0]] 
 ![![103, 0, 0], ![61, 1, 0], ![68, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-42, 1, 0], ![2, -41, 5], ![279, 39, -43]]]
  hmulB := by decide  
  f := ![![![965, -24922, 3040], ![-618, -62624, 0]], ![![595, -14757, 1800], ![-308, -37080, 0]], ![![664, -16454, 2007], ![-342, -41344, 0]]]
  g := ![![![1, 0, 0], ![-61, 103, 0], ![-68, 0, 103]], ![![-1, 1, 0], ![21, -41, 5], ![8, 39, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-6, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-6, 1, 0]] 
 ![![103, 0, 0], ![97, 1, 0], ![15, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-6, 1, 0], ![2, -5, 5], ![279, 39, -7]]]
  hmulB := by decide  
  f := ![![![-1245, 3143, -3145], ![206, 64787, 0]], ![![-1177, 2959, -2960], ![104, 60976, 0]], ![![-177, 457, -458], ![104, 9435, 0]]]
  g := ![![![1, 0, 0], ![-97, 103, 0], ![-15, 0, 103]], ![![-1, 1, 0], ![4, -5, 5], ![-33, 39, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![48, 1, 0]] ![![103, 0, 0], ![-42, 1, 0]]
  ![![103, 0, 0], ![-32, 22, 1]] where
 M := ![![![10609, 0, 0], ![-4326, 103, 0]], ![![4944, 103, 0], ![-2014, 7, 5]]]
 hmul := by decide  
 g := ![![![![103, 0, 0], ![0, 0, 0]], ![![-10, -21, -1], ![103, 0, 0]]], ![![![48, 1, 0], ![0, 0, 0]], ![![14, -23, -1], ![108, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-32, 22, 1]] ![![103, 0, 0], ![-6, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-618, 103, 0]], ![![-3296, 2266, 103], ![515, -103, 103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-6, 1, 0]]], ![![![-32, 22, 1]], ![![5, -1, 1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![12, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![12, 1, 0]] 
 ![![107, 0, 0], ![12, 1, 0], ![12, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![12, 1, 0], ![2, 13, 5], ![279, 39, 11]]]
  hmulB := by decide  
  f := ![![![-761, -5030, -1935], ![-107, 41409, 0]], ![![-86, -559, -215], ![1, 4601, 0]], ![![-96, -565, -217], ![83, 4644, 0]]]
  g := ![![![1, 0, 0], ![-12, 107, 0], ![-12, 0, 107]], ![![0, 1, 0], ![-2, 13, 5], ![-3, 39, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![19, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![19, 1, 0]] 
 ![![107, 0, 0], ![19, 1, 0], ![10, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![19, 1, 0], ![2, 20, 5], ![279, 39, 18]]]
  hmulB := by decide  
  f := ![![![-8404, -88019, -22010], ![-2247, 471014, 0]], ![![-1505, -15617, -3905], ![-320, 83567, 0]], ![![-803, -8227, -2057], ![-111, 44020, 0]]]
  g := ![![![1, 0, 0], ![-19, 107, 0], ![-10, 0, 107]], ![![0, 1, 0], ![-4, 20, 5], ![-6, 39, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-31, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-31, 1, 0]] 
 ![![107, 0, 0], ![76, 1, 0], ![7, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-31, 1, 0], ![2, -30, 5], ![279, 39, -32]]]
  hmulB := by decide  
  f := ![![![874, -14487, 2415], ![-321, -51681, 0]], ![![625, -10288, 1715], ![-213, -36701, 0]], ![![65, -948, 158], ![6, -3381, 0]]]
  g := ![![![1, 0, 0], ![-76, 107, 0], ![-7, 0, 107]], ![![-1, 1, 0], ![21, -30, 5], ![-23, 39, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![12, 1, 0]] ![![107, 0, 0], ![19, 1, 0]]
  ![![107, 0, 0], ![-61, -15, 1]] where
 M := ![![![11449, 0, 0], ![2033, 107, 0]], ![![1284, 107, 0], ![230, 32, 5]]]
 hmul := by decide  
 g := ![![![![107, 0, 0], ![0, 0, 0]], ![![19, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![5, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-61, -15, 1]] ![![107, 0, 0], ![-31, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-3317, 107, 0]], ![![-6527, -1605, 107], ![2140, 428, -107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-31, 1, 0]]], ![![![-61, -15, 1]], ![![20, 4, -1]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-60, 48, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-60, 48, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![49, 48, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-60, 48, 1], ![375, 27, 239], ![13296, 1920, -69]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -48, 109]], ![![-1, 0, 1], ![-104, -105, 239], ![153, 48, -69]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [16, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 108], [0, 1]]
 g := ![![[64, 75], [7], [52, 38], [61, 28], [73], [66, 1]], ![[0, 34], [7], [53, 71], [56, 81], [73], [23, 108]]]
 h' := ![![[66, 108], [71, 27], [40, 15], [5, 16], [97, 79], [34, 89], [0, 1]], ![[0, 1], [0, 82], [49, 94], [80, 93], [79, 30], [22, 20], [66, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [92, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [16, 43, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3122, 1906, 780]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-322, -326, 780]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-21, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-21, 1, 0]] 
 ![![109, 0, 0], ![88, 1, 0], ![69, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-21, 1, 0], ![2, -20, 5], ![279, 39, -22]]]
  hmulB := by decide  
  f := ![![![14475, -152682, 38180], ![-4142, -832324, 0]], ![![11678, -123249, 30820], ![-3378, -671876, 0]], ![![9165, -96652, 24169], ![-2612, -526884, 0]]]
  g := ![![![1, 0, 0], ![-88, 109, 0], ![-69, 0, 109]], ![![-1, 1, 0], ![13, -20, 5], ![-15, 39, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-60, 48, 1]] ![![109, 0, 0], ![-21, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-2289, 109, 0]], ![![-6540, 5232, 109], ![1635, -981, 218]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-21, 1, 0]]], ![![![-60, 48, 1]], ![![15, -9, 2]]]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [62, 14, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [110, 102, 22], [106, 10, 91], [0, 1]]
 g := ![![[93, 32, 109], [91, 81], [25, 112], [65, 52], [4, 71, 100], [1]], ![[14, 32, 108, 62], [16, 8], [108, 44], [86, 100], [60, 105, 23, 104], [104, 41, 40, 26]], ![[16, 110, 56, 8], [27, 61], [49, 14], [40, 50], [54, 6, 57, 106], [80, 102, 90, 87]]]
 h' := ![![[110, 102, 22], [26, 83, 83], [73, 94, 9], [70, 56, 98], [91, 64, 39], [51, 99, 103], [0, 1]], ![[106, 10, 91], [74, 91, 57], [7, 66, 11], [107, 112, 65], [44, 70, 103], [79, 112, 44], [110, 102, 22]], ![[0, 1], [39, 52, 86], [73, 66, 93], [88, 58, 63], [46, 92, 84], [8, 15, 79], [106, 10, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 4], []]
 b := ![[], [75, 84, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [62, 14, 10, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![49757516, 10521882, 2981279]
  a := ![3, 21, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![440332, 93114, 26383]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![0, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![0, 1, 0]] 
 ![![127, 0, 0], ![0, 1, 0], ![102, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![0, 1, 0], ![2, 1, 5], ![279, 39, -1]]]
  hmulB := by decide  
  f := ![![![-127, -64, -320], ![0, 8128, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-102, -52, -257], ![76, 6528, 0]]]
  g := ![![![1, 0, 0], ![0, 127, 0], ![-102, 0, 127]], ![![0, 1, 0], ![-4, 1, 5], ![3, 39, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![43, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![43, 1, 0]] 
 ![![127, 0, 0], ![43, 1, 0], ![3, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![43, 1, 0], ![2, 44, 5], ![279, 39, 42]]]
  hmulB := by decide  
  f := ![![![-10544, -274515, -31200], ![-5715, 792480, 0]], ![![-3579, -92913, -10560], ![-1904, 268224, 0]], ![![-266, -6485, -737], ![-85, 18720, 0]]]
  g := ![![![1, 0, 0], ![-43, 127, 0], ![-3, 0, 127]], ![![0, 1, 0], ![-15, 44, 5], ![-12, 39, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-43, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-43, 1, 0]] 
 ![![127, 0, 0], ![84, 1, 0], ![71, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-43, 1, 0], ![2, -42, 5], ![279, 39, -44]]]
  hmulB := by decide  
  f := ![![![1398, -33847, 4030], ![-635, -102362, 0]], ![![938, -22383, 2665], ![-380, -67691, 0]], ![![767, -18922, 2253], ![-398, -57226, 0]]]
  g := ![![![1, 0, 0], ![-84, 127, 0], ![-71, 0, 127]], ![![-1, 1, 0], ![25, -42, 5], ![1, 39, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![0, 1, 0]] ![![127, 0, 0], ![43, 1, 0]]
  ![![127, 0, 0], ![-25, -42, 1]] where
 M := ![![![16129, 0, 0], ![5461, 127, 0]], ![![0, 127, 0], ![2, 44, 5]]]
 hmul := by decide  
 g := ![![![![127, 0, 0], ![0, 0, 0]], ![![43, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![1, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-25, -42, 1]] ![![127, 0, 0], ![-43, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-5461, 127, 0]], ![![-3175, -5334, 127], ![1270, 1778, -254]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-43, 1, 0]]], ![![![-25, -42, 1]], ![![10, 14, -2]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![62, 13, 4]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![62, 13, 4]] 
 ![![131, 0, 0], ![0, 131, 0], ![81, 36, 1]] where
  M :=![![![62, 13, 4], ![1142, 231, 61], ![3243, 699, 205]]]
  hmulB := by decide  
  f := ![![![36, 1, -1]], ![![-277, -2, 6]], ![![-51, 0, 1]]]
  g := ![![![-2, -1, 4], ![-29, -15, 61], ![-102, -51, 205]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [40, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [119, 130], [0, 1]]
 g := ![![[92, 62], [81, 39], [36], [94], [62], [13], [1]], ![[3, 69], [6, 92], [36], [94], [62], [13], [1]]]
 h' := ![![[119, 130], [35, 113], [5, 68], [2, 125], [116, 15], [32, 18], [91, 119], [0, 1]], ![[0, 1], [120, 18], [106, 63], [74, 6], [67, 116], [78, 113], [104, 12], [119, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [99, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [40, 12, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8595, 1813, 1888]
  a := ![-3, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1233, -505, 1888]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36, -1, 1]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-36, -1, 1]] 
 ![![131, 0, 0], ![83, 1, 0], ![47, 0, 1]] where
  M :=![![![-36, -1, 1], ![277, 2, -6], ![-375, 9, 4]]]
  hmulB := by decide  
  f := ![![![-62, -13, -4]], ![![-48, -10, -3]], ![![-47, -10, -3]]]
  g := ![![![0, -1, 1], ![3, 2, -6], ![-10, 9, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![62, 13, 4]] ![![-36, -1, 1]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-53, -46, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-53, -46, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![84, 91, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-53, -46, 1], ![187, -60, -231], ![-12930, -1746, 32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-84, -91, 137]], ![![-1, -1, 1], ![143, 153, -231], ![-114, -34, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [12, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 136], [0, 1]]
 g := ![![[6, 123], [119], [16], [11, 65], [28], [115], [1]], ![[55, 14], [119], [16], [126, 72], [28], [115], [1]]]
 h' := ![![[65, 136], [20, 64], [107, 121], [5, 4], [84, 32], [134, 24], [125, 65], [0, 1]], ![[0, 1], [70, 73], [26, 16], [128, 133], [109, 105], [50, 113], [103, 72], [65, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [48, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [12, 72, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7474, 7389, 4685]
  a := ![4, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2818, -3058, 4685]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-43, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-43, 1, 0]] 
 ![![137, 0, 0], ![94, 1, 0], ![105, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-43, 1, 0], ![2, -42, 5], ![279, 39, -44]]]
  hmulB := by decide  
  f := ![![![2409, -57784, 6880], ![-1096, -188512, 0]], ![![1674, -39643, 4720], ![-684, -129328, 0]], ![![1846, -44287, 5273], ![-841, -144480, 0]]]
  g := ![![![1, 0, 0], ![-94, 137, 0], ![-105, 0, 137]], ![![-1, 1, 0], ![25, -42, 5], ![9, 39, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-53, -46, 1]] ![![137, 0, 0], ![-43, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-5891, 137, 0]], ![![-7261, -6302, 137], ![2466, 1918, -274]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-43, 1, 0]]], ![![![-53, -46, 1]], ![![18, 14, -2]]]]
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


lemma PB264I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB264I2 : PrimesBelowBoundCertificateInterval O 79 137 264 where
  m := 11
  g := ![2, 2, 2, 1, 3, 3, 2, 1, 3, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB264I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N2]
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
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![103, 103, 103]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![127, 127, 127]
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
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
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
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N1, I103N0, I103N1, I103N2, I107N0, I107N1, I107N2, I109N1, I127N0, I127N1, I127N2, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [], [I103N0, I103N1, I103N2], [I107N0, I107N1, I107N2], [I109N1], [], [I127N0, I127N1, I127N2], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
