
import IdealArithmetic.Examples.NF3_1_565068_1.RI3_1_565068_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-11, 31, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-11, 31, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![72, 31, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-11, 31, 1], ![-45, -9, 155], ![-1386, -908, -40]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -31, 83]], ![![-1, 0, 1], ![-135, -58, 155], ![18, 4, -40]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [66, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 82], [0, 1]]
 g := ![![[13, 9], [21, 77], [70], [78], [4, 37], [1]], ![[10, 74], [23, 6], [70], [78], [47, 46], [1]]]
 h' := ![![[55, 82], [25, 80], [40, 49], [57, 30], [68, 59], [17, 55], [0, 1]], ![[0, 1], [26, 3], [79, 34], [47, 53], [76, 24], [54, 28], [55, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [44, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [66, 28, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-825, -1825, -2581]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2229, 942, -2581]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![11, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![11, 1, 0]] 
 ![![83, 0, 0], ![11, 1, 0], ![40, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![11, 1, 0], ![0, 12, 5], ![-45, -29, 11]]]
  hmulB := by decide  
  f := ![![![727, 66, 0], ![-5478, 0, 0]], ![![77, 7, 0], ![-580, 0, 0]], ![![344, 24, -3], ![-2592, 50, 0]]]
  g := ![![![1, 0, 0], ![-11, 83, 0], ![-40, 0, 83]], ![![0, 1, 0], ![-4, 12, 5], ![-2, -29, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-11, 31, 1]] ![![83, 0, 0], ![11, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![913, 83, 0]], ![![-913, 2573, 83], ![-166, 332, 166]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![11, 1, 0]]], ![![![-11, 31, 1]], ![![-2, 4, 2]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![14, -7, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![14, -7, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![14, 82, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![14, -7, 1], ![-45, -22, -35], ![324, 194, -15]]]
  hmulB := by decide  
  f := ![![![-13, 7, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -82, 89]], ![![0, -1, 1], ![5, 32, -35], ![6, 16, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [15, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 88], [0, 1]]
 g := ![![[], [], [17], [0, 73], [], [1]], ![[], [], [17], [0, 16], [], [1]]]
 h' := ![![[0, 88], [55], [12], [0, 62], [0, 47], [74], [0, 1]], ![[0, 1], [55], [12], [0, 27], [0, 42], [74], [0, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [0, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [15, 0, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-173, -848, -1430]
  a := ![-1, 1, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![223, 1308, -1430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![35, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![35, 1, 0]] 
 ![![89, 0, 0], ![35, 1, 0], ![15, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![35, 1, 0], ![0, 36, 5], ![-45, -29, 35]]]
  hmulB := by decide  
  f := ![![![561, 16, 0], ![-1424, 0, 0]], ![![175, 5, 0], ![-444, 0, 0]], ![![45, -6, -1], ![-114, 18, 0]]]
  g := ![![![1, 0, 0], ![-35, 89, 0], ![-15, 0, 89]], ![![0, 1, 0], ![-15, 36, 5], ![5, -29, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![14, -7, 1]] ![![89, 0, 0], ![35, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![3115, 89, 0]], ![![1246, -623, 89], ![445, -267, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![35, 1, 0]]], ![![![14, -7, 1]], ![![5, -3, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [17, 70, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 49, 63], [57, 47, 34], [0, 1]]
 g := ![![[74, 46, 25], [47, 12], [37, 53], [76, 64], [20, 11], [1]], ![[7, 4, 37, 17], [35, 36], [80, 49], [76, 62], [25, 86], [12, 61, 12, 78]], ![[81, 5, 92, 37], [45, 2], [46, 8], [59, 64], [32, 96], [96, 46, 12, 19]]]
 h' := ![![[3, 49, 63], [71, 29, 92], [26, 92, 77], [48, 6, 21], [46, 17, 89], [80, 27, 60], [0, 1]], ![[57, 47, 34], [73, 82, 40], [59, 25, 6], [35, 59, 7], [58, 68, 16], [17, 28, 59], [3, 49, 63]], ![[0, 1], [29, 83, 62], [42, 77, 14], [40, 32, 69], [49, 12, 89], [37, 42, 75], [57, 47, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 51], []]
 b := ![[], [10, 72, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [17, 70, 37, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-116594, 873, -3977]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1202, 9, -41]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![51, -18, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![51, -18, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![51, 83, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![51, -18, 1], ![-45, 4, -90], ![819, 513, 22]]]
  hmulB := by decide  
  f := ![![![-50, 18, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -83, 101]], ![![0, -1, 1], ![45, 74, -90], ![-3, -13, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [99, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 100], [0, 1]]
 g := ![![[47, 4], [30], [20, 16], [65], [76], [94, 1]], ![[19, 97], [30], [9, 85], [65], [76], [87, 100]]]
 h' := ![![[94, 100], [44, 2], [40, 38], [34, 97], [45, 60], [87, 51], [0, 1]], ![[0, 1], [30, 99], [77, 63], [62, 4], [29, 41], [33, 50], [94, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [30, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [99, 7, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-784, -2379, -3588]
  a := ![1, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1804, 2925, -3588]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-11, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-11, 1, 0]] 
 ![![101, 0, 0], ![90, 1, 0], ![79, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-11, 1, 0], ![0, -10, 5], ![-45, -29, -11]]]
  hmulB := by decide  
  f := ![![![617, -56, 0], ![5656, 0, 0]], ![![562, -51, 0], ![5152, 0, 0]], ![![485, -36, -4], ![4446, 81, 0]]]
  g := ![![![1, 0, 0], ![-90, 101, 0], ![-79, 0, 101]], ![![-1, 1, 0], ![5, -10, 5], ![34, -29, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![51, -18, 1]] ![![101, 0, 0], ![-11, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-1111, 101, 0]], ![![5151, -1818, 101], ![-606, 202, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-11, 1, 0]]], ![![![51, -18, 1]], ![![-6, 2, -1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![27, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![27, 1, 0]] 
 ![![103, 0, 0], ![27, 1, 0], ![96, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![27, 1, 0], ![0, 28, 5], ![-45, -29, 27]]]
  hmulB := by decide  
  f := ![![![595, 22, 0], ![-2266, 0, 0]], ![![135, 5, 0], ![-514, 0, 0]], ![![564, 4, -3], ![-2148, 62, 0]]]
  g := ![![![1, 0, 0], ![-27, 103, 0], ![-96, 0, 103]], ![![0, 1, 0], ![-12, 28, 5], ![-18, -29, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-18, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-18, 1, 0]] 
 ![![103, 0, 0], ![85, 1, 0], ![83, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-18, 1, 0], ![0, -17, 5], ![-45, -29, -18]]]
  hmulB := by decide  
  f := ![![![1387, -77, 0], ![7931, 0, 0]], ![![1117, -62, 0], ![6387, 0, 0]], ![![1103, -51, -3], ![6307, 62, 0]]]
  g := ![![![1, 0, 0], ![-85, 103, 0], ![-83, 0, 103]], ![![-1, 1, 0], ![10, -17, 5], ![38, -29, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-10, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-10, 1, 0]] 
 ![![103, 0, 0], ![93, 1, 0], ![85, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-10, 1, 0], ![0, -9, 5], ![-45, -29, -10]]]
  hmulB := by decide  
  f := ![![![351, -35, 0], ![3605, 0, 0]], ![![321, -32, 0], ![3297, 0, 0]], ![![285, -23, -3], ![2927, 62, 0]]]
  g := ![![![1, 0, 0], ![-93, 103, 0], ![-85, 0, 103]], ![![-1, 1, 0], ![4, -9, 5], ![34, -29, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![27, 1, 0]] ![![103, 0, 0], ![-18, 1, 0]]
  ![![103, 0, 0], ![47, 2, 1]] where
 M := ![![![10609, 0, 0], ![-1854, 103, 0]], ![![2781, 103, 0], ![-486, 10, 5]]]
 hmul := by decide  
 g := ![![![![56, -2, -1], ![103, 0, 0]], ![![-18, 1, 0], ![0, 0, 0]]], ![![![-20, -1, -1], ![103, 0, 0]], ![![-7, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![47, 2, 1]] ![![103, 0, 0], ![-10, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-1030, 103, 0]], ![![4841, 206, 103], ![-515, 0, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-10, 1, 0]]], ![![![47, 2, 1]], ![![-5, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![42, 38, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![42, 38, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![42, 38, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![42, 38, 1], ![-45, 51, 190], ![-1701, -1111, 13]]]
  hmulB := by decide  
  f := ![![![-41, -38, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -38, 107]], ![![0, 0, 1], ![-75, -67, 190], ![-21, -15, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [97, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 106], [0, 1]]
 g := ![![[91, 64], [96, 16], [57], [26, 53], [85], [54, 1]], ![[16, 43], [104, 91], [57], [106, 54], [85], [1, 106]]]
 h' := ![![[54, 106], [104, 8], [11, 4], [46, 48], [19, 38], [5, 37], [0, 1]], ![[0, 1], [1, 99], [13, 103], [70, 59], [38, 69], [77, 70], [54, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [4, 91]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [97, 53, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-794, -1875, -2806]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1094, 979, -2806]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![24, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![24, 1, 0]] 
 ![![107, 0, 0], ![24, 1, 0], ![94, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![24, 1, 0], ![0, 25, 5], ![-45, -29, 24]]]
  hmulB := by decide  
  f := ![![![1201, 50, 0], ![-5350, 0, 0]], ![![264, 11, 0], ![-1176, 0, 0]], ![![1034, 33, -2], ![-4606, 43, 0]]]
  g := ![![![1, 0, 0], ![-24, 107, 0], ![-94, 0, 107]], ![![0, 1, 0], ![-10, 25, 5], ![-15, -29, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![42, 38, 1]] ![![107, 0, 0], ![24, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![2568, 107, 0]], ![![4494, 4066, 107], ![963, 963, 214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![24, 1, 0]]], ![![![42, 38, 1]], ![![9, 9, 2]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [45, 1, 97, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 58, 62], [50, 50, 47], [0, 1]]
 g := ![![[105, 61, 80], [21, 87], [92, 23, 105], [32, 0, 46], [69, 35], [1]], ![[89, 104, 31, 14], [100, 29], [41, 36, 34, 23], [33, 7, 11, 14], [53, 49], [94, 48, 26, 54]], ![[32, 56, 84, 10], [1, 108], [108, 48, 7, 76], [1, 65, 68, 6], [96, 25], [99, 99, 105, 55]]]
 h' := ![![[71, 58, 62], [40, 103, 84], [2, 56, 95], [86, 68, 43], [10, 81, 41], [64, 108, 12], [0, 1]], ![[50, 50, 47], [40, 53, 13], [92, 2, 47], [48, 102, 44], [44, 3, 96], [85, 46, 102], [71, 58, 62]], ![[0, 1], [15, 62, 12], [13, 51, 76], [70, 48, 22], [12, 25, 81], [100, 64, 104], [50, 50, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107, 96], []]
 b := ![[], [98, 100, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [45, 1, 97, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![579778848, 584878522, 401145288]
  a := ![1, 20, 81]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5319072, 5365858, 3680232]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-15, -22, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-15, -22, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![98, 91, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-15, -22, 1], ![-45, -66, -110], ![999, 629, -44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-98, -91, 113]], ![![-1, -1, 1], ![95, 88, -110], ![47, 41, -44]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [40, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 112], [0, 1]]
 g := ![![[93, 105], [95], [106], [13], [73, 99], [9, 1]], ![[21, 8], [95], [106], [13], [60, 14], [18, 112]]]
 h' := ![![[9, 112], [56, 61], [50, 35], [30, 28], [18, 76], [92, 41], [0, 1]], ![[0, 1], [40, 52], [26, 78], [56, 85], [24, 37], [9, 72], [9, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [90, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [40, 104, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-882, -1045, -687]
  a := ![-1, 2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![588, 544, -687]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-3, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-3, 1, 0]] 
 ![![113, 0, 0], ![110, 1, 0], ![44, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-3, 1, 0], ![0, -2, 5], ![-45, -29, -3]]]
  hmulB := by decide  
  f := ![![![121, -40, 0], ![4520, 0, 0]], ![![118, -39, 0], ![4408, 0, 0]], ![![52, -16, -3], ![1944, 68, 0]]]
  g := ![![![1, 0, 0], ![-110, 113, 0], ![-44, 0, 113]], ![![-1, 1, 0], ![0, -2, 5], ![29, -29, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-15, -22, 1]] ![![113, 0, 0], ![-3, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-339, 113, 0]], ![![-1695, -2486, 113], ![0, 0, -113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-3, 1, 0]]], ![![![-15, -22, 1]], ![![0, 0, -1]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![22, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![22, 1, 0]] 
 ![![127, 0, 0], ![22, 1, 0], ![102, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![22, 1, 0], ![0, 23, 5], ![-45, -29, 22]]]
  hmulB := by decide  
  f := ![![![749, 34, 0], ![-4318, 0, 0]], ![![110, 5, 0], ![-634, 0, 0]], ![![622, 19, -2], ![-3586, 51, 0]]]
  g := ![![![1, 0, 0], ![-22, 127, 0], ![-102, 0, 127]], ![![0, 1, 0], ![-8, 23, 5], ![-13, -29, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![29, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![29, 1, 0]] 
 ![![127, 0, 0], ![29, 1, 0], ![80, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![29, 1, 0], ![0, 30, 5], ![-45, -29, 29]]]
  hmulB := by decide  
  f := ![![![1973, 68, 0], ![-8636, 0, 0]], ![![435, 15, 0], ![-1904, 0, 0]], ![![1220, 30, -2], ![-5340, 51, 0]]]
  g := ![![![1, 0, 0], ![-29, 127, 0], ![-80, 0, 127]], ![![0, 1, 0], ![-10, 30, 5], ![-12, -29, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-52, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-52, 1, 0]] 
 ![![127, 0, 0], ![75, 1, 0], ![3, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-52, 1, 0], ![0, -51, 5], ![-45, -29, -52]]]
  hmulB := by decide  
  f := ![![![1353, -26, 0], ![3302, 0, 0]], ![![781, -15, 0], ![1906, 0, 0]], ![![77, 19, -2], ![188, 51, 0]]]
  g := ![![![1, 0, 0], ![-75, 127, 0], ![-3, 0, 127]], ![![-1, 1, 0], ![30, -51, 5], ![18, -29, -52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![22, 1, 0]] ![![127, 0, 0], ![29, 1, 0]]
  ![![127, 0, 0], ![26, -15, 1]] where
 M := ![![![16129, 0, 0], ![3683, 127, 0]], ![![2794, 127, 0], ![638, 52, 5]]]
 hmul := by decide  
 g := ![![![![101, 15, -1], ![127, 0, 0]], ![![3, 16, -1], ![127, 0, 0]]], ![![![-4, 16, -1], ![127, 0, 0]], ![![4, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![26, -15, 1]] ![![127, 0, 0], ![-52, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-6604, 127, 0]], ![![3302, -1905, 127], ![-1397, 762, -127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-52, 1, 0]]], ![![![26, -15, 1]], ![![-11, 6, -1]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![28, -5, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![28, -5, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![28, 126, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![28, -5, 1], ![-45, -6, -25], ![234, 136, -1]]]
  hmulB := by decide  
  f := ![![![-27, 5, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -126, 131]], ![![0, -1, 1], ![5, 24, -25], ![2, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [80, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 130], [0, 1]]
 g := ![![[9, 113], [101, 60], [74], [5], [4], [33], [1]], ![[0, 18], [0, 71], [74], [5], [4], [33], [1]]]
 h' := ![![[66, 130], [42, 47], [88, 86], [84, 104], [22, 108], [92, 2], [51, 66], [0, 1]], ![[0, 1], [0, 84], [0, 45], [5, 27], [76, 23], [93, 129], [84, 65], [66, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [55, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [80, 65, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1936, -3996, -4729]
  a := ![0, 3, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![996, 4518, -4729]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![25, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![25, 1, 0]] 
 ![![131, 0, 0], ![25, 1, 0], ![1, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![25, 1, 0], ![0, 26, 5], ![-45, -29, 25]]]
  hmulB := by decide  
  f := ![![![326, 13, 0], ![-1703, 0, 0]], ![![50, 2, 0], ![-261, 0, 0]], ![![-4, -21, -4], ![21, 105, 0]]]
  g := ![![![1, 0, 0], ![-25, 131, 0], ![-1, 0, 131]], ![![0, 1, 0], ![-5, 26, 5], ![5, -29, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![28, -5, 1]] ![![131, 0, 0], ![25, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![3275, 131, 0]], ![![3668, -655, 131], ![655, -131, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![25, 1, 0]]], ![![![28, -5, 1]], ![![5, -1, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![34, 36, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![34, 36, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![34, 36, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![34, 36, 1], ![-45, 41, 180], ![-1611, -1053, 5]]]
  hmulB := by decide  
  f := ![![![-33, -36, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -36, 137]], ![![0, 0, 1], ![-45, -47, 180], ![-13, -9, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [34, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 136], [0, 1]]
 g := ![![[15, 133], [74], [36], [78, 99], [61], [74], [1]], ![[0, 4], [74], [36], [4, 38], [61], [74], [1]]]
 h' := ![![[38, 136], [72, 63], [81, 38], [88, 131], [81, 28], [10, 91], [103, 38], [0, 1]], ![[0, 1], [0, 74], [18, 99], [134, 6], [49, 109], [43, 46], [40, 99], [38, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [48, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [34, 99, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13264, -22780, -28870]
  a := ![2, -8, -30]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7068, 7420, -28870]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-43, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-43, 1, 0]] 
 ![![137, 0, 0], ![94, 1, 0], ![132, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-43, 1, 0], ![0, -42, 5], ![-45, -29, -43]]]
  hmulB := by decide  
  f := ![![![3140, -73, 0], ![10001, 0, 0]], ![![2194, -51, 0], ![6988, 0, 0]], ![![3048, -54, -2], ![9708, 55, 0]]]
  g := ![![![1, 0, 0], ![-94, 137, 0], ![-132, 0, 137]], ![![-1, 1, 0], ![24, -42, 5], ![61, -29, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![34, 36, 1]] ![![137, 0, 0], ![-43, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-5891, 137, 0]], ![![4658, 4932, 137], ![-1507, -1507, 137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-43, 1, 0]]], ![![![34, 36, 1]], ![![-11, -11, 1]]]]
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


lemma PB213I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB213I2 : PrimesBelowBoundCertificateInterval O 79 137 213 where
  m := 11
  g := ![2, 2, 1, 2, 3, 2, 1, 2, 3, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB213I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
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
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![12769, 113]
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
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
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
  β := ![I83N1, I89N1, I101N1, I103N0, I103N1, I103N2, I107N1, I113N1, I127N0, I127N1, I127N2, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [], [I101N1], [I103N0, I103N1, I103N2], [I107N1], [], [I113N1], [I127N0, I127N1, I127N2], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
