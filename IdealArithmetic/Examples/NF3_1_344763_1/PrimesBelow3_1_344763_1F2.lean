
import IdealArithmetic.Examples.NF3_1_344763_1.RI3_1_344763_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![29, -19, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![29, -19, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![29, 64, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![29, -19, 1], ![113, 29, -19], ![-2147, 113, 29]]]
  hmulB := by decide  
  f := ![![![-28, 19, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -64, 83]], ![![0, -1, 1], ![8, 15, -19], ![-36, -21, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [10, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 82], [0, 1]]
 g := ![![[82, 25], [78, 70], [31], [33], [53, 17], [1]], ![[0, 58], [31, 13], [31], [33], [57, 66], [1]]]
 h' := ![![[10, 82], [50, 78], [9, 30], [30, 23], [51, 45], [73, 10], [0, 1]], ![[0, 1], [0, 5], [60, 53], [11, 60], [3, 38], [7, 73], [10, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [14, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [10, 73, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![236, 40, -72]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![28, 56, -72]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![19, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![19, 1, 0]] 
 ![![83, 0, 0], ![19, 1, 0], ![54, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![19, 1, 0], ![0, 19, 1], ![113, 0, 19]]]
  hmulB := by decide  
  f := ![![![514, 27, 0], ![-2241, 0, 0]], ![![114, 6, 0], ![-497, 0, 0]], ![![328, 17, 0], ![-1430, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 83, 0], ![-54, 0, 83]], ![![0, 1, 0], ![-5, 19, 1], ![-11, 0, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![29, -19, 1]] ![![83, 0, 0], ![19, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![1577, 83, 0]], ![![2407, -1577, 83], ![664, -332, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![19, 1, 0]]], ![![![29, -19, 1]], ![![8, -4, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-18, -31, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-18, -31, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![71, 58, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-18, -31, 1], ![113, -18, -31], ![-3503, 113, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -58, 89]], ![![-1, -1, 1], ![26, 20, -31], ![-25, 13, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [60, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 88], [0, 1]]
 g := ![![[15, 18], [21], [34], [85, 8], [22, 11], [1]], ![[13, 71], [21], [34], [5, 81], [1, 78], [1]]]
 h' := ![![[79, 88], [28, 75], [24, 56], [62, 52], [15, 50], [29, 79], [0, 1]], ![[0, 1], [79, 14], [87, 33], [76, 37], [49, 39], [40, 10], [79, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [70, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [60, 10, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1305, 1001, 28]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37, -7, 28]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![31, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![31, 1, 0]] 
 ![![89, 0, 0], ![31, 1, 0], ![18, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![31, 1, 0], ![0, 31, 1], ![113, 0, 31]]]
  hmulB := by decide  
  f := ![![![590, 19, 0], ![-1691, 0, 0]], ![![186, 6, 0], ![-533, 0, 0]], ![![104, 3, 0], ![-298, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 89, 0], ![-18, 0, 89]], ![![0, 1, 0], ![-11, 31, 1], ![-5, 0, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-18, -31, 1]] ![![89, 0, 0], ![31, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![2759, 89, 0]], ![![-1602, -2759, 89], ![-445, -979, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![31, 1, 0]]], ![![![-18, -31, 1]], ![![-5, -11, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [64, 17, 95, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 52, 27], [57, 44, 70], [0, 1]]
 g := ![![[63, 81, 86], [46, 31], [53, 12], [47, 66], [37, 4], [1]], ![[93, 34, 29, 65], [56, 2], [50, 65], [21, 16], [72, 95], [77, 80, 24, 89]], ![[58, 38, 31, 72], [12, 1], [69, 73], [73, 6], [24, 70], [75, 48, 20, 8]]]
 h' := ![![[42, 52, 27], [14, 69, 38], [57, 7, 82], [32, 8, 20], [79, 30, 39], [33, 80, 2], [0, 1]], ![[57, 44, 70], [21, 85, 43], [4, 85, 14], [87, 12, 29], [49, 35, 4], [96, 65, 17], [42, 52, 27]], ![[0, 1], [72, 40, 16], [89, 5, 1], [72, 77, 48], [66, 32, 54], [70, 49, 78], [57, 44, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90, 70], []]
 b := ![[], [13, 79, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [64, 17, 95, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![135218, -11155, 97]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1394, -115, 1]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10308, -2132, -441]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-10308, -2132, -441]] 
 ![![101, 0, 0], ![0, 101, 0], ![22, 74, 1]] where
  M :=![![![-10308, -2132, -441], ![-49833, -10308, -2132], ![-240916, -49833, -10308]]]
  hmulB := by decide  
  f := ![![![-108, 3, 4]], ![![452, -108, 3]], ![![311, -74, 2]]]
  g := ![![![-6, 302, -441], ![-29, 1460, -2132], ![-140, 7059, -10308]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [64, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 100], [0, 1]]
 g := ![![[79, 30], [77], [64, 68], [78], [77], [95, 1]], ![[0, 71], [77], [60, 33], [78], [77], [89, 100]]]
 h' := ![![[95, 100], [26, 38], [45, 28], [44, 88], [17, 52], [81, 73], [0, 1]], ![[0, 1], [0, 63], [79, 73], [21, 13], [8, 49], [47, 28], [95, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [34, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [64, 6, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-607, 1025, -23]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, 27, -23]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-108, 3, 4]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-108, 3, 4]] 
 ![![101, 0, 0], ![27, 1, 0], ![79, 0, 1]] where
  M :=![![![-108, 3, 4], ![452, -108, 3], ![339, 452, -108]]]
  hmulB := by decide  
  f := ![![![-10308, -2132, -441]], ![![-3249, -672, -139]], ![![-10448, -2161, -447]]]
  g := ![![![-5, 3, 4], ![31, -108, 3], ![-33, 452, -108]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-10308, -2132, -441]] ![![-108, 3, 4]]
  ![![101, 0, 0]] where
 M := ![![![101, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![33, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![33, 1, 0]] 
 ![![103, 0, 0], ![33, 1, 0], ![44, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![33, 1, 0], ![0, 33, 1], ![113, 0, 33]]]
  hmulB := by decide  
  f := ![![![694, 21, 0], ![-2163, 0, 0]], ![![198, 6, 0], ![-617, 0, 0]], ![![242, 7, 0], ![-754, 1, 0]]]
  g := ![![![1, 0, 0], ![-33, 103, 0], ![-44, 0, 103]], ![![0, 1, 0], ![-11, 33, 1], ![-13, 0, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-27, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-27, 1, 0]] 
 ![![103, 0, 0], ![76, 1, 0], ![95, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-27, 1, 0], ![0, -27, 1], ![113, 0, -27]]]
  hmulB := by decide  
  f := ![![![1513, -56, 0], ![5768, 0, 0]], ![![1108, -41, 0], ![4224, 0, 0]], ![![1385, -51, 0], ![5280, 1, 0]]]
  g := ![![![1, 0, 0], ![-76, 103, 0], ![-95, 0, 103]], ![![-1, 1, 0], ![19, -27, 1], ![26, 0, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![-6, 1, 0]] 
 ![![103, 0, 0], ![97, 1, 0], ![67, 0, 1]] where
  M :=![![![-6, 1, 0], ![0, -6, 1], ![113, 0, -6]]]
  hmulB := by decide  
  f := ![![![-36, -6, -1]], ![![-35, -6, -1]], ![![-30, -5, -1]]]
  g := ![![![-1, 1, 0], ![5, -6, 1], ![5, 0, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![33, 1, 0]] ![![103, 0, 0], ![-27, 1, 0]]
  ![![36, 6, 1]] where
 M := ![![![10609, 0, 0], ![-2781, 103, 0]], ![![3399, 103, 0], ![-891, 6, 1]]]
 hmul := by decide  
 g := ![![![![618, -103, 0]], ![![-162, 33, -1]]], ![![![198, -27, -1]], ![![-53, 9, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![36, 6, 1]] ![![-6, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![-103, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![30, 43, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![30, 43, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![30, 43, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![30, 43, 1], ![113, 30, 43], ![4859, 113, 30]]]
  hmulB := by decide  
  f := ![![![-29, -43, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -43, 107]], ![![0, 0, 1], ![-11, -17, 43], ![37, -11, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [68, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 106], [0, 1]]
 g := ![![[54, 35], [38, 11], [3], [89, 81], [3], [73, 1]], ![[41, 72], [92, 96], [3], [10, 26], [3], [39, 106]]]
 h' := ![![[73, 106], [91, 28], [79, 92], [47, 18], [62, 98], [65, 18], [0, 1]], ![[0, 1], [102, 79], [54, 15], [77, 89], [47, 9], [95, 89], [73, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [37, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [68, 34, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![294, 79, -33]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12, 14, -33]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-43, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-43, 1, 0]] 
 ![![107, 0, 0], ![64, 1, 0], ![77, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-43, 1, 0], ![0, -43, 1], ![113, 0, -43]]]
  hmulB := by decide  
  f := ![![![388, -9, 0], ![963, 0, 0]], ![![216, -5, 0], ![536, 0, 0]], ![![276, -6, 0], ![685, 1, 0]]]
  g := ![![![1, 0, 0], ![-64, 107, 0], ![-77, 0, 107]], ![![-1, 1, 0], ![25, -43, 1], ![32, 0, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![30, 43, 1]] ![![107, 0, 0], ![-43, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-4601, 107, 0]], ![![3210, 4601, 107], ![-1177, -1819, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-43, 1, 0]]], ![![![30, 43, 1]], ![![-11, -17, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![15, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![15, 1, 0]] 
 ![![109, 0, 0], ![15, 1, 0], ![102, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![15, 1, 0], ![0, 15, 1], ![113, 0, 15]]]
  hmulB := by decide  
  f := ![![![961, 64, 0], ![-6976, 0, 0]], ![![105, 7, 0], ![-762, 0, 0]], ![![888, 59, 0], ![-6446, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 109, 0], ![-102, 0, 109]], ![![0, 1, 0], ![-3, 15, 1], ![-13, 0, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![21, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![21, 1, 0]] 
 ![![109, 0, 0], ![21, 1, 0], ![104, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![21, 1, 0], ![0, 21, 1], ![113, 0, 21]]]
  hmulB := by decide  
  f := ![![![463, 22, 0], ![-2398, 0, 0]], ![![63, 3, 0], ![-326, 0, 0]], ![![446, 21, 0], ![-2310, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 109, 0], ![-104, 0, 109]], ![![0, 1, 0], ![-5, 21, 1], ![-19, 0, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-36, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-36, 1, 0]] 
 ![![109, 0, 0], ![73, 1, 0], ![12, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-36, 1, 0], ![0, -36, 1], ![113, 0, -36]]]
  hmulB := by decide  
  f := ![![![3889, -108, 0], ![11772, 0, 0]], ![![2629, -73, 0], ![7958, 0, 0]], ![![444, -12, 0], ![1344, 1, 0]]]
  g := ![![![1, 0, 0], ![-73, 109, 0], ![-12, 0, 109]], ![![-1, 1, 0], ![24, -36, 1], ![5, 0, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![15, 1, 0]] ![![109, 0, 0], ![21, 1, 0]]
  ![![109, 0, 0], ![-12, 36, 1]] where
 M := ![![![11881, 0, 0], ![2289, 109, 0]], ![![1635, 109, 0], ![315, 36, 1]]]
 hmul := by decide  
 g := ![![![![109, 0, 0], ![0, 0, 0]], ![![21, 1, 0], ![0, 0, 0]]], ![![![15, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-12, 36, 1]] ![![109, 0, 0], ![-36, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-3924, 109, 0]], ![![-1308, 3924, 109], ![545, -1308, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-36, 1, 0]]], ![![![-12, 36, 1]], ![![5, -12, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![0, 1, 0]] 
 ![![113, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![0, 1, 0], ![0, 0, 1], ![113, 0, 0]]]
  hmulB := by decide  
  f := ![![![0, 0, 1]], ![![1, 0, 0]], ![![0, 1, 0]]]
  g := ![![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![0, 1, 0]] ![![0, 1, 0]]
  ![![0, 0, 1]] where
 M := ![![![0, 0, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI113N1 : IdealMulLeCertificate' Table 
  ![![0, 0, 1]] ![![0, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N0, I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N0
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [35, 39, 124, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [102, 70, 24], [28, 56, 103], [0, 1]]
 g := ![![[37, 77, 44], [94, 121, 73], [98, 97, 79], [66, 58, 37], [85, 47, 9], [1]], ![[125, 48, 78, 57], [105, 71, 103, 91], [16, 12, 81, 20], [73, 0, 33, 77], [54, 21, 28, 102], [114, 77, 126, 108]], ![[105, 79, 59, 52], [8, 69, 57, 113], [13, 79, 27, 103], [50, 50, 70, 84], [106, 116, 84, 38], [49, 58, 51, 19]]]
 h' := ![![[102, 70, 24], [12, 101, 67], [126, 90, 94], [103, 90, 98], [73, 75, 75], [92, 88, 3], [0, 1]], ![[28, 56, 103], [28, 3, 80], [80, 70, 58], [40, 67, 28], [70, 82, 31], [70, 30, 121], [102, 70, 24]], ![[0, 1], [121, 23, 107], [52, 94, 102], [24, 97, 1], [79, 97, 21], [44, 9, 3], [28, 56, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 17], []]
 b := ![[], [34, 74, 121], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [35, 39, 124, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1333373, 142240, 52578]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10499, 1120, 414]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-24, -32, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-24, -32, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![107, 99, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-24, -32, 1], ![113, -24, -32], ![-3616, 113, -24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-107, -99, 131]], ![![-1, -1, 1], ![27, 24, -32], ![-8, 19, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [104, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 130], [0, 1]]
 g := ![![[22, 36], [40, 129], [129], [99], [5], [53], [1]], ![[53, 95], [31, 2], [129], [99], [5], [53], [1]]]
 h' := ![![[70, 130], [32, 6], [81, 103], [2, 28], [39, 19], [64, 23], [27, 70], [0, 1]], ![[0, 1], [59, 125], [86, 28], [128, 103], [59, 112], [102, 108], [80, 61], [70, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [46, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [104, 61, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-634, 290, -50]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![36, 40, -50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![32, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![32, 1, 0]] 
 ![![131, 0, 0], ![32, 1, 0], ![24, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![32, 1, 0], ![0, 32, 1], ![113, 0, 32]]]
  hmulB := by decide  
  f := ![![![1857, 58, 0], ![-7598, 0, 0]], ![![416, 13, 0], ![-1702, 0, 0]], ![![328, 10, 0], ![-1342, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 131, 0], ![-24, 0, 131]], ![![0, 1, 0], ![-8, 32, 1], ![-5, 0, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-24, -32, 1]] ![![131, 0, 0], ![32, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![4192, 131, 0]], ![![-3144, -4192, 131], ![-655, -1048, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![32, 1, 0]]], ![![![-24, -32, 1]], ![![-5, -8, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-61, -58, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-61, -58, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![76, 79, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-61, -58, 1], ![113, -61, -58], ![-6554, 113, -61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-76, -79, 137]], ![![-1, -1, 1], ![33, 33, -58], ![-14, 36, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [75, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 136], [0, 1]]
 g := ![![[25, 69], [107], [119], [45, 68], [63], [68], [1]], ![[115, 68], [107], [119], [92, 69], [63], [68], [1]]]
 h' := ![![[43, 136], [117, 53], [14, 92], [50, 121], [51, 94], [114, 36], [62, 43], [0, 1]], ![[0, 1], [67, 84], [134, 45], [47, 16], [120, 43], [18, 101], [130, 94], [43, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [63, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [75, 94, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![527, 546, 189]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-101, -105, 189]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![58, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![58, 1, 0]] 
 ![![137, 0, 0], ![58, 1, 0], ![61, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![58, 1, 0], ![0, 58, 1], ![113, 0, 58]]]
  hmulB := by decide  
  f := ![![![1277, 22, 0], ![-3014, 0, 0]], ![![522, 9, 0], ![-1232, 0, 0]], ![![489, 8, 0], ![-1154, 1, 0]]]
  g := ![![![1, 0, 0], ![-58, 137, 0], ![-61, 0, 137]], ![![0, 1, 0], ![-25, 58, 1], ![-25, 0, 58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-61, -58, 1]] ![![137, 0, 0], ![58, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![7946, 137, 0]], ![![-8357, -7946, 137], ![-3425, -3425, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![58, 1, 0]]], ![![![-61, -58, 1]], ![![-25, -25, 0]]]]
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


lemma PB167I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB167I2 : PrimesBelowBoundCertificateInterval O 79 137 167 where
  m := 11
  g := ![2, 2, 1, 2, 3, 2, 3, 3, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB167I2_primes
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
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N0, I113N0]
    · exact ![I127N0]
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
    · exact ![109, 109, 109]
    · exact ![113, 113, 113]
    · exact ![2048383]
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
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N0
      exact NI113N0
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
      exact NI137N1
  β := ![I83N1, I89N1, I101N1, I103N0, I103N1, I103N2, I107N1, I109N0, I109N1, I109N2, I113N0, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [], [I101N1], [I103N0, I103N1, I103N2], [I107N1], [I109N0, I109N1, I109N2], [I113N0, I113N0, I113N0], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
