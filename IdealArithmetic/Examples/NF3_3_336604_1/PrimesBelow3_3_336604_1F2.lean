
import IdealArithmetic.Examples.NF3_3_336604_1.RI3_3_336604_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-547, 234, 58]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-547, 234, 58]] 
 ![![83, 0, 0], ![0, 83, 0], ![75, 67, 1]] where
  M :=![![![-547, 234, 58], ![-4408, 1891, 468], ![-15580, 6688, 1657]]]
  hmulB := by decide  
  f := ![![![-41, -2, 2]], ![![-152, 33, -4]], ![![-157, 23, -1]]]
  g := ![![![-59, -44, 58], ![-476, -355, 468], ![-1685, -1257, 1657]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [10, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 82], [0, 1]]
 g := ![![[37, 25], [64, 41], [28], [10], [4, 33], [1]], ![[0, 58], [0, 42], [28], [10], [78, 50], [1]]]
 h' := ![![[45, 82], [24, 5], [5, 46], [6, 51], [43, 33], [73, 45], [0, 1]], ![[0, 1], [0, 78], [0, 37], [60, 32], [34, 50], [23, 38], [45, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [41, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [10, 38, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-560, 42, 236]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-220, -190, 236]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -2, 2]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-41, -2, 2]] 
 ![![83, 0, 0], ![32, 1, 0], ![53, 0, 1]] where
  M :=![![![-41, -2, 2], ![-152, 33, -4], ![228, -152, 35]]]
  hmulB := by decide  
  f := ![![![-547, 234, 58]], ![![-264, 113, 28]], ![![-537, 230, 57]]]
  g := ![![![-1, -2, 2], ![-12, 33, -4], ![39, -152, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-547, 234, 58]] ![![-41, -2, 2]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 12, -4]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-21, 12, -4]] 
 ![![89, 0, 0], ![0, 89, 0], ![72, 86, 1]] where
  M :=![![![-21, 12, -4], ![304, -161, 24], ![-1064, 608, -173]]]
  hmulB := by decide  
  f := ![![![-149, 4, 4]], ![![-304, 7, 8]], ![![-416, 10, 11]]]
  g := ![![![3, 4, -4], ![-16, -25, 24], ![128, 174, -173]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [34, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 88], [0, 1]]
 g := ![![[85, 55], [40], [17], [17, 57], [57, 73], [1]], ![[0, 34], [40], [17], [26, 32], [17, 16], [1]]]
 h' := ![![[47, 88], [59, 12], [23, 60], [45, 62], [20, 18], [55, 47], [0, 1]], ![[0, 1], [0, 77], [84, 29], [22, 27], [65, 71], [39, 42], [47, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [60, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [34, 42, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7, -263, 770]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-623, -747, 770]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, -4, -4]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![149, -4, -4]] 
 ![![89, 0, 0], ![6, 1, 0], ![68, 0, 1]] where
  M :=![![![149, -4, -4], ![304, -7, -8], ![152, 0, -3]]]
  hmulB := by decide  
  f := ![![![21, -12, 4]], ![![-2, 1, 0]], ![![28, -16, 5]]]
  g := ![![![5, -4, -4], ![10, -7, -8], ![4, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-21, 12, -4]] ![![149, -4, -4]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![347, -188, 41]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![347, -188, 41]] 
 ![![97, 0, 0], ![0, 97, 0], ![96, 38, 1]] where
  M :=![![![347, -188, 41], ![-3116, 1717, -376], ![15846, -8702, 1905]]]
  hmulB := by decide  
  f := ![![![-11, 14, 3]], ![![-228, 117, 28]], ![![-110, 64, 15]]]
  g := ![![![-37, -18, 41], ![340, 165, -376], ![-1722, -836, 1905]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [56, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 96], [0, 1]]
 g := ![![[74, 65], [93], [66], [49], [36], [27, 1]], ![[83, 32], [93], [66], [49], [36], [54, 96]]]
 h' := ![![[27, 96], [34, 68], [2, 44], [77, 58], [69, 7], [40, 91], [0, 1]], ![[0, 1], [27, 29], [26, 53], [91, 39], [64, 90], [72, 6], [27, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [45, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [56, 70, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-290, -38, 96]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-98, -38, 96]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 14, 3]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-11, 14, 3]] 
 ![![97, 0, 0], ![21, 1, 0], ![60, 0, 1]] where
  M :=![![![-11, 14, 3], ![-228, 117, 28], ![-950, 418, 103]]]
  hmulB := by decide  
  f := ![![![347, -188, 41]], ![![43, -23, 5]], ![![378, -206, 45]]]
  g := ![![![-5, 14, 3], ![-45, 117, 28], ![-164, 418, 103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![347, -188, 41]] ![![-11, 14, 3]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-99, 30, -5]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-99, 30, -5]] 
 ![![101, 0, 0], ![0, 101, 0], ![40, 95, 1]] where
  M :=![![![-99, 30, -5], ![380, -259, 60], ![-2470, 1330, -289]]]
  hmulB := by decide  
  f := ![![![-49, 20, 5]], ![![-380, 161, 40]], ![![-390, 165, 41]]]
  g := ![![![1, 5, -5], ![-20, -59, 60], ![90, 285, -289]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [22, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 100], [0, 1]]
 g := ![![[19, 23], [88], [87, 88], [5], [77], [87, 1]], ![[0, 78], [88], [67, 13], [5], [77], [73, 100]]]
 h' := ![![[87, 100], [8, 15], [5, 54], [73, 54], [48, 56], [5, 73], [0, 1]], ![[0, 1], [0, 86], [57, 47], [24, 47], [72, 45], [94, 28], [87, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [99, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [22, 14, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-533, -218, 878]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-353, -828, 878]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49, -20, -5]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![49, -20, -5]] 
 ![![101, 0, 0], ![12, 1, 0], ![23, 0, 1]] where
  M :=![![![49, -20, -5], ![380, -161, -40], ![1330, -570, -141]]]
  hmulB := by decide  
  f := ![![![99, -30, 5]], ![![8, -1, 0]], ![![47, -20, 4]]]
  g := ![![![4, -20, -5], ![32, -161, -40], ![113, -570, -141]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-99, 30, -5]] ![![49, -20, -5]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21073, -9048, -2240]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![21073, -9048, -2240]] 
 ![![103, 0, 0], ![57, 1, 0], ![98, 0, 1]] where
  M :=![![![21073, -9048, -2240], ![170240, -73095, -18096], ![602528, -258704, -64047]]]
  hmulB := by decide  
  f := ![![![-7881, 296, 192]], ![![-4503, 161, 112]], ![![-7646, 320, 177]]]
  g := ![![![7343, -9048, -2240], ![59321, -73095, -18096], ![209954, -258704, -64047]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 4, 1]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-11, 4, 1]] 
 ![![103, 0, 0], ![91, 1, 0], ![37, 0, 1]] where
  M :=![![![-11, 4, 1], ![-76, 31, 8], ![-266, 114, 27]]]
  hmulB := by decide  
  f := ![![![-75, 6, 1]], ![![-67, 5, 1]], ![![-31, 4, 0]]]
  g := ![![![-4, 4, 1], ![-31, 31, 8], ![-113, 114, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![21073, -9048, -2240]] ![![21073, -9048, -2240]]
  ![![-2445922911, 1050192016, 259994368]] where
 M := ![![![-2445922911, 1050192016, 259994368]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-2445922911, 1050192016, 259994368]] ![![-11, 4, 1]]
  ![![103, 0, 0]] where
 M := ![![![-122067943083, 52411618804, 12975461153]]]
 hmul := by decide  
 g := ![![![![-1185125661, 508850668, 125975351]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N0
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [53, 36, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 61, 42], [100, 45, 65], [0, 1]]
 g := ![![[89, 6, 19], [23, 34, 13], [], [21, 106, 36], [52, 42], [1]], ![[8, 97, 32, 1], [85, 102, 7, 27], [69, 85], [79, 39, 33, 19], [61, 11], [72, 14, 38, 44]], ![[105, 16, 67, 71], [72, 10, 9, 84], [17, 85], [63, 49, 76, 51], [83, 1], [13, 3, 20, 63]]]
 h' := ![![[98, 61, 42], [65, 89, 33], [30, 35, 86], [64, 73], [53, 39, 6], [54, 71, 91], [0, 1]], ![[100, 45, 65], [102, 95, 87], [28, 14, 97], [49, 66, 70], [10, 96, 89], [56, 40, 15], [98, 61, 42]], ![[0, 1], [75, 30, 94], [102, 58, 31], [88, 75, 37], [41, 79, 12], [38, 103, 1], [100, 45, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 49], []]
 b := ![[], [85, 101, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [53, 36, 16, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![31137, 2568, -33170]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![291, 24, -310]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [14, 25, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 97, 59], [108, 11, 50], [0, 1]]
 g := ![![[40, 10, 16], [44, 15], [1, 51, 83], [30, 72, 36], [83, 38], [1]], ![[7, 22, 4, 67], [52, 83], [50, 96, 60, 33], [73, 77, 104, 41], [105, 38], [82, 52, 102, 23]], ![[101, 80, 9, 30], [18, 71], [79, 83, 108, 103], [62, 23, 43, 6], [49, 43], [57, 95, 28, 86]]]
 h' := ![![[94, 97, 59], [16, 6, 4], [95, 62, 48], [16, 102, 65], [15, 55, 103], [95, 84, 93], [0, 1]], ![[108, 11, 50], [57, 52, 71], [83, 90, 44], [97, 28, 84], [29, 26, 18], [55, 22, 93], [94, 97, 59]], ![[0, 1], [49, 51, 34], [65, 66, 17], [30, 88, 69], [65, 28, 97], [73, 3, 32], [108, 11, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106, 72], []]
 b := ![[], [48, 86, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [14, 25, 16, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-38408330, 11417750, 13979904]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-352370, 104750, 128256]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1369, -38, -37]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![1369, -38, -37]] 
 ![![113, 0, 0], ![0, 113, 0], ![76, 56, 1]] where
  M :=![![![1369, -38, -37], ![2812, -75, -76], ![1482, -38, -37]]]
  hmulB := by decide  
  f := ![![![-1, 0, 1]], ![![-76, 37, 0]], ![![-38, 18, 1]]]
  g := ![![![37, 18, -37], ![76, 37, -76], ![38, 18, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [53, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 112], [0, 1]]
 g := ![![[22, 32], [32], [81], [85], [], [77, 1]], ![[0, 81], [32], [81], [85], [], [41, 112]]]
 h' := ![![[77, 112], [112, 91], [0, 91], [15, 104], [0, 56], [100], [0, 1]], ![[0, 1], [0, 22], [1, 22], [0, 9], [18, 57], [100], [77, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [45, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [53, 36, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-248, 186, 80]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56, -38, 80]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 0, 1]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-1, 0, 1]] 
 ![![113, 0, 0], ![1, 1, 0], ![112, 0, 1]] where
  M :=![![![-1, 0, 1], ![-76, 37, 0], ![38, -38, 37]]]
  hmulB := by decide  
  f := ![![![1369, -38, -37]], ![![37, -1, -1]], ![![1370, -38, -37]]]
  g := ![![![-1, 0, 1], ![-1, 37, 0], ![-36, -38, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![1369, -38, -37]] ![![-1, 0, 1]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![309, -170, 37]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![309, -170, 37]] 
 ![![127, 0, 0], ![0, 127, 0], ![77, 16, 1]] where
  M :=![![![309, -170, 37], ![-2812, 1545, -340], ![14326, -7866, 1715]]]
  hmulB := by decide  
  f := ![![![-195, 4, 5]], ![![-380, -1, 8]], ![![-167, 2, 4]]]
  g := ![![![-20, -6, 37], ![184, 55, -340], ![-927, -278, 1715]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [56, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 126], [0, 1]]
 g := ![![[114, 99], [20, 47], [22, 100], [77, 49], [85, 71], [93, 1]], ![[50, 28], [73, 80], [51, 27], [62, 78], [84, 56], [59, 126]]]
 h' := ![![[93, 126], [23, 37], [38, 38], [6, 10], [66, 120], [126, 84], [0, 1]], ![[0, 1], [35, 90], [16, 89], [47, 117], [50, 7], [64, 43], [93, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [76, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [56, 34, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1274, 301, 1138]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-700, -141, 1138]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-195, 4, 5]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-195, 4, 5]] 
 ![![127, 0, 0], ![95, 1, 0], ![12, 0, 1]] where
  M :=![![![-195, 4, 5], ![-380, -1, 8], ![-114, -38, -5]]]
  hmulB := by decide  
  f := ![![![309, -170, 37]], ![![209, -115, 25]], ![![142, -78, 17]]]
  g := ![![![-5, 4, 5], ![-3, -1, 8], ![28, -38, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![309, -170, 37]] ![![-195, 4, 5]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB129I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 128 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 128 (by omega)

def PB129I2 : PrimesBelowBoundCertificateInterval O 79 128 129 where
  m := 9
  g := ![2, 2, 2, 2, 3, 1, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127]
  hP := PB129I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
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
    · exact ![1295029]
    · exact ![12769, 113]
    · exact ![16129, 127]
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
      exact NI103N0
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
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
  β := ![I83N1, I89N1, I97N1, I101N1, I103N0, I103N1, I113N1, I127N1]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N1], [I103N0, I103N0, I103N1], [], [], [I113N1], [I127N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
