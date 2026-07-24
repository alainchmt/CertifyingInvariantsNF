
import IdealArithmetic.Examples.NF3_1_817516_2.RI3_1_817516_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-21, -29, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-21, -29, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![62, 54, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-21, -29, 1], ![-260, -114, -205], ![5138, 151, 32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-62, -54, 83]], ![![-1, -1, 1], ![150, 132, -205], ![38, -19, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [82, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 82], [0, 1]]
 g := ![![[52, 31], [70, 44], [23], [21], [27, 48], [1]], ![[4, 52], [34, 39], [23], [21], [33, 35], [1]]]
 h' := ![![[52, 82], [70, 60], [32, 25], [3, 40], [27, 42], [1, 52], [0, 1]], ![[0, 1], [36, 23], [4, 58], [8, 43], [53, 41], [49, 31], [52, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [1, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [82, 31, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3713, -1515, -420]
  a := ![-3, -4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![269, 255, -420]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![39, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![39, 1, 0]] 
 ![![83, 0, 0], ![39, 1, 0], ![51, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![39, 1, 0], ![3, 42, 7], ![-173, -6, 37]]]
  hmulB := by decide  
  f := ![![![3703, 69268, 11550], ![2656, -136950, 0]], ![![1740, 32535, 5425], ![1246, -64325, 0]], ![![2265, 42562, 7097], ![1654, -84150, 0]]]
  g := ![![![1, 0, 0], ![-39, 83, 0], ![-51, 0, 83]], ![![0, 1, 0], ![-24, 42, 7], ![-22, -6, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-21, -29, 1]] ![![83, 0, 0], ![39, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![3237, 83, 0]], ![![-1743, -2407, 83], ![-1079, -1245, -166]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![39, 1, 0]]], ![![![-21, -29, 1]], ![![-13, -15, -2]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-16, 25, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-16, 25, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![73, 25, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-16, 25, 1], ![-98, 53, 173], ![-4204, -173, -71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-73, -25, 89]], ![![-1, 0, 1], ![-143, -48, 173], ![11, 18, -71]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [60, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 88], [0, 1]]
 g := ![![[81, 17], [85], [36], [29, 32], [49, 68], [1]], ![[53, 72], [85], [36], [81, 57], [26, 21], [1]]]
 h' := ![![[35, 88], [26, 62], [63, 68], [40, 83], [86, 78], [29, 35], [0, 1]], ![[0, 1], [60, 27], [40, 21], [8, 6], [57, 11], [8, 54], [35, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [80, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [60, 54, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4901, -9143, -679]
  a := ![8, 6, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![612, 88, -679]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![5, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![5, 1, 0]] 
 ![![89, 0, 0], ![5, 1, 0], ![71, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![5, 1, 0], ![3, 8, 7], ![-173, -6, 3]]]
  hmulB := by decide  
  f := ![![![-3224, -8637, -7560], ![-267, 96120, 0]], ![![-180, -480, -420], ![1, 5340, 0]], ![![-2576, -6891, -6031], ![-141, 76680, 0]]]
  g := ![![![1, 0, 0], ![-5, 89, 0], ![-71, 0, 89]], ![![0, 1, 0], ![-6, 8, 7], ![-4, -6, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-16, 25, 1]] ![![89, 0, 0], ![5, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![445, 89, 0]], ![![-1424, 2225, 89], ![-178, 178, 178]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![5, 1, 0]]], ![![![-16, 25, 1]], ![![-2, 2, 2]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![7, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![7, 1, 0]] 
 ![![97, 0, 0], ![7, 1, 0], ![32, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![7, 1, 0], ![3, 10, 7], ![-173, -6, 5]]]
  hmulB := by decide  
  f := ![![![-3919, -13156, -9212], ![-388, 127652, 0]], ![![-282, -940, -658], ![1, 9118, 0]], ![![-1299, -4341, -3039], ![-43, 42112, 0]]]
  g := ![![![1, 0, 0], ![-7, 97, 0], ![-32, 0, 97]], ![![0, 1, 0], ![-3, 10, 7], ![-3, -6, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-15, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-15, 1, 0]] 
 ![![97, 0, 0], ![82, 1, 0], ![44, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-15, 1, 0], ![3, -12, 7], ![-173, -6, -17]]]
  hmulB := by decide  
  f := ![![![4417, -18136, 10584], ![-776, -146664, 0]], ![![3730, -15329, 8946], ![-678, -123966, 0]], ![![2009, -8227, 4801], ![-317, -66528, 0]]]
  g := ![![![1, 0, 0], ![-82, 97, 0], ![-44, 0, 97]], ![![-1, 1, 0], ![7, -12, 7], ![11, -6, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![7, 1, 0]] ![![97, 0, 0], ![7, 1, 0]]
  ![![97, 0, 0], ![49, 44, 1]] where
 M := ![![![9409, 0, 0], ![679, 97, 0]], ![![679, 97, 0], ![52, 17, 7]]]
 hmul := by decide  
 g := ![![![![48, -44, -1], ![97, 0, 0]], ![![-42, -43, -1], ![97, 0, 0]]], ![![![-42, -43, -1], ![97, 0, 0]], ![![-3, -3, 0], ![7, 0, 0]]]]
 hle2 := by decide  
def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![49, 44, 1]] ![![97, 0, 0], ![-15, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-1455, 97, 0]], ![![4753, 4268, 97], ![-776, -485, 291]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-15, 1, 0]]], ![![![49, 44, 1]], ![![-8, -5, 3]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [13, 8, 95, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 23, 99], [3, 77, 2], [0, 1]]
 g := ![![[93, 73, 1], [98, 84], [52, 59, 54], [47, 56], [19, 36], [1]], ![[55, 14, 24, 2], [42, 87], [42, 11, 53, 51], [13, 56], [70, 22], [90, 11, 26, 93]], ![[51, 71, 34, 40], [28, 82], [47, 42, 68, 74], [19, 22], [16, 37], [66, 69, 63, 8]]]
 h' := ![![[3, 23, 99], [91, 84, 1], [31, 87, 65], [19, 43, 85], [23, 93, 37], [88, 93, 6], [0, 1]], ![[3, 77, 2], [24, 37, 10], [60, 26, 84], [0, 100, 96], [13, 98, 37], [69, 61, 74], [3, 23, 99]], ![[0, 1], [76, 81, 90], [6, 89, 53], [77, 59, 21], [18, 11, 27], [78, 48, 21], [3, 77, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 15], []]
 b := ![[], [47, 36, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [13, 8, 95, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11315022627, -539631183, 147629781]
  a := ![-67, -66, -135]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-112029927, -5342883, 1461681]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [99, 33, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 72, 3], [96, 30, 100], [0, 1]]
 g := ![![[72, 72, 56], [49, 13, 63], [42, 95, 63], [26, 79], [84, 63], [1]], ![[51, 28, 20, 95], [1, 56, 85, 3], [23, 51, 52, 57], [17, 63], [81, 41], [79, 89, 55, 27]], ![[4, 83, 15, 29], [91, 99, 20, 79], [55, 36, 58, 8], [13, 60], [81, 55], [1, 48, 21, 76]]]
 h' := ![![[82, 72, 3], [93, 85, 46], [65, 40, 75], [99, 24, 28], [43, 100, 39], [4, 70, 75], [0, 1]], ![[96, 30, 100], [8, 16, 90], [89, 102, 1], [70, 77, 88], [65, 41, 28], [16, 99, 91], [82, 72, 3]], ![[0, 1], [29, 2, 70], [35, 64, 27], [93, 2, 90], [91, 65, 36], [73, 37, 40], [96, 30, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 91], []]
 b := ![[], [31, 3, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [99, 33, 28, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-29688205, -1884179, -72203]
  a := ![-8, -7, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-288235, -18293, -701]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-39, -46, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-39, -46, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![68, 61, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-39, -46, 1], ![-311, -183, -324], ![8079, 253, 48]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -61, 107]], ![![-1, -1, 1], ![203, 183, -324], ![45, -25, 48]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [3, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 106], [0, 1]]
 g := ![![[48, 36], [33, 105], [76], [97, 1], [90], [70, 1]], ![[0, 71], [0, 2], [76], [60, 106], [90], [33, 106]]]
 h' := ![![[70, 106], [8, 6], [30, 76], [30, 41], [67, 1], [4, 82], [0, 1]], ![[0, 1], [0, 101], [0, 31], [11, 66], [30, 106], [73, 25], [70, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [42, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [3, 37, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3810, -1539, -462]
  a := ![-3, -4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![258, 249, -462]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![3, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![3, 1, 0]] 
 ![![107, 0, 0], ![3, 1, 0], ![59, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![3, 1, 0], ![3, 6, 7], ![-173, -6, 1]]]
  hmulB := by decide  
  f := ![![![-6902, -13821, -16128], ![-321, 246528, 0]], ![![-192, -384, -448], ![1, 6848, 0]], ![![-3806, -7621, -8893], ![-169, 135936, 0]]]
  g := ![![![1, 0, 0], ![-3, 107, 0], ![-59, 0, 107]], ![![0, 1, 0], ![-4, 6, 7], ![-2, -6, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-39, -46, 1]] ![![107, 0, 0], ![3, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![321, 107, 0]], ![![-4173, -4922, 107], ![-428, -321, -321]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![3, 1, 0]]], ![![![-39, -46, 1]], ![![-4, -3, -3]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [108, 61, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 63, 1], [47, 45, 108], [0, 1]]
 g := ![![[107, 93, 7], [65, 64], [80, 104, 31], [9, 97, 105], [70, 63], [1]], ![[24, 6, 40, 28], [16, 46], [58, 67, 107, 5], [88, 55, 61, 94], [68, 4], [49, 25, 16, 1]], ![[70, 81, 71, 102], [62, 3], [89, 97, 82, 100], [57, 44, 103, 102], [24, 29], [65, 30, 90, 108]]]
 h' := ![![[107, 63, 1], [34, 51, 94], [80, 101, 101], [9, 11, 85], [71, 31, 66], [1, 48, 45], [0, 1]], ![[47, 45, 108], [32, 52, 30], [4, 41, 68], [38, 39, 21], [5, 100, 58], [41, 81, 2], [107, 63, 1]], ![[0, 1], [55, 6, 94], [50, 76, 49], [38, 59, 3], [36, 87, 94], [11, 89, 62], [47, 45, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82, 44], []]
 b := ![[], [13, 48, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [108, 61, 64, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7607764, -2474409, -968247]
  a := ![4, 23, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-69796, -22701, -8883]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![25, -4, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![25, -4, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![25, 109, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![25, -4, 1], ![-185, 7, -30], ![813, 1, 28]]]
  hmulB := by decide  
  f := ![![![-24, 4, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -109, 113]], ![![0, -1, 1], ![5, 29, -30], ![1, -27, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [86, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 112], [0, 1]]
 g := ![![[112, 51], [18], [72], [62], [101, 95], [86, 1]], ![[91, 62], [18], [72], [62], [22, 18], [59, 112]]]
 h' := ![![[86, 112], [8, 86], [55, 73], [91, 80], [15, 66], [62, 78], [0, 1]], ![[0, 1], [59, 27], [5, 40], [78, 33], [41, 47], [103, 35], [86, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [51, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [86, 27, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6684, -1987, -605]
  a := ![-4, -1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![193, 566, -605]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![30, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![30, 1, 0]] 
 ![![113, 0, 0], ![30, 1, 0], ![85, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![30, 1, 0], ![3, 33, 7], ![-173, -6, 28]]]
  hmulB := by decide  
  f := ![![![14965, 181054, 38416], ![5650, -620144, 0]], ![![3948, 48034, 10192], ![1583, -164528, 0]], ![![11255, 136191, 28897], ![4257, -466480, 0]]]
  g := ![![![1, 0, 0], ![-30, 113, 0], ![-85, 0, 113]], ![![0, 1, 0], ![-14, 33, 7], ![-21, -6, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![25, -4, 1]] ![![113, 0, 0], ![30, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![3390, 113, 0]], ![![2825, -452, 113], ![565, -113, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![30, 1, 0]]], ![![![25, -4, 1]], ![![5, -1, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-6, -10, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-6, -10, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![121, 117, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-6, -10, 1], ![-203, -42, -72], ![1851, 37, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-121, -117, 127]], ![![-1, -1, 1], ![67, 66, -72], ![6, -8, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [88, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [116, 126], [0, 1]]
 g := ![![[16, 13], [36, 61], [54, 70], [100, 32], [93, 73], [116, 1]], ![[0, 114], [0, 66], [46, 57], [2, 95], [52, 54], [105, 126]]]
 h' := ![![[116, 126], [7, 93], [74, 76], [90, 109], [71, 64], [79, 33], [0, 1]], ![[0, 1], [0, 34], [0, 51], [34, 18], [2, 63], [97, 94], [116, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [121, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [88, 11, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9855, -5376, -707]
  a := ![6, 7, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![596, 609, -707]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-55, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-55, 1, 0]] 
 ![![127, 0, 0], ![72, 1, 0], ![118, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-55, 1, 0], ![3, -52, 7], ![-173, -6, -57]]]
  hmulB := by decide  
  f := ![![![7866, -171563, 23100], ![-4699, -419100, 0]], ![![4456, -97219, 13090], ![-2666, -237490, 0]], ![![7309, -159405, 21463], ![-4365, -389400, 0]]]
  g := ![![![1, 0, 0], ![-72, 127, 0], ![-118, 0, 127]], ![![-1, 1, 0], ![23, -52, 7], ![55, -6, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-6, -10, 1]] ![![127, 0, 0], ![-55, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-6985, 127, 0]], ![![-762, -1270, 127], ![127, 508, -127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-55, 1, 0]]], ![![![-6, -10, 1]], ![![1, 4, -1]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-55, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-55, 1, 0]] 
 ![![131, 0, 0], ![76, 1, 0], ![41, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-55, 1, 0], ![3, -52, 7], ![-173, -6, -57]]]
  hmulB := by decide  
  f := ![![![12916, -278143, 37450], ![-7467, -700850, 0]], ![![7495, -161323, 21721], ![-4322, -406493, 0]], ![![4076, -87053, 11721], ![-2257, -219350, 0]]]
  g := ![![![1, 0, 0], ![-76, 131, 0], ![-41, 0, 131]], ![![-1, 1, 0], ![28, -52, 7], ![20, -6, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-52, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-52, 1, 0]] 
 ![![131, 0, 0], ![79, 1, 0], ![123, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-52, 1, 0], ![3, -49, 7], ![-173, -6, -54]]]
  hmulB := by decide  
  f := ![![![17117, -339793, 48552], ![-9301, -908616, 0]], ![![10311, -204875, 29274], ![-5632, -547842, 0]], ![![16057, -319042, 45587], ![-8770, -853128, 0]]]
  g := ![![![1, 0, 0], ![-79, 131, 0], ![-123, 0, 131]], ![![-1, 1, 0], ![23, -49, 7], ![53, -6, -54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-25, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-25, 1, 0]] 
 ![![131, 0, 0], ![106, 1, 0], ![109, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-25, 1, 0], ![3, -22, 7], ![-173, -6, -27]]]
  hmulB := by decide  
  f := ![![![5056, -38711, 12320], ![-1179, -230560, 0]], ![![4098, -31321, 9968], ![-916, -186544, 0]], ![![4209, -32210, 10251], ![-970, -191840, 0]]]
  g := ![![![1, 0, 0], ![-106, 131, 0], ![-109, 0, 131]], ![![-1, 1, 0], ![12, -22, 7], ![26, -6, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-55, 1, 0]] ![![131, 0, 0], ![-52, 1, 0]]
  ![![131, 0, 0], ![16, 60, 1]] where
 M := ![![![17161, 0, 0], ![-6812, 131, 0]], ![![-7205, 131, 0], ![2863, -104, 7]]]
 hmul := by decide  
 g := ![![![![115, -60, -1], ![131, 0, 0]], ![![-52, 1, 0], ![0, 0, 0]]], ![![![-55, 1, 0], ![0, 0, 0]], ![![21, -4, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![16, 60, 1]] ![![131, 0, 0], ![-25, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-3275, 131, 0]], ![![2096, 7860, 131], ![-393, -1310, 393]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-25, 1, 0]]], ![![![16, 60, 1]], ![![-3, -10, 3]]]]
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
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-50, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-50, 1, 0]] 
 ![![137, 0, 0], ![87, 1, 0], ![17, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-50, 1, 0], ![3, -47, 7], ![-173, -6, -52]]]
  hmulB := by decide  
  f := ![![![19042, -352290, 52479], ![-9453, -1027089, 0]], ![![12081, -223676, 33320], ![-6027, -652120, 0]], ![![2372, -43715, 6512], ![-1148, -127449, 0]]]
  g := ![![![1, 0, 0], ![-87, 137, 0], ![-17, 0, 137]], ![![-1, 1, 0], ![29, -47, 7], ![9, -6, -52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-45, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-45, 1, 0]] 
 ![![137, 0, 0], ![92, 1, 0], ![24, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-45, 1, 0], ![3, -42, 7], ![-173, -6, -47]]]
  hmulB := by decide  
  f := ![![![14851, -238092, 39690], ![-6576, -776790, 0]], ![![9982, -159862, 26649], ![-4383, -521559, 0]], ![![2622, -41710, 6953], ![-1090, -136080, 0]]]
  g := ![![![1, 0, 0], ![-92, 137, 0], ![-24, 0, 137]], ![![-1, 1, 0], ![27, -42, 7], ![11, -6, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-43, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-43, 1, 0]] 
 ![![137, 0, 0], ![94, 1, 0], ![107, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-43, 1, 0], ![3, -40, 7], ![-173, -6, -45]]]
  hmulB := by decide  
  f := ![![![22103, -333612, 58394], ![-9316, -1142854, 0]], ![![15192, -228874, 40061], ![-6301, -784051, 0]], ![![17251, -260558, 45607], ![-7314, -892594, 0]]]
  g := ![![![1, 0, 0], ![-94, 137, 0], ![-107, 0, 137]], ![![-1, 1, 0], ![22, -40, 7], ![38, -6, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-50, 1, 0]] ![![137, 0, 0], ![-45, 1, 0]]
  ![![137, 0, 0], ![-50, 26, 1]] where
 M := ![![![18769, 0, 0], ![-6165, 137, 0]], ![![-6850, 137, 0], ![2253, -92, 7]]]
 hmul := by decide  
 g := ![![![![137, 0, 0], ![0, 0, 0]], ![![5, -25, -1], ![137, 0, 0]]], ![![![0, -25, -1], ![137, 0, 0]], ![![19, -2, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-50, 26, 1]] ![![137, 0, 0], ![-43, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-5891, 137, 0]], ![![-6850, 3562, 137], ![2055, -1096, 137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-43, 1, 0]]], ![![![-50, 26, 1]], ![![15, -8, 1]]]]
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


lemma PB256I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB256I2 : PrimesBelowBoundCertificateInterval O 79 137 256 where
  m := 11
  g := ![2, 2, 3, 1, 1, 2, 1, 2, 2, 3, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB256I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![97, 97, 97]
    · exact ![1030301]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![12769, 113]
    · exact ![16129, 127]
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
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I83N1, I89N1, I97N0, I97N1, I107N1, I113N1, I127N1, I131N0, I131N1, I131N2, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [I89N1], [I97N0, I97N0, I97N1], [], [], [I107N1], [], [I113N1], [I127N1], [I131N0, I131N1, I131N2], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
