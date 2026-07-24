
import IdealArithmetic.Examples.NF3_3_653844_1.RI3_3_653844_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 5, 2]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-13, 5, 2]] 
 ![![83, 0, 0], ![0, 83, 0], ![35, 44, 1]] where
  M :=![![![-13, 5, 2], ![276, 79, 15], ![690, 322, 79]]]
  hmulB := by decide  
  f := ![![![-17, -3, 1]], ![![138, 29, -9]], ![![61, 13, -4]]]
  g := ![![![-1, -1, 2], ![-3, -7, 15], ![-25, -38, 79]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [30, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 82], [0, 1]]
 g := ![![[43, 36], [74, 33], [12], [59], [53, 33], [1]], ![[0, 47], [0, 50], [12], [59], [62, 50], [1]]]
 h' := ![![[38, 82], [21, 6], [50, 38], [59, 26], [70, 15], [53, 38], [0, 1]], ![[0, 1], [0, 77], [0, 45], [51, 57], [59, 68], [3, 45], [38, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [32, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [30, 45, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![306, 93, 4]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2, -1, 4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -3, 1]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-17, -3, 1]] 
 ![![83, 0, 0], ![34, 1, 0], ![2, 0, 1]] where
  M :=![![![-17, -3, 1], ![138, 29, -9], ![-414, -92, 29]]]
  hmulB := by decide  
  f := ![![![-13, 5, 2]], ![![-2, 3, 1]], ![![8, 4, 1]]]
  g := ![![![1, -3, 1], ![-10, 29, -9], ![32, -92, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-13, 5, 2]] ![![-17, -3, 1]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4565, -1872, -431]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-4565, -1872, -431]] 
 ![![89, 0, 0], ![8, 1, 0], ![38, 0, 1]] where
  M :=![![![-4565, -1872, -431], ![-59478, -24391, -5616], ![-258336, -105938, -24391]]]
  hmulB := by decide  
  f := ![![![26927, 674, -631]], ![![1442, 37, -34]], ![![12542, 310, -293]]]
  g := ![![![301, -1872, -431], ![3922, -24391, -5616], ![17034, -105938, -24391]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1529, 39, -36]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![1529, 39, -36]] 
 ![![89, 0, 0], ![84, 1, 0], ![51, 0, 1]] where
  M :=![![![1529, 39, -36], ![-4968, -127, 117], ![5382, 138, -127]]]
  hmulB := by decide  
  f := ![![![-17, -15, -9]], ![![-30, -19, -9]], ![![-33, -21, -10]]]
  g := ![![![1, 39, -36], ![-3, -127, 117], ![3, 138, -127]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-127, -25, 8]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![-127, -25, 8]] 
 ![![89, 0, 0], ![86, 1, 0], ![86, 0, 1]] where
  M :=![![![-127, -25, 8], ![1104, 241, -75], ![-3450, -782, 241]]]
  hmulB := by decide  
  f := ![![![-569, -231, -53]], ![![-632, -257, -59]], ![![-908, -370, -85]]]
  g := ![![![15, -25, 8], ![-148, 241, -75], ![484, -782, 241]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-4565, -1872, -431]] ![![1529, 39, -36]]
  ![![569, 231, 53]] where
 M := ![![![569, 231, 53]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![569, 231, 53]] ![![-127, -25, 8]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [59, 57, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 75, 37], [91, 21, 60], [0, 1]]
 g := ![![[15, 80, 50], [4, 43], [79, 86], [32, 6], [3, 33], [1]], ![[79, 24, 61, 23], [82, 48], [66, 50], [], [38, 61], [17, 77, 96, 19]], ![[84, 9, 42, 51], [72, 31], [32, 24], [71, 6], [5, 95], [76, 40, 65, 78]]]
 h' := ![![[85, 75, 37], [11, 7, 70], [76, 31, 72], [88, 59, 59], [6, 49, 43], [38, 40, 79], [0, 1]], ![[91, 21, 60], [34, 79, 80], [33, 87, 40], [12, 61, 27], [20, 67], [82, 19, 35], [85, 75, 37]], ![[0, 1], [12, 11, 44], [34, 76, 82], [46, 74, 11], [89, 78, 54], [53, 38, 80], [91, 21, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 6], []]
 b := ![[], [37, 4, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [59, 57, 18, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-199529, 1746, 61110]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2057, 18, 630]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [83, 95, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 86, 27], [9, 14, 74], [0, 1]]
 g := ![![[23, 86, 70], [39, 19], [28, 21, 9], [20, 24], [17, 58], [1]], ![[88, 25, 52, 74], [16, 30], [95, 98, 55, 89], [87, 81], [58, 71], [13, 14, 95, 89]], ![[90, 29, 42, 57], [56, 68], [3, 21, 48, 2], [81, 14], [25, 31], [91, 12, 41, 12]]]
 h' := ![![[10, 86, 27], [97, 46, 26], [100, 63, 76], [27, 76, 3], [24, 49, 78], [18, 6, 19], [0, 1]], ![[9, 14, 74], [87, 42, 91], [1, 6, 38], [18, 71, 74], [13, 47, 92], [22, 72, 24], [10, 86, 27]], ![[0, 1], [74, 13, 85], [50, 32, 88], [74, 55, 24], [63, 5, 32], [44, 23, 58], [9, 14, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 74], []]
 b := ![[], [27, 81, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [83, 95, 82, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![111201, 8787, -9393]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1101, 87, -93]
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


def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, -20, 6]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-79, -20, 6]] 
 ![![103, 0, 0], ![56, 1, 0], ![19, 0, 1]] where
  M :=![![![-79, -20, 6], ![828, 197, -60], ![-2760, -644, 197]]]
  hmulB := by decide  
  f := ![![![-169, -76, -18]], ![![-116, -51, -12]], ![![-133, -56, -13]]]
  g := ![![![9, -20, 6], ![-88, 197, -60], ![287, -644, 197]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-197, -37, 12]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-197, -37, 12]] 
 ![![103, 0, 0], ![94, 1, 0], ![76, 0, 1]] where
  M :=![![![-197, -37, 12], ![1656, 355, -111], ![-5106, -1150, 355]]]
  hmulB := by decide  
  f := ![![![-1625, -665, -153]], ![![-1688, -691, -159]], ![![-2090, -856, -197]]]
  g := ![![![23, -37, 12], ![-226, 355, -111], ![738, -1150, 355]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-79, -20, 6]] ![![-79, -20, 6]]
  ![![-26879, -6224, 1908]] where
 M := ![![![-26879, -6224, 1908]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-26879, -6224, 1908]] ![![-197, -37, 12]]
  ![![103, 0, 0]] where
 M := ![![![-14754029, -3409197, 1045656]]]
 hmul := by decide  
 g := ![![![![-143243, -33099, 10152]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1583, -366, 112]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-1583, -366, 112]] 
 ![![107, 0, 0], ![0, 107, 0], ![90, 98, 1]] where
  M :=![![![-1583, -366, 112], ![15456, 3569, -1098], ![-50508, -11684, 3569]]]
  hmulB := by decide  
  f := ![![![-853, -22, 20]], ![![2760, 67, -66]], ![![1782, 42, -43]]]
  g := ![![![-109, -106, 112], ![1068, 1039, -1098], ![-3474, -3378, 3569]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [21, 53, 1] where
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
 g := ![![[28, 4], [64, 13], [101], [8, 1], [36], [54, 1]], ![[30, 103], [17, 94], [101], [62, 106], [36], [1, 106]]]
 h' := ![![[54, 106], [47, 105], [102, 21], [46, 84], [23, 106], [43, 6], [0, 1]], ![[0, 1], [46, 2], [59, 86], [88, 23], [76, 1], [46, 101], [54, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [61, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [21, 53, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-753, 193, 252]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-219, -229, 252]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-853, -22, 20]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-853, -22, 20]] 
 ![![107, 0, 0], ![27, 1, 0], ![78, 0, 1]] where
  M :=![![![-853, -22, 20], ![2760, 67, -66], ![-3036, -92, 67]]]
  hmulB := by decide  
  f := ![![![-1583, -366, 112]], ![![-255, -59, 18]], ![![-1626, -376, 115]]]
  g := ![![![-17, -22, 20], ![57, 67, -66], ![-54, -92, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-1583, -366, 112]] ![![-853, -22, 20]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-143, -60, -14]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-143, -60, -14]] 
 ![![109, 0, 0], ![0, 109, 0], ![18, 51, 1]] where
  M :=![![![-143, -60, -14], ![-1932, -787, -180], ![-8280, -3404, -787]]]
  hmulB := by decide  
  f := ![![![61, 4, -2]], ![![-276, -31, 12]], ![![-114, -13, 5]]]
  g := ![![![1, 6, -14], ![12, 77, -180], ![54, 337, -787]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [22, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 108], [0, 1]]
 g := ![![[29, 5], [46], [88, 35], [62, 22], [38], [16, 1]], ![[0, 104], [46], [103, 74], [87, 87], [38], [32, 108]]]
 h' := ![![[16, 108], [100, 21], [26, 68], [53, 12], [7, 26], [84, 16], [0, 1]], ![[0, 1], [0, 88], [24, 41], [27, 97], [96, 83], [13, 93], [16, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [52, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [22, 93, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![298, 45, -44]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, 21, -44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 4, -2]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![61, 4, -2]] 
 ![![109, 0, 0], ![65, 1, 0], ![45, 0, 1]] where
  M :=![![![61, 4, -2], ![-276, -31, 12], ![552, 92, -31]]]
  hmulB := by decide  
  f := ![![![-143, -60, -14]], ![![-103, -43, -10]], ![![-135, -56, -13]]]
  g := ![![![-1, 4, -2], ![11, -31, 12], ![-37, 92, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-143, -60, -14]] ![![61, 4, -2]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [77, 102, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 13, 36], [107, 99, 77], [0, 1]]
 g := ![![[75, 107, 91], [20, 102], [58, 100], [52, 30], [24, 100, 98], [1]], ![[70, 99, 34, 50], [70, 41], [37, 14], [64, 100], [48, 13, 0, 82], [109, 95, 41, 100]], ![[94, 0, 82, 98], [27, 32], [1, 18], [15, 36], [21, 50, 29, 111], [51, 40, 26, 13]]]
 h' := ![![[101, 13, 36], [46, 103, 54], [111, 15, 92], [82, 59, 10], [73, 75, 16], [36, 11, 95], [0, 1]], ![[107, 99, 77], [70, 104, 14], [6, 104, 43], [97, 57, 63], [36, 65, 103], [49, 65, 83], [101, 13, 36]], ![[0, 1], [15, 19, 45], [25, 107, 91], [92, 110, 40], [2, 86, 107], [38, 37, 48], [107, 99, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 9], []]
 b := ![[], [100, 17, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [77, 102, 18, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3318132, 1261193, 183286]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29364, 11161, 1622]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97259, 39884, 9183]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![97259, 39884, 9183]] 
 ![![127, 0, 0], ![0, 127, 0], ![45, 49, 1]] where
  M :=![![![97259, 39884, 9183], ![1267254, 519677, 119652], ![5503992, 2257082, 519677]]]
  hmulB := by decide  
  f := ![![![1505, 106, -51]], ![![-7038, -841, 318]], ![![-2067, -267, 98]]]
  g := ![![![-2488, -3229, 9183], ![-32418, -42073, 119652], ![-140799, -182733, 519677]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [33, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 126], [0, 1]]
 g := ![![[25, 16], [11, 100], [34, 98], [25, 4], [97, 1], [64, 1]], ![[33, 111], [61, 27], [83, 29], [27, 123], [34, 126], [1, 126]]]
 h' := ![![[64, 126], [18, 4], [21, 117], [64, 112], [101, 2], [47, 126], [0, 1]], ![[0, 1], [20, 123], [16, 10], [120, 15], [102, 125], [110, 1], [64, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [40, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [33, 63, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-857, -47, 12]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, -5, 12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1505, -106, 51]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-1505, -106, 51]] 
 ![![127, 0, 0], ![107, 1, 0], ![36, 0, 1]] where
  M :=![![![-1505, -106, 51], ![7038, 841, -318], ![-14628, -2530, 841]]]
  hmulB := by decide  
  f := ![![![-97259, -39884, -9183]], ![![-91921, -37695, -8679]], ![![-70908, -29078, -6695]]]
  g := ![![![63, -106, 51], ![-563, 841, -318], ![1778, -2530, 841]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![97259, 39884, 9183]] ![![-1505, -106, 51]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2749, 636, -195]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![2749, 636, -195]] 
 ![![131, 0, 0], ![0, 131, 0], ![86, 31, 1]] where
  M :=![![![2749, 636, -195], ![-26910, -6221, 1908], ![87768, 20286, -6221]]]
  hmulB := by decide  
  f := ![![![-37, 6, 3]], ![![414, 101, 18]], ![![80, 31, 7]]]
  g := ![![![149, 51, -195], ![-1458, -499, 1908], ![4754, 1627, -6221]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [91, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 130], [0, 1]]
 g := ![![[71, 36], [98, 46], [59], [81], [74], [61], [1]], ![[0, 95], [0, 85], [59], [81], [74], [61], [1]]]
 h' := ![![[89, 130], [121, 6], [102, 96], [121, 94], [126, 122], [110, 104], [40, 89], [0, 1]], ![[0, 1], [0, 125], [0, 35], [103, 37], [111, 9], [65, 27], [101, 42], [89, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [17, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [91, 42, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![643, 410, 271]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-173, -61, 271]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, 6, 3]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-37, 6, 3]] 
 ![![131, 0, 0], ![38, 1, 0], ![130, 0, 1]] where
  M :=![![![-37, 6, 3], ![414, 101, 18], ![828, 414, 101]]]
  hmulB := by decide  
  f := ![![![2749, 636, -195]], ![![592, 137, -42]], ![![3398, 786, -241]]]
  g := ![![![-5, 6, 3], ![-44, 101, 18], ![-214, 414, 101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![2749, 636, -195]] ![![-37, 6, 3]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-172225, -70626, -16261]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-172225, -70626, -16261]] 
 ![![137, 0, 0], ![0, 137, 0], ![104, 119, 1]] where
  M :=![![![-172225, -70626, -16261], ![-2244018, -920231, -211878], ![-9746388, -3996802, -920231]]]
  hmulB := by decide  
  f := ![![![68035, 1732, -1601]], ![![-220938, -5611, 5196]], ![![-138518, -3515, 3257]]]
  g := ![![![11087, 13609, -16261], ![144462, 177323, -211878], ![627428, 770151, -920231]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [18, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 136], [0, 1]]
 g := ![![[21, 99], [36], [22], [91, 22], [72], [130], [1]], ![[0, 38], [36], [22], [132, 115], [72], [130], [1]]]
 h' := ![![[33, 136], [35, 28], [51, 131], [6, 76], [88, 61], [39, 88], [119, 33], [0, 1]], ![[0, 1], [0, 109], [127, 6], [48, 61], [46, 76], [66, 49], [112, 104], [33, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [36, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [18, 104, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5290, -2736, 700]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-570, -628, 700]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-68035, -1732, 1601]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-68035, -1732, 1601]] 
 ![![137, 0, 0], ![54, 1, 0], ![124, 0, 1]] where
  M :=![![![-68035, -1732, 1601], ![220938, 5611, -5196], ![-239016, -6026, 5611]]]
  hmulB := by decide  
  f := ![![![172225, 70626, 16261]], ![![84264, 34555, 7956]], ![![227024, 93098, 21435]]]
  g := ![![![-1263, -1732, 1601], ![4104, 5611, -5196], ![-4448, -6026, 5611]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-172225, -70626, -16261]] ![![-68035, -1732, 1601]]
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


lemma PB180I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB180I2 : PrimesBelowBoundCertificateInterval O 79 137 180 where
  m := 11
  g := ![2, 3, 1, 1, 3, 2, 2, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB180I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0, I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
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
    · exact ![89, 89, 89]
    · exact ![912673]
    · exact ![1030301]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
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
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N0, I89N1, I89N2, I103N0, I103N1, I107N1, I109N1, I127N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N0, I89N1, I89N2], [], [], [I103N0, I103N0, I103N1], [I107N1], [I109N1], [], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
