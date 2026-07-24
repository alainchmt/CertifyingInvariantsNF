
import IdealArithmetic.Examples.NF3_1_960204_2.RI3_1_960204_2
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [31, 19, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 62, 67], [25, 20, 16], [0, 1]]
 g := ![![[73, 8, 81], [58, 51, 27], [32, 64], [39, 63], [73, 3, 1], []], ![[44, 20, 60, 74], [25, 40, 22, 74], [51, 61], [44, 38], [16, 58, 48, 74], [29, 7]], ![[78, 76, 50, 10], [43, 37, 78, 3], [1, 16], [74, 41], [78, 40, 28, 1], [80, 7]]]
 h' := ![![[61, 62, 67], [28, 73, 74], [73, 6, 39], [22, 10, 75], [61, 14, 48], [0, 0, 1], [0, 1]], ![[25, 20, 16], [82, 51, 63], [24, 65, 20], [51, 36, 12], [2, 56, 72], [0, 73, 20], [61, 62, 67]], ![[0, 1], [39, 42, 29], [5, 12, 24], [6, 37, 79], [15, 13, 46], [54, 10, 62], [25, 20, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 18], []]
 b := ![[], [45, 30, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [31, 19, 80, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![84992, 8964, -77937]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1024, 108, -939]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![17, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![17, 1, 0]] 
 ![![89, 0, 0], ![17, 1, 0], ![87, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![17, 1, 0], ![-1, 16, 3], ![51, -42, 18]]]
  hmulB := by decide  
  f := ![![![-1616, 25872, 4851], ![0, -143913, 0]], ![![-308, 4928, 924], ![1, -27412, 0]], ![![-1590, 25290, 4742], ![54, -140679, 0]]]
  g := ![![![1, 0, 0], ![-17, 89, 0], ![-87, 0, 89]], ![![0, 1, 0], ![-6, 16, 3], ![-9, -42, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![23, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![23, 1, 0]] 
 ![![89, 0, 0], ![23, 1, 0], ![9, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![23, 1, 0], ![-1, 22, 3], ![51, -42, 24]]]
  hmulB := by decide  
  f := ![![![-1301, 28644, 3906], ![0, -115878, 0]], ![![-336, 7392, 1008], ![1, -29904, 0]], ![![-145, 2896, 395], ![52, -11718, 0]]]
  g := ![![![1, 0, 0], ![-23, 89, 0], ![-9, 0, 89]], ![![0, 1, 0], ![-6, 22, 3], ![9, -42, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-40, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-40, 1, 0]] 
 ![![89, 0, 0], ![49, 1, 0], ![76, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-40, 1, 0], ![-1, -41, 3], ![51, -42, -39]]]
  hmulB := by decide  
  f := ![![![381, 13939, -1020], ![89, 30260, 0]], ![![228, 7666, -561], ![90, 16643, 0]], ![![324, 11903, -871], ![73, 25840, 0]]]
  g := ![![![1, 0, 0], ![-49, 89, 0], ![-76, 0, 89]], ![![-1, 1, 0], ![20, -41, 3], ![57, -42, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![17, 1, 0]] ![![89, 0, 0], ![23, 1, 0]]
  ![![89, 0, 0], ![41, 13, 1]] where
 M := ![![![7921, 0, 0], ![2047, 89, 0]], ![![1513, 89, 0], ![390, 39, 3]]]
 hmul := by decide  
 g := ![![![![48, -13, -1], ![89, 0, 0]], ![![-18, -12, -1], ![89, 0, 0]]], ![![![-24, -12, -1], ![89, 0, 0]], ![![3, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![41, 13, 1]] ![![89, 0, 0], ![-40, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-3560, 89, 0]], ![![3649, 1157, 89], ![-1602, -534, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-40, 1, 0]]], ![![![41, 13, 1]], ![![-18, -6, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [96, 20, 91, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 81, 50], [67, 15, 47], [0, 1]]
 g := ![![[36, 23, 16], [80, 81], [55, 49], [23, 22], [73, 36], [1]], ![[13, 87, 73, 93], [70, 47], [74, 8], [47, 85], [95, 11], [61, 25, 82, 64]], ![[76, 36, 10, 79], [7, 9], [36, 53], [50, 70], [83, 88], [26, 66, 81, 33]]]
 h' := ![![[36, 81, 50], [14, 3, 4], [82, 1, 88], [67, 73, 7], [74, 88, 33], [1, 77, 6], [0, 1]], ![[67, 15, 47], [27, 53, 16], [65, 72, 12], [31, 3, 69], [9, 80, 45], [60, 35, 60], [36, 81, 50]], ![[0, 1], [3, 41, 77], [44, 24, 94], [28, 21, 21], [50, 26, 19], [89, 82, 31], [67, 15, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84, 21], []]
 b := ![[], [32, 31, 83], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [96, 20, 91, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1033632, -1485749, 622934]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10656, -15317, 6422]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![50, -2, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![50, -2, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![50, 99, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![50, -2, 1], ![53, 10, -5], ![-54, 87, 7]]]
  hmulB := by decide  
  f := ![![![-49, 2, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-50, -99, 101]], ![![0, -1, 1], ![3, 5, -5], ![-4, -6, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [33, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 100], [0, 1]]
 g := ![![[74, 49], [68], [38, 16], [58], [43], [83, 1]], ![[0, 52], [68], [53, 85], [58], [43], [65, 100]]]
 h' := ![![[83, 100], [25, 7], [59, 13], [35, 97], [38, 19], [89, 89], [0, 1]], ![[0, 1], [0, 94], [27, 88], [6, 4], [100, 82], [2, 12], [83, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [22, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [33, 18, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![201852, 24759, -185645]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![93902, 182214, -185645]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![5, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![5, 1, 0]] 
 ![![101, 0, 0], ![5, 1, 0], ![94, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![5, 1, 0], ![-1, 4, 3], ![51, -42, 6]]]
  hmulB := by decide  
  f := ![![![-6641, 26568, 19926], ![0, -670842, 0]], ![![-328, 1312, 984], ![1, -33128, 0]], ![![-6179, 24727, 18545], ![-35, -624348, 0]]]
  g := ![![![1, 0, 0], ![-5, 101, 0], ![-94, 0, 101]], ![![0, 1, 0], ![-3, 4, 3], ![-3, -42, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![50, -2, 1]] ![![101, 0, 0], ![5, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![505, 101, 0]], ![![5050, -202, 101], ![303, 0, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![5, 1, 0]]], ![![![50, -2, 1]], ![![3, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![35, -29, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![35, -29, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![35, 74, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![35, -29, 1], ![80, 22, -86], ![-1431, 1221, -35]]]
  hmulB := by decide  
  f := ![![![-34, 29, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -74, 103]], ![![0, -1, 1], ![30, 62, -86], ![-2, 37, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [26, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 102], [0, 1]]
 g := ![![[51, 4], [102, 8], [65, 98], [98], [55], [13, 1]], ![[0, 99], [0, 95], [0, 5], [98], [55], [26, 102]]]
 h' := ![![[13, 102], [26, 101], [61, 27], [44, 60], [29, 43], [74, 40], [0, 1]], ![[0, 1], [0, 2], [0, 76], [0, 43], [73, 60], [79, 63], [13, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [62, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [26, 90, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![97, 3248, -3408]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1159, 2480, -3408]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-17, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-17, 1, 0]] 
 ![![103, 0, 0], ![86, 1, 0], ![35, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-17, 1, 0], ![-1, -18, 3], ![51, -42, -16]]]
  hmulB := by decide  
  f := ![![![276, 4643, -774], ![103, 26574, 0]], ![![233, 3869, -645], ![104, 22145, 0]], ![![89, 1578, -263], ![6, 9030, 0]]]
  g := ![![![1, 0, 0], ![-86, 103, 0], ![-35, 0, 103]], ![![-1, 1, 0], ![14, -18, 3], ![41, -42, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![35, -29, 1]] ![![103, 0, 0], ![-17, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-1751, 103, 0]], ![![3605, -2987, 103], ![-515, 515, -103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-17, 1, 0]]], ![![![35, -29, 1]], ![![-5, 5, -1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [46, 25, 69, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 23, 33], [100, 83, 74], [0, 1]]
 g := ![![[6, 93, 27], [56, 8, 13], [82, 64], [97, 1, 92], [7, 53], [1]], ![[43, 52, 93, 42], [20, 94, 3, 102], [1, 39], [73, 50, 0, 100], [85, 90], [49, 9, 99, 92]], ![[58, 84, 90, 70], [65, 97, 17, 84], [39, 52], [35, 43, 24, 26], [59, 62], [28, 46, 58, 15]]]
 h' := ![![[45, 23, 33], [99, 30, 54], [34, 19, 21], [32, 80, 99], [82, 8, 29], [61, 82, 38], [0, 1]], ![[100, 83, 74], [1, 38, 15], [100, 17, 16], [50, 74, 50], [25, 32, 103], [61, 56, 82], [45, 23, 33]], ![[0, 1], [1, 39, 38], [4, 71, 70], [34, 60, 65], [102, 67, 82], [81, 76, 94], [100, 83, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 36], []]
 b := ![[], [78, 44, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [46, 25, 69, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![80250, 8667, -73830]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![750, 81, -690]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![3, -17, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![3, -17, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![3, 92, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![3, -17, 1], ![68, -22, -50], ![-819, 717, -55]]]
  hmulB := by decide  
  f := ![![![-2, 17, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -92, 109]], ![![0, -1, 1], ![2, 42, -50], ![-6, 53, -55]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [26, 86, 1] where
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
 g := ![![[62, 21], [29], [21, 60], [37, 49], [20], [23, 1]], ![[0, 88], [29], [93, 49], [74, 60], [20], [46, 108]]]
 h' := ![![[23, 108], [10, 28], [108, 47], [19, 13], [0, 7], [56, 67], [0, 1]], ![[0, 1], [0, 81], [99, 62], [100, 96], [52, 102], [71, 42], [23, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [97, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [26, 86, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7729, -4812, 796]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![49, -716, 796]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![50, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![50, 1, 0]] 
 ![![109, 0, 0], ![50, 1, 0], ![55, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![50, 1, 0], ![-1, 49, 3], ![51, -42, 51]]]
  hmulB := by decide  
  f := ![![![-71, 3528, 216], ![0, -7848, 0]], ![![-33, 1617, 99], ![1, -3597, 0]], ![![-45, 1780, 109], ![20, -3960, 0]]]
  g := ![![![1, 0, 0], ![-50, 109, 0], ![-55, 0, 109]], ![![0, 1, 0], ![-24, 49, 3], ![-6, -42, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![3, -17, 1]] ![![109, 0, 0], ![50, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![5450, 109, 0]], ![![327, -1853, 109], ![218, -872, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![50, 1, 0]]], ![![![3, -17, 1]], ![![2, -8, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![37, -14, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![37, -14, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![37, 99, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![37, -14, 1], ![65, 9, -41], ![-666, 591, -18]]]
  hmulB := by decide  
  f := ![![![-36, 14, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -99, 113]], ![![0, -1, 1], ![14, 36, -41], ![0, 21, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [36, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 112], [0, 1]]
 g := ![![[7, 22], [56], [62], [25], [26, 88], [87, 1]], ![[0, 91], [56], [62], [25], [111, 25], [61, 112]]]
 h' := ![![[87, 112], [71, 94], [36, 100], [11, 47], [81, 5], [32, 75], [0, 1]], ![[0, 1], [0, 19], [35, 13], [32, 66], [64, 108], [3, 38], [87, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [59, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [36, 26, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-817, 1488, -752]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![239, 672, -752]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![41, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![41, 1, 0]] 
 ![![113, 0, 0], ![41, 1, 0], ![18, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![41, 1, 0], ![-1, 40, 3], ![51, -42, 42]]]
  hmulB := by decide  
  f := ![![![7508, -301921, -22644], ![113, 852924, 0]], ![![2697, -109521, -8214], ![114, 309394, 0]], ![![1180, -48094, -3607], ![62, 135864, 0]]]
  g := ![![![1, 0, 0], ![-41, 113, 0], ![-18, 0, 113]], ![![0, 1, 0], ![-15, 40, 3], ![9, -42, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![37, -14, 1]] ![![113, 0, 0], ![41, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![4633, 113, 0]], ![![4181, -1582, 113], ![1582, -565, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![41, 1, 0]]], ![![![37, -14, 1]], ![![14, -5, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![46, 11, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![46, 11, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![46, 11, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![46, 11, 1], ![40, -7, 34], ![609, -459, 16]]]
  hmulB := by decide  
  f := ![![![-45, -11, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-46, -11, 127]], ![![0, 0, 1], ![-12, -3, 34], ![-1, -5, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [26, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 126], [0, 1]]
 g := ![![[51, 44], [12, 100], [2, 120], [106, 49], [78, 34], [71, 1]], ![[0, 83], [0, 27], [13, 7], [29, 78], [79, 93], [15, 126]]]
 h' := ![![[71, 126], [69, 67], [75, 117], [38, 45], [4, 7], [59, 62], [0, 1]], ![[0, 1], [0, 60], [0, 10], [58, 82], [120, 120], [16, 65], [71, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [67, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [26, 56, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1033, 559, -1173]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![433, 106, -1173]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-34, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-34, 1, 0]] 
 ![![127, 0, 0], ![93, 1, 0], ![111, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-34, 1, 0], ![-1, -35, 3], ![51, -42, -33]]]
  hmulB := by decide  
  f := ![![![-6775, -237160, 20328], ![0, -860552, 0]], ![![-4960, -173635, 14883], ![1, -630047, 0]], ![![-5907, -207282, 17767], ![54, -752136, 0]]]
  g := ![![![1, 0, 0], ![-93, 127, 0], ![-111, 0, 127]], ![![-1, 1, 0], ![23, -35, 3], ![60, -42, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![46, 11, 1]] ![![127, 0, 0], ![-34, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-4318, 127, 0]], ![![5842, 1397, 127], ![-1524, -381, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-34, 1, 0]]], ![![![46, 11, 1]], ![![-12, -3, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![5, 52, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![5, 52, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![5, 52, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![5, 52, 1], ![-1, -89, 157], ![2700, -2181, 16]]]
  hmulB := by decide  
  f := ![![![-4, -52, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -52, 131]], ![![0, 0, 1], ![-6, -63, 157], ![20, -23, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [24, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 130], [0, 1]]
 g := ![![[94, 7], [118, 20], [117], [114], [75], [55], [1]], ![[22, 124], [62, 111], [117], [114], [75], [55], [1]]]
 h' := ![![[102, 130], [50, 20], [75, 85], [1, 36], [95, 30], [42, 59], [107, 102], [0, 1]], ![[0, 1], [125, 111], [99, 46], [5, 95], [11, 101], [34, 72], [31, 29], [102, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [71, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [24, 29, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1224, 75, -1170]
  a := ![0, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![54, 465, -1170]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-26, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-26, 1, 0]] 
 ![![131, 0, 0], ![105, 1, 0], ![115, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-26, 1, 0], ![-1, -27, 3], ![51, -42, -25]]]
  hmulB := by decide  
  f := ![![![57, 809, -90], ![131, 3930, 0]], ![![25, 648, -72], ![1, 3144, 0]], ![![29, 711, -79], ![9, 3450, 0]]]
  g := ![![![1, 0, 0], ![-105, 131, 0], ![-115, 0, 131]], ![![-1, 1, 0], ![19, -27, 3], ![56, -42, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![5, 52, 1]] ![![131, 0, 0], ![-26, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-3406, 131, 0]], ![![655, 6812, 131], ![-131, -1441, 131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-26, 1, 0]]], ![![![5, 52, 1]], ![![-1, -11, 1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-33, -40, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-33, -40, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![104, 97, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-33, -40, 1], ![91, -35, -119], ![-1992, 1683, -114]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-104, -97, 137]], ![![-1, -1, 1], ![91, 84, -119], ![72, 93, -114]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [101, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 136], [0, 1]]
 g := ![![[28, 19], [129], [39], [10, 78], [103], [72], [1]], ![[0, 118], [129], [39], [133, 59], [103], [72], [1]]]
 h' := ![![[49, 136], [51, 108], [32, 102], [86, 54], [110, 30], [52, 69], [36, 49], [0, 1]], ![[0, 1], [0, 29], [98, 35], [129, 83], [73, 107], [8, 68], [108, 88], [49, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104]]
 b := ![[], [96, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [101, 88, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6935, 7104, -1712]
  a := ![-2, -12, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1249, 1264, -1712]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-18, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-18, 1, 0]] 
 ![![137, 0, 0], ![119, 1, 0], ![114, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-18, 1, 0], ![-1, -19, 3], ![51, -42, -17]]]
  hmulB := by decide  
  f := ![![![-3837, -72922, 11514], ![0, -525806, 0]], ![![-3332, -63327, 9999], ![1, -456621, 0]], ![![-3186, -60680, 9581], ![52, -437532, 0]]]
  g := ![![![1, 0, 0], ![-119, 137, 0], ![-114, 0, 137]], ![![-1, 1, 0], ![14, -19, 3], ![51, -42, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-33, -40, 1]] ![![137, 0, 0], ![-18, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-2466, 137, 0]], ![![-4521, -5480, 137], ![685, 685, -137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-18, 1, 0]]], ![![![-33, -40, 1]], ![![5, 5, -1]]]]
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


lemma PB278I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB278I2 : PrimesBelowBoundCertificateInterval O 79 137 278 where
  m := 11
  g := ![1, 3, 1, 2, 2, 1, 2, 2, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB278I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
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
    · exact ![571787]
    · exact ![89, 89, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![12769, 113]
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
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
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
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I89N0, I89N1, I89N2, I101N1, I103N1, I109N1, I113N1, I127N1, I131N1, I137N1]
  Il := ![[], [I89N0, I89N1, I89N2], [], [I101N1], [I103N1], [], [I109N1], [I113N1], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
