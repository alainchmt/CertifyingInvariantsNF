
import IdealArithmetic.Examples.NF3_1_428868_2.RI3_1_428868_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![47, 28, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![47, 28, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![47, 28, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![47, 28, 1], ![95, 46, 55], ![2565, -750, -9]]]
  hmulB := by decide  
  f := ![![![-46, -28, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -28, 83]], ![![0, 0, 1], ![-30, -18, 55], ![36, -6, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [8, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 82], [0, 1]]
 g := ![![[72, 4], [71, 33], [17], [36], [45, 25], [1]], ![[9, 79], [70, 50], [17], [36], [4, 58], [1]]]
 h' := ![![[5, 82], [13, 2], [34, 45], [81, 10], [55, 6], [75, 5], [0, 1]], ![[0, 1], [23, 81], [10, 38], [48, 73], [2, 77], [17, 78], [5, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [23, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [8, 78, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![293, 58, -490]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![281, 166, -490]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![28, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![28, 1, 0]] 
 ![![83, 0, 0], ![28, 1, 0], ![9, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![28, 1, 0], ![0, 29, 2], ![95, -29, 27]]]
  hmulB := by decide  
  f := ![![![29, 1, 0], ![-83, 0, 0]], ![![-28, -1, 0], ![84, 0, 0]], ![![-9, -15, -1], ![27, 42, 0]]]
  g := ![![![1, 0, 0], ![-28, 83, 0], ![-9, 0, 83]], ![![0, 1, 0], ![-10, 29, 2], ![8, -29, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![47, 28, 1]] ![![83, 0, 0], ![28, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![2324, 83, 0]], ![![3901, 2324, 83], ![1411, 830, 83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![28, 1, 0]]], ![![![47, 28, 1]], ![![17, 10, 1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![55, -31, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![55, -31, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![55, 58, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![55, -31, 1], ![95, -5, -63], ![-3040, 961, 58]]]
  hmulB := by decide  
  f := ![![![-54, 31, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -58, 89]], ![![0, -1, 1], ![40, 41, -63], ![-70, -27, 58]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [71, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 88], [0, 1]]
 g := ![![[52, 84], [55], [81], [], [24, 69], [1]], ![[0, 5], [55], [81], [], [83, 20], [1]]]
 h' := ![![[46, 88], [10, 23], [34, 77], [0, 80], [76], [18, 46], [0, 1]], ![[0, 1], [0, 66], [16, 12], [31, 9], [76], [87, 43], [46, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [18, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [71, 43, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-731, 802, -290]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![171, 198, -290]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-26, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-26, 1, 0]] 
 ![![89, 0, 0], ![63, 1, 0], ![31, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-26, 1, 0], ![0, -25, 2], ![95, -29, -27]]]
  hmulB := by decide  
  f := ![![![1197, -46, 0], ![4094, 0, 0]], ![![859, -33, 0], ![2938, 0, 0]], ![![459, -5, -1], ![1570, 45, 0]]]
  g := ![![![1, 0, 0], ![-63, 89, 0], ![-31, 0, 89]], ![![-1, 1, 0], ![17, -25, 2], ![31, -29, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![55, -31, 1]] ![![89, 0, 0], ![-26, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-2314, 89, 0]], ![![4895, -2759, 89], ![-1335, 801, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-26, 1, 0]]], ![![![55, -31, 1]], ![![-15, 9, -1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![3, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![3, 1, 0]] 
 ![![97, 0, 0], ![3, 1, 0], ![91, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![3, 1, 0], ![0, 4, 2], ![95, -29, 2]]]
  hmulB := by decide  
  f := ![![![178, 59, 0], ![-5723, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![172, 55, -1], ![-5531, 49, 0]]]
  g := ![![![1, 0, 0], ![-3, 97, 0], ![-91, 0, 97]], ![![0, 1, 0], ![-2, 4, 2], ![0, -29, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![44, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![44, 1, 0]] 
 ![![97, 0, 0], ![44, 1, 0], ![77, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![44, 1, 0], ![0, 45, 2], ![95, -29, 43]]]
  hmulB := by decide  
  f := ![![![1673, 38, 0], ![-3686, 0, 0]], ![![748, 17, 0], ![-1648, 0, 0]], ![![1309, 7, -1], ![-2884, 49, 0]]]
  g := ![![![1, 0, 0], ![-44, 97, 0], ![-77, 0, 97]], ![![0, 1, 0], ![-22, 45, 2], ![-20, -29, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-47, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-47, 1, 0]] 
 ![![97, 0, 0], ![50, 1, 0], ![83, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-47, 1, 0], ![0, -46, 2], ![95, -29, -48]]]
  hmulB := by decide  
  f := ![![![3291, -70, 0], ![6790, 0, 0]], ![![1740, -37, 0], ![3590, 0, 0]], ![![2785, -36, -1], ![5746, 49, 0]]]
  g := ![![![1, 0, 0], ![-50, 97, 0], ![-83, 0, 97]], ![![-1, 1, 0], ![22, -46, 2], ![57, -29, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![3, 1, 0]] ![![97, 0, 0], ![44, 1, 0]]
  ![![97, 0, 0], ![66, 24, 1]] where
 M := ![![![9409, 0, 0], ![4268, 97, 0]], ![![291, 97, 0], ![132, 48, 2]]]
 hmul := by decide  
 g := ![![![![31, -24, -1], ![97, 0, 0]], ![![-22, -23, -1], ![97, 0, 0]]], ![![![-63, -23, -1], ![97, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![66, 24, 1]] ![![97, 0, 0], ![-47, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-4559, 97, 0]], ![![6402, 2328, 97], ![-3007, -1067, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-47, 1, 0]]], ![![![66, 24, 1]], ![![-31, -11, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![27, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![27, 1, 0]] 
 ![![101, 0, 0], ![27, 1, 0], ![26, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![27, 1, 0], ![0, 28, 2], ![95, -29, 26]]]
  hmulB := by decide  
  f := ![![![190, 7, 0], ![-707, 0, 0]], ![![54, 2, 0], ![-201, 0, 0]], ![![58, -12, -1], ![-216, 51, 0]]]
  g := ![![![1, 0, 0], ![-27, 101, 0], ![-26, 0, 101]], ![![0, 1, 0], ![-8, 28, 2], ![2, -29, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-15, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-15, 1, 0]] 
 ![![101, 0, 0], ![86, 1, 0], ![97, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-15, 1, 0], ![0, -14, 2], ![95, -29, -16]]]
  hmulB := by decide  
  f := ![![![616, -41, 0], ![4141, 0, 0]], ![![526, -35, 0], ![3536, 0, 0]], ![![602, -33, -1], ![4047, 51, 0]]]
  g := ![![![1, 0, 0], ![-86, 101, 0], ![-97, 0, 101]], ![![-1, 1, 0], ![10, -14, 2], ![41, -29, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-12, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-12, 1, 0]] 
 ![![101, 0, 0], ![89, 1, 0], ![35, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-12, 1, 0], ![0, -11, 2], ![95, -29, -13]]]
  hmulB := by decide  
  f := ![![![781, -65, 0], ![6565, 0, 0]], ![![673, -56, 0], ![5657, 0, 0]], ![![283, -18, -1], ![2379, 51, 0]]]
  g := ![![![1, 0, 0], ![-89, 101, 0], ![-35, 0, 101]], ![![-1, 1, 0], ![9, -11, 2], ![31, -29, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![27, 1, 0]] ![![101, 0, 0], ![-15, 1, 0]]
  ![![101, 0, 0], ![50, -44, 1]] where
 M := ![![![10201, 0, 0], ![-1515, 101, 0]], ![![2727, 101, 0], ![-405, 13, 2]]]
 hmul := by decide  
 g := ![![![![51, 44, -1], ![101, 0, 0]], ![![-15, 1, 0], ![0, 0, 0]]], ![![![-23, 45, -1], ![101, 0, 0]], ![![-5, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![50, -44, 1]] ![![101, 0, 0], ![-12, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-1212, 101, 0]], ![![5050, -4444, 101], ![-505, 505, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-12, 1, 0]]], ![![![50, -44, 1]], ![![-5, 5, -1]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-26, -35, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-26, -35, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![77, 68, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-26, -35, 1], ![95, -90, -71], ![-3420, 1077, -19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-77, -68, 103]], ![![-1, -1, 1], ![54, 46, -71], ![-19, 23, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [57, 90, 1] where
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
 g := ![![[7, 19], [67, 93], [18, 97], [63], [81], [13, 1]], ![[48, 84], [40, 10], [43, 6], [63], [81], [26, 102]]]
 h' := ![![[13, 102], [95, 15], [4, 89], [50, 71], [6, 75], [83, 9], [0, 1]], ![[0, 1], [84, 88], [28, 14], [46, 32], [54, 28], [97, 94], [13, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [12, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [57, 90, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1702, 62, 10]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24, -6, 10]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-32, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-32, 1, 0]] 
 ![![103, 0, 0], ![71, 1, 0], ![19, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-32, 1, 0], ![0, -31, 2], ![95, -29, -33]]]
  hmulB := by decide  
  f := ![![![1057, -33, 0], ![3399, 0, 0]], ![![769, -24, 0], ![2473, 0, 0]], ![![213, 9, -1], ![685, 52, 0]]]
  g := ![![![1, 0, 0], ![-71, 103, 0], ![-19, 0, 103]], ![![-1, 1, 0], ![21, -31, 2], ![27, -29, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-26, -35, 1]] ![![103, 0, 0], ![-32, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-3296, 103, 0]], ![![-2678, -3605, 103], ![927, 1030, -103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-32, 1, 0]]], ![![![-26, -35, 1]], ![![9, 10, -1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-5, -9, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-5, -9, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![102, 98, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-5, -9, 1], ![95, -43, -19], ![-950, 323, -24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-102, -98, 107]], ![![-1, -1, 1], ![19, 17, -19], ![14, 25, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [25, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 106], [0, 1]]
 g := ![![[89, 30], [25, 101], [100], [36, 14], [105], [22, 1]], ![[0, 77], [0, 6], [100], [23, 93], [105], [44, 106]]]
 h' := ![![[22, 106], [17, 43], [78, 84], [63, 97], [61, 96], [92, 31], [0, 1]], ![[0, 1], [0, 64], [0, 23], [57, 10], [33, 11], [25, 76], [22, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [53, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [25, 85, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-364, 800, -1147]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1090, 1058, -1147]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![19, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![19, 1, 0]] 
 ![![107, 0, 0], ![19, 1, 0], ![24, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![19, 1, 0], ![0, 20, 2], ![95, -29, 18]]]
  hmulB := by decide  
  f := ![![![799, 42, 0], ![-4494, 0, 0]], ![![133, 7, 0], ![-748, 0, 0]], ![![154, -2, -1], ![-866, 54, 0]]]
  g := ![![![1, 0, 0], ![-19, 107, 0], ![-24, 0, 107]], ![![0, 1, 0], ![-4, 20, 2], ![2, -29, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-5, -9, 1]] ![![107, 0, 0], ![19, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![2033, 107, 0]], ![![-535, -963, 107], ![0, -214, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![19, 1, 0]]], ![![![-5, -9, 1]], ![![0, -2, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-3, 21, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-3, 21, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![106, 21, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-3, 21, 1], ![95, -11, 41], ![1900, -547, -52]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-106, -21, 109]], ![![-1, 0, 1], ![-39, -8, 41], ![68, 5, -52]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [46, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 108], [0, 1]]
 g := ![![[5, 64], [3], [71, 87], [83, 78], [12], [97, 1]], ![[0, 45], [3], [8, 22], [19, 31], [12], [85, 108]]]
 h' := ![![[97, 108], [96, 8], [4, 60], [106, 14], [42, 29], [7, 98], [0, 1]], ![[0, 1], [0, 101], [47, 49], [47, 95], [21, 80], [30, 11], [97, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [33, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [46, 12, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![331, 190, -292]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![287, 58, -292]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-41, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-41, 1, 0]] 
 ![![109, 0, 0], ![68, 1, 0], ![52, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-41, 1, 0], ![0, -40, 2], ![95, -29, -42]]]
  hmulB := by decide  
  f := ![![![1067, -26, 0], ![2834, 0, 0]], ![![698, -17, 0], ![1854, 0, 0]], ![![582, 6, -1], ![1546, 55, 0]]]
  g := ![![![1, 0, 0], ![-68, 109, 0], ![-52, 0, 109]], ![![-1, 1, 0], ![24, -40, 2], ![39, -29, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-3, 21, 1]] ![![109, 0, 0], ![-41, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-4469, 109, 0]], ![![-327, 2289, 109], ![218, -872, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-41, 1, 0]]], ![![![-3, 21, 1]], ![![2, -8, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-13, 49, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-13, 49, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![100, 49, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-13, 49, 1], ![95, 7, 97], ![4560, -1359, -90]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-100, -49, 113]], ![![-1, 0, 1], ![-85, -42, 97], ![120, 27, -90]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [4, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [111, 112], [0, 1]]
 g := ![![[57, 85], [85], [85], [28], [], [111, 1]], ![[0, 28], [85], [85], [28], [], [109, 112]]]
 h' := ![![[111, 112], [112, 56], [0, 57], [1, 57], [0, 64], [8], [0, 1]], ![[0, 1], [0, 57], [112, 56], [0, 56], [98, 49], [8], [111, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [19, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [4, 2, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![37912, 3462, -12304]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11224, 5366, -12304]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![16, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![16, 1, 0]] 
 ![![113, 0, 0], ![16, 1, 0], ![90, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![16, 1, 0], ![0, 17, 2], ![95, -29, 15]]]
  hmulB := by decide  
  f := ![![![1601, 100, 0], ![-11300, 0, 0]], ![![208, 13, 0], ![-1468, 0, 0]], ![![1274, 71, -1], ![-8992, 57, 0]]]
  g := ![![![1, 0, 0], ![-16, 113, 0], ![-90, 0, 113]], ![![0, 1, 0], ![-4, 17, 2], ![-7, -29, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-13, 49, 1]] ![![113, 0, 0], ![16, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![1808, 113, 0]], ![![-1469, 5537, 113], ![-113, 791, 113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![16, 1, 0]]], ![![![-13, 49, 1]], ![![-1, 7, 1]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [119, 122, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 91, 35], [40, 35, 92], [0, 1]]
 g := ![![[51, 21, 81], [15, 86, 81], [102, 44, 4], [122, 101, 98], [10, 62, 44], [1]], ![[7, 3, 32, 122], [17, 117, 94, 13], [15, 113, 91, 1], [18, 34, 114, 107], [56, 126, 98, 30], [86, 7, 46, 76]], ![[50, 19, 112, 77], [63, 118, 94, 63], [95, 93, 27, 45], [54, 38, 37, 108], [4, 16, 89, 28], [78, 82, 89, 51]]]
 h' := ![![[27, 91, 35], [120, 123, 9], [54, 49, 9], [87, 71, 2], [80, 102, 15], [8, 5, 67], [0, 1]], ![[40, 35, 92], [102, 81, 48], [70, 78, 125], [119, 97, 15], [63, 33, 31], [51, 113, 107], [27, 91, 35]], ![[0, 1], [102, 50, 70], [124, 0, 120], [94, 86, 110], [121, 119, 81], [108, 9, 80], [40, 35, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 100], []]
 b := ![[], [80, 64, 106], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [119, 122, 60, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9271, -1016, -508]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![73, -8, -4]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![66, 30, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![66, 30, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![66, 30, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![66, 30, 1], ![95, 67, 59], ![2755, -808, 8]]]
  hmulB := by decide  
  f := ![![![-65, -30, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -30, 131]], ![![0, 0, 1], ![-29, -13, 59], ![17, -8, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [31, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 130], [0, 1]]
 g := ![![[50, 77], [37, 94], [25], [59], [27], [91], [1]], ![[41, 54], [9, 37], [25], [59], [27], [91], [1]]]
 h' := ![![[22, 130], [32, 48], [24, 15], [119, 126], [101, 37], [105, 114], [100, 22], [0, 1]], ![[0, 1], [40, 83], [92, 116], [9, 5], [129, 94], [124, 17], [60, 109], [22, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [43, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [31, 109, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![506, 1016, -167]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![88, 46, -167]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-59, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-59, 1, 0]] 
 ![![131, 0, 0], ![72, 1, 0], ![123, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-59, 1, 0], ![0, -58, 2], ![95, -29, -60]]]
  hmulB := by decide  
  f := ![![![3541, -60, 0], ![7860, 0, 0]], ![![1948, -33, 0], ![4324, 0, 0]], ![![3259, -26, -1], ![7234, 66, 0]]]
  g := ![![![1, 0, 0], ![-72, 131, 0], ![-123, 0, 131]], ![![-1, 1, 0], ![30, -58, 2], ![73, -29, -60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![66, 30, 1]] ![![131, 0, 0], ![-59, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-7729, 131, 0]], ![![8646, 3930, 131], ![-3799, -1703, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-59, 1, 0]]], ![![![66, 30, 1]], ![![-29, -13, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![37, 24, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![37, 24, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![37, 24, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![37, 24, 1], ![95, 32, 47], ![2185, -634, -15]]]
  hmulB := by decide  
  f := ![![![-36, -24, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -24, 137]], ![![0, 0, 1], ![-12, -8, 47], ![20, -2, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [87, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 136], [0, 1]]
 g := ![![[51, 63], [112], [34], [83, 87], [101], [69], [1]], ![[0, 74], [112], [34], [130, 50], [101], [69], [1]]]
 h' := ![![[84, 136], [127, 36], [12, 89], [40, 87], [37, 19], [59, 85], [50, 84], [0, 1]], ![[0, 1], [0, 101], [90, 48], [87, 50], [126, 118], [75, 52], [119, 53], [84, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [38, 110]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [87, 53, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5897, -944, -1318]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![399, 224, -1318]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-47, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-47, 1, 0]] 
 ![![137, 0, 0], ![90, 1, 0], ![15, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-47, 1, 0], ![0, -46, 2], ![95, -29, -48]]]
  hmulB := by decide  
  f := ![![![1740, -37, 0], ![5069, 0, 0]], ![![1176, -25, 0], ![3426, 0, 0]], ![![196, 19, -1], ![571, 69, 0]]]
  g := ![![![1, 0, 0], ![-90, 137, 0], ![-15, 0, 137]], ![![-1, 1, 0], ![30, -46, 2], ![25, -29, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![37, 24, 1]] ![![137, 0, 0], ![-47, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-6439, 137, 0]], ![![5069, 3288, 137], ![-1644, -1096, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-47, 1, 0]]], ![![![37, 24, 1]], ![![-12, -8, 0]]]]
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


lemma PB186I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB186I2 : PrimesBelowBoundCertificateInterval O 79 137 186 where
  m := 11
  g := ![2, 2, 3, 3, 2, 2, 2, 2, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB186I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
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
    · exact ![97, 97, 97]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
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
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
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
      exact NI113N1
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
  β := ![I83N1, I89N1, I97N0, I97N1, I97N2, I101N0, I101N1, I101N2, I103N1, I107N1, I109N1, I113N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [I97N0, I97N1, I97N2], [I101N0, I101N1, I101N2], [I103N1], [I107N1], [I109N1], [I113N1], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
