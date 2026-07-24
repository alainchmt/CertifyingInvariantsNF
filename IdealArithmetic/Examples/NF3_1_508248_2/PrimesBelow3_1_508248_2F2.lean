
import IdealArithmetic.Examples.NF3_1_508248_2.RI3_1_508248_2
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [81, 78, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 43, 5], [58, 39, 78], [0, 1]]
 g := ![![[33, 7, 4], [7, 39, 38], [70, 11], [26, 37], [26, 41, 1], []], ![[37, 39, 22, 76], [72, 63, 1, 45], [8, 61], [21, 36], [6, 10, 59, 52], [44, 25]], ![[15, 80, 61, 28], [24, 53, 22, 12], [8, 21], [62, 69], [45, 38, 48, 51], [54, 25]]]
 h' := ![![[66, 43, 5], [14, 60, 81], [14, 63, 11], [17, 8, 54], [52, 46, 28], [0, 0, 1], [0, 1]], ![[58, 39, 78], [66, 67, 56], [19, 55, 80], [70, 52, 71], [32, 59, 77], [45, 53, 39], [66, 43, 5]], ![[0, 1], [36, 39, 29], [28, 48, 75], [57, 23, 41], [4, 61, 61], [69, 30, 43], [58, 39, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 40], []]
 b := ![[], [10, 72, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [81, 78, 42, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-221776, -3486, -8715]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2672, -42, -105]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-31, 9, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-31, 9, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![58, 9, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-31, 9, 1], ![120, -9, 88], ![1186, 49, -44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -9, 89]], ![![-1, 0, 1], ![-56, -9, 88], ![42, 5, -44]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [32, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 88], [0, 1]]
 g := ![![[66, 64], [4], [87], [40, 4], [6, 42], [1]], ![[0, 25], [4], [87], [47, 85], [35, 47], [1]]]
 h' := ![![[24, 88], [14, 81], [63, 2], [55, 49], [75, 2], [57, 24], [0, 1]], ![[0, 1], [0, 8], [22, 87], [74, 40], [34, 87], [10, 65], [24, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [8, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [32, 65, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11130, 2548, 1806]
  a := ![-3, 0, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1302, -154, 1806]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![1, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![1, 1, 0]] 
 ![![89, 0, 0], ![1, 1, 0], ![44, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![1, 1, 0], ![-2, 3, 10], ![138, 4, -1]]]
  hmulB := by decide  
  f := ![![![-36, 53, 180], ![89, -1602, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-18, 26, 89], ![62, -792, 0]]]
  g := ![![![1, 0, 0], ![-1, 89, 0], ![-44, 0, 89]], ![![0, 1, 0], ![-5, 3, 10], ![2, 4, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-31, 9, 1]] ![![89, 0, 0], ![1, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![89, 89, 0]], ![![-2759, 801, 89], ![89, 0, 89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![1, 1, 0]]], ![![![-31, 9, 1]], ![![1, 0, 1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![125555, 16533, 11500]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![125555, 16533, 11500]] 
 ![![97, 0, 0], ![8, 1, 0], ![50, 0, 1]] where
  M :=![![![125555, 16533, 11500], ![1553934, 204621, 142330], ![1637554, 215632, 149989]]]
  hmulB := by decide  
  f := ![![![-3391, -137, 390]], ![![278, -33, 10]], ![![-2168, -24, 189]]]
  g := ![![![-5997, 16533, 11500], ![-74222, 204621, 142330], ![-78216, 215632, 149989]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![20, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![20, 1, 0]] 
 ![![97, 0, 0], ![20, 1, 0], ![14, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![20, 1, 0], ![-2, 22, 10], ![138, 4, 18]]]
  hmulB := by decide  
  f := ![![![-5543, 62089, 28220], ![-485, -273734, 0]], ![![-1142, 12783, 5810], ![-96, -56357, 0]], ![![-806, 8961, 4073], ![-41, -39508, 0]]]
  g := ![![![1, 0, 0], ![-20, 97, 0], ![-14, 0, 97]], ![![0, 1, 0], ![-6, 22, 10], ![-2, 4, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-28, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-28, 1, 0]] 
 ![![97, 0, 0], ![69, 1, 0], ![24, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-28, 1, 0], ![-2, -26, 10], ![138, 4, -30]]]
  hmulB := by decide  
  f := ![![![-4033, -54997, 21150], ![679, -205155, 0]], ![![-2867, -39109, 15040], ![486, -145888, 0]], ![![-984, -13608, 5233], ![216, -50760, 0]]]
  g := ![![![1, 0, 0], ![-69, 97, 0], ![-24, 0, 97]], ![![-1, 1, 0], ![16, -26, 10], ![6, 4, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![125555, 16533, 11500]] ![![97, 0, 0], ![20, 1, 0]]
  ![![97, 0, 0], ![-23, 3, 1]] where
 M := ![![![12178835, 1603701, 1115500], ![4065034, 535281, 372330]]]
 hmul := by decide  
 g := ![![![![119023, 17385, 11784], ![-27548, 0, 0]], ![![39733, 5802, 3933], ![-9171, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-23, 3, 1]] ![![97, 0, 0], ![-28, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-2716, 97, 0]], ![![-2231, 291, 97], ![776, -97, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-28, 1, 0]]], ![![![-23, 3, 1]], ![![8, -1, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [58, 37, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 76, 57], [8, 24, 44], [0, 1]]
 g := ![![[70, 58, 68], [98, 31], [7, 92, 33], [22, 6], [69, 43], [1]], ![[3, 82, 66, 73], [31, 88], [21, 92, 5, 74], [93, 21], [86, 22], [33, 12, 25, 60]], ![[46, 4, 78, 74], [38, 16], [33, 70, 26, 57], [12, 17], [99, 23], [94, 85, 25, 41]]]
 h' := ![![[81, 76, 57], [77, 88, 13], [99, 36, 43], [51, 92, 29], [69, 53, 39], [43, 64, 89], [0, 1]], ![[8, 24, 44], [100, 32, 76], [79, 11, 54], [83, 22, 82], [15, 18, 18], [85, 100, 27], [81, 76, 57]], ![[0, 1], [9, 82, 12], [71, 54, 4], [36, 88, 91], [96, 30, 44], [9, 38, 86], [8, 24, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 83], []]
 b := ![[], [16, 89, 96], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [58, 37, 12, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1210087262, -155733718, -127572696]
  a := ![1, -64, -69]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11981062, -1541918, -1263096]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![23, 15, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![23, 15, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![23, 15, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![23, 15, 1], ![108, 57, 148], ![2014, 73, -2]]]
  hmulB := by decide  
  f := ![![![-22, -15, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -15, 103]], ![![0, 0, 1], ![-32, -21, 148], ![20, 1, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [81, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 102], [0, 1]]
 g := ![![[0, 14], [0, 13], [], [], [72], [0, 1]], ![[0, 89], [0, 90], [], [], [72], [0, 102]]]
 h' := ![![[0, 102], [0, 80], [0, 61], [79], [39], [0, 22], [0, 1]], ![[0, 1], [0, 23], [0, 42], [79], [39], [0, 81], [0, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [0, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [81, 0, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7024, 2656, 850]
  a := ![3, -1, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-258, -98, 850]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-45, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-45, 1, 0]] 
 ![![103, 0, 0], ![58, 1, 0], ![2, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-45, 1, 0], ![-2, -43, 10], ![138, 4, -47]]]
  hmulB := by decide  
  f := ![![![2221, 51604, -12000], ![-412, 123600, 0]], ![![1261, 29027, -6750], ![-205, 69525, 0]], ![![44, 1002, -233], ![-6, 2400, 0]]]
  g := ![![![1, 0, 0], ![-58, 103, 0], ![-2, 0, 103]], ![![-1, 1, 0], ![24, -43, 10], ![0, 4, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![23, 15, 1]] ![![103, 0, 0], ![-45, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-4635, 103, 0]], ![![2369, 1545, 103], ![-927, -618, 103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-45, 1, 0]]], ![![![23, 15, 1]], ![![-9, -6, 1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-51, 37, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-51, 37, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![56, 37, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-51, 37, 1], ![64, 27, 368], ![5050, 161, -120]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -37, 107]], ![![-1, 0, 1], ![-192, -127, 368], ![110, 43, -120]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [83, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 106], [0, 1]]
 g := ![![[44, 49], [13, 85], [37], [30, 52], [36], [93, 1]], ![[0, 58], [0, 22], [37], [51, 55], [36], [79, 106]]]
 h' := ![![[93, 106], [98, 7], [17, 70], [78, 12], [19, 65], [92, 6], [0, 1]], ![[0, 1], [0, 100], [0, 37], [17, 95], [72, 42], [8, 101], [93, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85]]
 b := ![[], [30, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [83, 14, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1450, 381, 45]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, -12, 45]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-47, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-47, 1, 0]] 
 ![![107, 0, 0], ![60, 1, 0], ![13, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-47, 1, 0], ![-2, -45, 10], ![138, 4, -49]]]
  hmulB := by decide  
  f := ![![![-1923, -47524, 10560], ![428, -112992, 0]], ![![-1042, -26643, 5920], ![322, -63344, 0]], ![![-231, -5774, 1283], ![58, -13728, 0]]]
  g := ![![![1, 0, 0], ![-60, 107, 0], ![-13, 0, 107]], ![![-1, 1, 0], ![24, -45, 10], ![5, 4, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-51, 37, 1]] ![![107, 0, 0], ![-47, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-5029, 107, 0]], ![![-5457, 3959, 107], ![2461, -1712, 321]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-47, 1, 0]]], ![![![-51, 37, 1]], ![![23, -16, 3]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-37, 33, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-37, 33, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![72, 33, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-37, 33, 1], ![72, 33, 328], ![4498, 145, -98]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -33, 109]], ![![-1, 0, 1], ![-216, -99, 328], ![106, 31, -98]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [71, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 108], [0, 1]]
 g := ![![[88, 43], [21], [67, 97], [67, 49], [63], [74, 1]], ![[0, 66], [21], [51, 12], [96, 60], [63], [39, 108]]]
 h' := ![![[74, 108], [30, 32], [39, 28], [39, 36], [44, 102], [87, 64], [0, 1]], ![[0, 1], [0, 77], [40, 81], [87, 73], [71, 7], [27, 45], [74, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [69, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [71, 35, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![31915, 3051, 4284]
  a := ![-1, 21, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2537, -1269, 4284]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-1, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-1, 1, 0]] 
 ![![109, 0, 0], ![108, 1, 0], ![98, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-1, 1, 0], ![-2, 1, 10], ![138, 4, -3]]]
  hmulB := by decide  
  f := ![![![217, -108, -1080], ![0, 11772, 0]], ![![215, -107, -1070], ![1, 11663, 0]], ![![196, -98, -971], ![98, 10584, 0]]]
  g := ![![![1, 0, 0], ![-108, 109, 0], ![-98, 0, 109]], ![![-1, 1, 0], ![-10, 1, 10], ![0, 4, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-37, 33, 1]] ![![109, 0, 0], ![-1, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-109, 109, 0]], ![![-4033, 3597, 109], ![109, 0, 327]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-1, 1, 0]]], ![![![-37, 33, 1]], ![![1, 0, 3]]]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [2, 25, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 43, 68], [68, 69, 45], [0, 1]]
 g := ![![[3, 68, 41], [76, 111], [9, 81], [], [5, 75, 2], [1]], ![[96, 100, 39, 96], [2, 44], [67, 8], [76, 81], [3, 109, 9, 43], [112, 1, 106, 66]], ![[54, 23, 31, 70], [88, 32], [41, 4], [95, 81], [24, 57, 77, 48], [44, 105, 34, 47]]]
 h' := ![![[107, 43, 68], [49, 100, 43], [38, 56, 26], [100, 109, 104], [103, 68], [111, 88, 62], [0, 1]], ![[68, 69, 45], [91, 37, 49], [35, 59, 65], [100, 37, 11], [34, 99, 104], [12, 34, 92], [107, 43, 68]], ![[0, 1], [75, 89, 21], [5, 111, 22], [58, 80, 111], [94, 59, 9], [91, 104, 72], [68, 69, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 88], []]
 b := ![[], [75, 72, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [2, 25, 51, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-447141, -5876, 35256]
  a := ![1, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3957, -52, 312]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-31, 8, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-31, 8, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![96, 8, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-31, 8, 1], ![122, -11, 78], ![1048, 45, -42]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-96, -8, 127]], ![![-1, 0, 1], ![-58, -5, 78], ![40, 3, -42]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [89, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 126], [0, 1]]
 g := ![![[74, 121], [25, 37], [102, 124], [107, 1], [64, 107], [18, 1]], ![[93, 6], [56, 90], [48, 3], [125, 126], [85, 20], [36, 126]]]
 h' := ![![[18, 126], [61, 116], [66, 75], [2, 39], [19, 126], [49, 108], [0, 1]], ![[0, 1], [117, 11], [19, 52], [69, 88], [1, 1], [88, 19], [18, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [55, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [89, 109, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2537, 1873, 1520]
  a := ![-2, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1129, -81, 1520]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![49, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![49, 1, 0]] 
 ![![127, 0, 0], ![49, 1, 0], ![42, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![49, 1, 0], ![-2, 51, 10], ![138, 4, 47]]]
  hmulB := by decide  
  f := ![![![16374, -446273, -87500], ![2921, 1111250, 0]], ![![6309, -172134, -33750], ![1144, 428625, 0]], ![![5383, -147587, -28937], ![1049, 367500, 0]]]
  g := ![![![1, 0, 0], ![-49, 127, 0], ![-42, 0, 127]], ![![0, 1, 0], ![-23, 51, 10], ![-16, 4, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-31, 8, 1]] ![![127, 0, 0], ![49, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![6223, 127, 0]], ![![-3937, 1016, 127], ![-1397, 381, 127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![49, 1, 0]]], ![![![-31, 8, 1]], ![![-11, 3, 1]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![332535, 43788, 30458]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![332535, 43788, 30458]] 
 ![![131, 0, 0], ![0, 131, 0], ![114, 68, 1]] where
  M :=![![![332535, 43788, 30458], ![4115628, 541943, 376964], ![4337096, 571106, 397249]]]
  hmulB := by decide  
  f := ![![![-667, 56, -2]], ![![-388, -563, 564]], ![![-722, -242, 285]]]
  g := ![![![-23967, -15476, 30458], ![-296628, -191539, 376964], ![-312590, -201846, 397249]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [58, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 130], [0, 1]]
 g := ![![[129, 61], [84, 58], [74], [48], [39], [94], [1]], ![[0, 70], [0, 73], [74], [48], [39], [94], [1]]]
 h' := ![![[116, 130], [106, 42], [122, 78], [22, 27], [29, 110], [8, 68], [73, 116], [0, 1]], ![[0, 1], [0, 89], [0, 53], [10, 104], [82, 21], [36, 63], [36, 15], [116, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [77, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [58, 15, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5508, 500, 200]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-132, -100, 200]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-667, 56, -2]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-667, 56, -2]] 
 ![![131, 0, 0], ![108, 1, 0], ![17, 0, 1]] where
  M :=![![![-667, 56, -2], ![-388, -563, 564], ![7840, 198, -789]]]
  hmulB := by decide  
  f := ![![![332535, 43788, 30458]], ![![305568, 40237, 27988]], ![![76261, 10042, 6985]]]
  g := ![![![-51, 56, -2], ![388, -563, 564], ![-1, 198, -789]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![332535, 43788, 30458]] ![![-667, 56, -2]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [88, 31, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 21, 9], [24, 115, 128], [0, 1]]
 g := ![![[133, 37, 22], [111, 109], [113, 9], [58, 127, 99], [108, 14], [102, 1], []], ![[61, 118, 122, 128], [71, 78], [38, 99], [37, 88, 8, 38], [109, 130], [13, 73], [9, 81]], ![[66, 74, 98, 11], [20, 37], [117, 2], [108, 123, 25, 88], [8, 115], [106, 30], [27, 81]]]
 h' := ![![[78, 21, 9], [31, 136, 76], [49, 119, 66], [102, 117, 3], [58, 25, 28], [66, 38, 98], [0, 0, 1], [0, 1]], ![[24, 115, 128], [50, 27, 100], [74, 17, 30], [33, 65, 28], [32, 74, 20], [87, 110, 104], [86, 116, 115], [78, 21, 9]], ![[0, 1], [70, 111, 98], [7, 1, 41], [113, 92, 106], [126, 38, 89], [75, 126, 72], [118, 21, 21], [24, 115, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133, 60], []]
 b := ![[], [66, 61, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [88, 31, 35, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-582250, 438126, -314004]
  a := ![-2, -6, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4250, 3198, -2292]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB202I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB202I2 : PrimesBelowBoundCertificateInterval O 79 137 202 where
  m := 11
  g := ![1, 2, 3, 1, 2, 2, 2, 1, 2, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB202I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0]
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
    · exact ![97, 97, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![17161, 131]
    · exact ![2571353]
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
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
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
  β := ![I89N1, I97N0, I97N1, I97N2, I103N1, I107N1, I109N1, I127N1, I131N1]
  Il := ![[], [I89N1], [I97N0, I97N1, I97N2], [], [I103N1], [I107N1], [I109N1], [], [I127N1], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
