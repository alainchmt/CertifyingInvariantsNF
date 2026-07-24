
import IdealArithmetic.Examples.NF3_1_226175_1.RI3_1_226175_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![4, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![4, 1, 0]] 
 ![![83, 0, 0], ![4, 1, 0], ![67, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![4, 1, 0], ![0, 4, 1], ![45, -35, 4]]]
  hmulB := by decide  
  f := ![![![77, 19, 0], ![-1577, 0, 0]], ![![-4, -1, 0], ![84, 0, 0]], ![![61, 15, 0], ![-1249, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 83, 0], ![-67, 0, 83]], ![![0, 1, 0], ![-1, 4, 1], ![-1, -35, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-182, 144, 3]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-182, 144, 3]] 
 ![![83, 0, 0], ![75, 1, 0], ![19, 0, 1]] where
  M :=![![![-182, 144, 3], ![135, -287, 144], ![6480, -4905, -287]]]
  hmulB := by decide  
  f := ![![![-788689, -26613, -21597]], ![![-724380, -24443, -19836]], ![![-194972, -6579, -5339]]]
  g := ![![![-133, 144, 3], ![228, -287, 144], ![4576, -4905, -287]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![4, 1, 0]] ![![83, 0, 0], ![4, 1, 0]]
  ![![788689, 26613, 21597]] where
 M := ![![![6889, 0, 0], ![332, 83, 0]], ![![332, 83, 0], ![16, 8, 1]]]
 hmul := by decide  
 g := ![![![![15106, -11952, -249]], ![![593, -289, -156]]], ![![![593, -289, -156]], ![![-56, 59, -11]]]]
 hle2 := by decide  
def MulI83N1 : IdealMulLeCertificate' Table 
  ![![788689, 26613, 21597]] ![![-182, 144, 3]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![14, 35, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![14, 35, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![14, 35, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![14, 35, 1], ![45, -21, 35], ![1575, -1180, -21]]]
  hmulB := by decide  
  f := ![![![-13, -35, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -35, 89]], ![![0, 0, 1], ![-5, -14, 35], ![21, -5, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [76, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 88], [0, 1]]
 g := ![![[27, 11], [22], [64], [57, 32], [12, 25], [1]], ![[61, 78], [22], [64], [75, 57], [65, 64], [1]]]
 h' := ![![[84, 88], [76, 79], [71, 17], [29, 81], [67, 78], [13, 84], [0, 1]], ![[0, 1], [37, 10], [75, 72], [69, 8], [33, 11], [38, 5], [84, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [82, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [76, 5, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![166, -30, -39]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, 15, -39]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-35, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-35, 1, 0]] 
 ![![89, 0, 0], ![54, 1, 0], ![21, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-35, 1, 0], ![0, -35, 1], ![45, -35, -35]]]
  hmulB := by decide  
  f := ![![![1471, -42, 0], ![3738, 0, 0]], ![![876, -25, 0], ![2226, 0, 0]], ![![399, -11, 0], ![1014, 1, 0]]]
  g := ![![![1, 0, 0], ![-54, 89, 0], ![-21, 0, 89]], ![![-1, 1, 0], ![21, -35, 1], ![30, -35, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![14, 35, 1]] ![![89, 0, 0], ![-35, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-3115, 89, 0]], ![![1246, 3115, 89], ![-445, -1246, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-35, 1, 0]]], ![![![14, 35, 1]], ![![-5, -14, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-152209, -5136, -4168]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-152209, -5136, -4168]] 
 ![![97, 0, 0], ![0, 97, 0], ![27, 34, 1]] where
  M :=![![![-152209, -5136, -4168], ![-187560, -6329, -5136], ![-231120, -7800, -6329]]]
  hmulB := by decide  
  f := ![![![47, -48, 8]], ![![360, -233, -48]], ![![117, -74, -17]]]
  g := ![![![-409, 1408, -4168], ![-504, 1735, -5136], ![-621, 2138, -6329]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [74, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 96], [0, 1]]
 g := ![![[96, 79], [73], [33], [33], [27], [74, 1]], ![[25, 18], [73], [33], [33], [27], [51, 96]]]
 h' := ![![[74, 96], [83, 46], [76, 49], [44, 18], [35, 79], [53, 67], [0, 1]], ![[0, 1], [92, 51], [16, 48], [18, 79], [61, 18], [64, 30], [74, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [79, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [74, 23, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-488, 783, -248]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![64, 95, -248]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, -48, 8]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![47, -48, 8]] 
 ![![97, 0, 0], ![63, 1, 0], ![8, 0, 1]] where
  M :=![![![47, -48, 8], ![360, -233, -48], ![-2160, 2040, -233]]]
  hmulB := by decide  
  f := ![![![-152209, -5136, -4168]], ![![-100791, -3401, -2760]], ![![-14936, -504, -409]]]
  g := ![![![31, -48, 8], ![159, -233, -48], ![-1328, 2040, -233]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-152209, -5136, -4168]] ![![47, -48, 8]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [65, 77, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 79, 33], [65, 21, 68], [0, 1]]
 g := ![![[93, 23, 80], [79, 22], [80, 38, 45], [22, 45], [33, 37], [1]], ![[100, 77, 68, 95], [13, 87], [32, 4, 95, 71], [36, 76], [60, 82], [73, 24, 33, 82]], ![[68, 46, 42, 5], [61, 100], [91, 86, 11, 19], [1, 87], [31, 22], [24, 92, 33, 19]]]
 h' := ![![[15, 79, 33], [94, 60, 79], [52, 33, 74], [49, 91, 67], [60, 14, 67], [36, 24, 80], [0, 1]], ![[65, 21, 68], [0, 66, 3], [80, 66, 17], [89, 39, 67], [56, 16, 51], [44, 88, 48], [15, 79, 33]], ![[0, 1], [88, 76, 19], [66, 2, 10], [56, 72, 68], [11, 71, 84], [62, 90, 74], [65, 21, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 54], []]
 b := ![[], [61, 64, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [65, 77, 21, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-172306, -3333, -4848]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1706, -33, -48]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [42, 43, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 9, 37], [50, 93, 66], [0, 1]]
 g := ![![[28, 77, 36], [12, 82, 16], [101, 63, 98], [67, 52], [50, 49], [1]], ![[77, 27, 7, 90], [39, 76, 65, 6], [21, 45, 25, 101], [49, 36], [23, 66], [40, 44, 31, 80]], ![[85, 17, 31, 83], [42, 97, 31, 91], [84, 98, 47, 36], [80, 7], [90, 36], [80, 10, 85, 23]]]
 h' := ![![[60, 9, 37], [11, 6, 97], [84, 22, 4], [78, 30, 60], [76, 22, 19], [61, 60, 7], [0, 1]], ![[50, 93, 66], [12, 27, 76], [64, 10, 53], [9, 25, 98], [78, 26, 6], [80, 5, 90], [60, 9, 37]], ![[0, 1], [68, 70, 33], [7, 71, 46], [94, 48, 48], [40, 55, 78], [100, 38, 6], [50, 93, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 66], []]
 b := ![[], [80, 54, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [42, 43, 96, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-123703, 178808, -63345]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1201, 1736, -615]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![130663, 4409, 3578]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![130663, 4409, 3578]] 
 ![![107, 0, 0], ![50, 1, 0], ![68, 0, 1]] where
  M :=![![![130663, 4409, 3578], ![161010, 5433, 4409], ![198405, 6695, 5433]]]
  hmulB := by decide  
  f := ![![![-766, 613, 7]], ![![-355, 277, 9]], ![![-229, 192, -5]]]
  g := ![![![-3113, 4409, 3578], ![-3836, 5433, 4409], ![-4727, 6695, 5433]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-29, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-29, 1, 0]] 
 ![![107, 0, 0], ![78, 1, 0], ![15, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-29, 1, 0], ![0, -29, 1], ![45, -35, -29]]]
  hmulB := by decide  
  f := ![![![1799, -62, 0], ![6634, 0, 0]], ![![1306, -45, 0], ![4816, 0, 0]], ![![269, -9, 0], ![992, 1, 0]]]
  g := ![![![1, 0, 0], ![-78, 107, 0], ![-15, 0, 107]], ![![-1, 1, 0], ![21, -29, 1], ![30, -35, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-21, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-21, 1, 0]] 
 ![![107, 0, 0], ![86, 1, 0], ![94, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-21, 1, 0], ![0, -21, 1], ![45, -35, -21]]]
  hmulB := by decide  
  f := ![![![1324, -63, 0], ![6741, 0, 0]], ![![1072, -51, 0], ![5458, 0, 0]], ![![1160, -55, 0], ![5906, 1, 0]]]
  g := ![![![1, 0, 0], ![-86, 107, 0], ![-94, 0, 107]], ![![-1, 1, 0], ![16, -21, 1], ![47, -35, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![130663, 4409, 3578]] ![![107, 0, 0], ![-29, 1, 0]]
  ![![107, 0, 0], ![48, 21, 1]] where
 M := ![![![13980941, 471763, 382846], ![-3628217, -122428, -99353]]]
 hmul := by decide  
 g := ![![![![109111, -5020, 3129], ![48043, 0, 0]], ![![-28363, 1282, -813], ![-12362, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![48, 21, 1]] ![![107, 0, 0], ![-21, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-2247, 107, 0]], ![![5136, 2247, 107], ![-963, -428, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-21, 1, 0]]], ![![![48, 21, 1]], ![![-9, -4, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, -3, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![4, -3, 0]] 
 ![![109, 0, 0], ![35, 1, 0], ![83, 0, 1]] where
  M :=![![![4, -3, 0], ![0, 4, -3], ![-135, 105, 4]]]
  hmulB := by decide  
  f := ![![![331, 12, 9]], ![![110, 4, 3]], ![![257, 9, 7]]]
  g := ![![![1, -3, 0], ![1, 4, -3], ![-38, 105, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![37, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![37, 1, 0]] 
 ![![109, 0, 0], ![37, 1, 0], ![48, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![37, 1, 0], ![0, 37, 1], ![45, -35, 37]]]
  hmulB := by decide  
  f := ![![![1407, 38, 0], ![-4142, 0, 0]], ![![481, 13, 0], ![-1416, 0, 0]], ![![568, 15, 0], ![-1672, 1, 0]]]
  g := ![![![1, 0, 0], ![-37, 109, 0], ![-48, 0, 109]], ![![0, 1, 0], ![-13, 37, 1], ![-4, -35, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![4, -3, 0]] ![![109, 0, 0], ![37, 1, 0]]
  ![![109, 0, 0], ![-13, -37, 1]] where
 M := ![![![436, -327, 0], ![148, -107, -3]]]
 hmul := by decide  
 g := ![![![![17, 34, -1], ![109, 0, 0]], ![![14, 35, -1], ![106, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-13, -37, 1]] ![![109, 0, 0], ![37, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![4033, 109, 0]], ![![-1417, -4033, 109], ![-436, -1417, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![37, 1, 0]]], ![![![-13, -37, 1]], ![![-4, -13, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N1
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [29, 108, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 92, 103], [27, 20, 10], [0, 1]]
 g := ![![[18, 80, 28], [101, 97], [72, 91], [59, 41], [69, 67, 41], [1]], ![[90, 13, 111, 70], [59, 97], [70, 100], [96, 41], [92, 88, 40, 92], [23, 39, 88, 17]], ![[36, 4, 27, 78], [], [6, 28], [], [81, 43, 69, 54], [69, 87, 64, 96]]]
 h' := ![![[43, 92, 103], [66, 50, 49], [31, 100, 53], [56, 107, 54], [33, 34, 70], [84, 5, 70], [0, 1]], ![[27, 20, 10], [28, 75, 28], [48, 7, 60], [48, 49, 10], [32, 86, 43], [79, 17, 107], [43, 92, 103]], ![[0, 1], [1, 101, 36], [112, 6], [25, 70, 49], [108, 106], [54, 91, 49], [27, 20, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 43], []]
 b := ![[], [83, 105, 106], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [29, 108, 43, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6554, -1808, -2825]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![58, -16, -25]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![71, 6, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![71, 6, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![71, 6, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![71, 6, 1], ![45, 36, 6], ![270, -165, 36]]]
  hmulB := by decide  
  f := ![![![-70, -6, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -6, 127]], ![![0, 0, 1], ![-3, 0, 6], ![-18, -3, 36]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [7, 91, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 126], [0, 1]]
 g := ![![[13, 107], [13, 9], [44, 38], [85, 15], [118, 107], [36, 1]], ![[55, 20], [83, 118], [15, 89], [117, 112], [33, 20], [72, 126]]]
 h' := ![![[36, 126], [36, 19], [73, 124], [40, 66], [63, 74], [2, 19], [0, 1]], ![[0, 1], [85, 108], [92, 3], [3, 61], [60, 53], [51, 108], [36, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [109, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [7, 91, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1809, 482, 419]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-220, -16, 419]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-6, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-6, 1, 0]] 
 ![![127, 0, 0], ![121, 1, 0], ![91, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-6, 1, 0], ![0, -6, 1], ![45, -35, -6]]]
  hmulB := by decide  
  f := ![![![649, -108, 0], ![13716, 0, 0]], ![![619, -103, 0], ![13082, 0, 0]], ![![469, -78, 0], ![9912, 1, 0]]]
  g := ![![![1, 0, 0], ![-121, 127, 0], ![-91, 0, 127]], ![![-1, 1, 0], ![5, -6, 1], ![38, -35, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![71, 6, 1]] ![![127, 0, 0], ![-6, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-762, 127, 0]], ![![9017, 762, 127], ![-381, 0, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-6, 1, 0]]], ![![![71, 6, 1]], ![![-3, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [57, 105, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [127, 90, 37], [71, 40, 94], [0, 1]]
 g := ![![[92, 95, 65], [32, 76, 89], [], [35, 11], [45, 53], [67, 1], []], ![[106, 15, 102, 73], [130, 28, 96, 19], [116, 16], [117, 5], [112, 63], [84, 28], [2, 59]], ![[65, 42, 17, 1], [111, 33, 46, 16], [85, 16], [94, 74], [58, 1], [69, 109], [76, 59]]]
 h' := ![![[127, 90, 37], [10, 96, 117], [94, 113, 58], [15, 78], [62, 48, 50], [111, 113, 61], [0, 0, 1], [0, 1]], ![[71, 40, 94], [81, 98, 110], [115, 120, 82], [96, 77, 4], [79, 56, 108], [100, 79, 71], [33, 30, 40], [127, 90, 37]], ![[0, 1], [44, 68, 35], [114, 29, 122], [51, 107, 127], [13, 27, 104], [31, 70, 130], [54, 101, 90], [71, 40, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 83], []]
 b := ![[], [111, 5, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [57, 105, 64, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31440, 27510, -1441]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-240, 210, -11]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀



lemma PB135I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 134 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 134 (by omega)

def PB135I2 : PrimesBelowBoundCertificateInterval O 79 134 135 where
  m := 10
  g := ![3, 2, 2, 1, 1, 3, 3, 1, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131]
  hP := PB135I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![83, 83, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![109, 109, 109]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![2248091]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
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
  β := ![I83N0, I83N1, I89N1, I97N1, I107N0, I107N1, I107N2, I109N0, I109N1, I127N1]
  Il := ![[I83N0, I83N0, I83N1], [I89N1], [I97N1], [], [], [I107N0, I107N1, I107N2], [I109N0, I109N1, I109N1], [], [I127N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
