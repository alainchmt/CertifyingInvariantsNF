
import IdealArithmetic.Examples.NF3_1_271660_2.RI3_1_271660_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-57, -23, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-57, -23, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![17, 14, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-57, -23, 1], ![238, 11, -23], ![-5474, -1326, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -14, 37]], ![![-2, -1, 1], ![17, 9, -23], ![-153, -40, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [31, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 36], [0, 1]]
 g := ![![[], [1], [], [], [1]], ![[], [1], [], [], [1]]]
 h' := ![![[0, 36], [6], [0, 1], [36], [6], [0, 1]], ![[0, 1], [6], [0, 36], [36], [6], [0, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [0, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [31, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![507, 374, 69]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, -16, 69]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-14, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-14, 1, 0]] 
 ![![37, 0, 0], ![23, 1, 0], ![26, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-14, 1, 0], ![0, -14, 1], ![238, 68, -14]]]
  hmulB := by decide  
  f := ![![![197, -14, 0], ![518, 0, 0]], ![![127, -9, 0], ![334, 0, 0]], ![![146, -10, 0], ![384, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 37, 0], ![-26, 0, 37]], ![![-1, 1, 0], ![8, -14, 1], ![-26, 68, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-57, -23, 1]] ![![37, 0, 0], ![-14, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-518, 37, 0]], ![![-2109, -851, 37], ![1036, 333, -37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-14, 1, 0]]], ![![![-57, -23, 1]], ![![28, 9, -1]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-50, 10, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-50, 10, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![32, 10, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-50, 10, 1], ![238, 18, 10], ![2380, 918, 18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -10, 41]], ![![-2, 0, 1], ![-2, -2, 10], ![44, 18, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [26, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 40], [0, 1]]
 g := ![![[33, 36], [25], [32], [35, 9], [1]], ![[18, 5], [25], [32], [21, 32], [1]]]
 h' := ![![[3, 40], [4, 6], [11, 36], [33, 14], [15, 3], [0, 1]], ![[0, 1], [22, 35], [37, 5], [34, 27], [24, 38], [3, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [25, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [26, 38, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2867, 1254, 724]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-635, -146, 724]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-10, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-10, 1, 0]] 
 ![![41, 0, 0], ![31, 1, 0], ![23, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-10, 1, 0], ![0, -10, 1], ![238, 68, -10]]]
  hmulB := by decide  
  f := ![![![391, -39, 0], ![1599, 0, 0]], ![![301, -30, 0], ![1231, 0, 0]], ![![233, -23, 0], ![953, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 41, 0], ![-23, 0, 41]], ![![-1, 1, 0], ![7, -10, 1], ![-40, 68, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-50, 10, 1]] ![![41, 0, 0], ![-10, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-410, 41, 0]], ![![-2050, 410, 41], ![738, -82, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-10, 1, 0]]], ![![![-50, 10, 1]], ![![18, -2, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![19, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![19, 1, 0]] 
 ![![43, 0, 0], ![19, 1, 0], ![26, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![19, 1, 0], ![0, 19, 1], ![238, 68, 19]]]
  hmulB := by decide  
  f := ![![![267, 14, 0], ![-602, 0, 0]], ![![95, 5, 0], ![-214, 0, 0]], ![![142, 7, 0], ![-320, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 43, 0], ![-26, 0, 43]], ![![0, 1, 0], ![-9, 19, 1], ![-36, 68, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-13, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-13, 1, 0]] 
 ![![43, 0, 0], ![30, 1, 0], ![3, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-13, 1, 0], ![0, -13, 1], ![238, 68, -13]]]
  hmulB := by decide  
  f := ![![![209, -16, 0], ![688, 0, 0]], ![![144, -11, 0], ![474, 0, 0]], ![![17, -1, 0], ![56, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 43, 0], ![-3, 0, 43]], ![![-1, 1, 0], ![9, -13, 1], ![-41, 68, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1073, -33, 15]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-1073, -33, 15]] 
 ![![43, 0, 0], ![37, 1, 0], ![7, 0, 1]] where
  M :=![![![-1073, -33, 15], ![3570, -53, -33], ![-7854, 1326, -53]]]
  hmulB := by decide  
  f := ![![![46567, 18141, 1884]], ![![50497, 19672, 2043]], ![![107989, 42069, 4369]]]
  g := ![![![1, -33, 15], ![134, -53, -33], ![-1315, 1326, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![19, 1, 0]] ![![43, 0, 0], ![-13, 1, 0]]
  ![![-46567, -18141, -1884]] where
 M := ![![![1849, 0, 0], ![-559, 43, 0]], ![![817, 43, 0], ![-247, 6, 1]]]
 hmul := by decide  
 g := ![![![![46139, 1419, -645]], ![![-17519, -376, 228]]], ![![![16817, 680, -252]], ![![-6479, -213, 92]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-46567, -18141, -1884]] ![![-1073, -33, 15]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1959, 278, -50]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![1959, 278, -50]] 
 ![![47, 0, 0], ![13, 1, 0], ![19, 0, 1]] where
  M :=![![![1959, 278, -50], ![-11900, -1441, 278], ![66164, 7004, -1441]]]
  hmulB := by decide  
  f := ![![![129369, 50398, 5234]], ![![62287, 24265, 2520]], ![![307505, 119794, 12441]]]
  g := ![![![-15, 278, -50], ![33, -1441, 278], ![53, 7004, -1441]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![123, 48, 5]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![123, 48, 5]] 
 ![![47, 0, 0], ![17, 1, 0], ![40, 0, 1]] where
  M :=![![![123, 48, 5], ![1190, 463, 48], ![11424, 4454, 463]]]
  hmulB := by decide  
  f := ![![![577, 46, -11]], ![![153, 13, -3]], ![![724, 50, -13]]]
  g := ![![![-19, 48, 5], ![-183, 463, 48], ![-1762, 4454, 463]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![1959, 278, -50]] ![![123, 48, 5]]
  ![![577, 46, -11]] where
 M := ![![![577, 46, -11]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![577, 46, -11]] ![![123, 48, 5]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-19, 7, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-19, 7, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![34, 7, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-19, 7, 1], ![238, 49, 7], ![1666, 714, 49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -7, 53]], ![![-1, 0, 1], ![0, 0, 7], ![0, 7, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [39, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 52], [0, 1]]
 g := ![![[22, 15], [37], [3, 6], [11], [43, 1]], ![[31, 38], [37], [49, 47], [11], [33, 52]]]
 h' := ![![[43, 52], [3, 11], [42, 14], [38, 35], [19, 8], [0, 1]], ![[0, 1], [52, 42], [8, 39], [6, 18], [45, 45], [43, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [21, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [39, 10, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3019, -16, 187]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-63, -25, 187]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-7, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-7, 1, 0]] 
 ![![53, 0, 0], ![46, 1, 0], ![4, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-7, 1, 0], ![0, -7, 1], ![238, 68, -7]]]
  hmulB := by decide  
  f := ![![![295, -42, 0], ![2226, 0, 0]], ![![260, -37, 0], ![1962, 0, 0]], ![![22, -3, 0], ![166, 1, 0]]]
  g := ![![![1, 0, 0], ![-46, 53, 0], ![-4, 0, 53]], ![![-1, 1, 0], ![6, -7, 1], ![-54, 68, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-19, 7, 1]] ![![53, 0, 0], ![-7, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-371, 53, 0]], ![![-1007, 371, 53], ![371, 0, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-7, 1, 0]]], ![![![-19, 7, 1]], ![![7, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [55, 43, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 4, 6], [31, 54, 53], [0, 1]]
 g := ![![[9, 35, 17], [22, 8, 5], [40, 36], [54, 1, 5], [1]], ![[26, 26, 18, 54], [7, 38, 55, 58], [14, 57], [54, 20, 57, 54], [15, 14, 36, 39]], ![[29, 35, 16, 16], [38, 51, 48, 7], [28, 15], [22, 13, 39, 27], [53, 1, 33, 20]]]
 h' := ![![[36, 4, 6], [29, 45, 31], [29, 57, 8], [39, 58, 6], [4, 16, 8], [0, 1]], ![[31, 54, 53], [4, 42, 56], [14, 23, 7], [31, 34, 23], [47, 36, 56], [36, 4, 6]], ![[0, 1], [27, 31, 31], [29, 38, 44], [25, 26, 30], [31, 7, 54], [31, 54, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 1], []]
 b := ![[], [57, 2, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [55, 43, 51, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1169144, -657378, -86376]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19816, -11142, -1464]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![3, 1, 0]] 
 ![![61, 0, 0], ![3, 1, 0], ![52, 0, 1]] where
  M :=![![![3, 1, 0], ![0, 3, 1], ![238, 68, 3]]]
  hmulB := by decide  
  f := ![![![-59, -3, 1]], ![![1, 0, 0]], ![![-62, -2, 1]]]
  g := ![![![0, 1, 0], ![-1, 3, 1], ![-2, 68, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-2, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-2, 1, 0]] 
 ![![61, 0, 0], ![59, 1, 0], ![57, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-2, 1, 0], ![0, -2, 1], ![238, 68, -2]]]
  hmulB := by decide  
  f := ![![![67, -33, 0], ![2013, 0, 0]], ![![65, -32, 0], ![1953, 0, 0]], ![![63, -31, 0], ![1893, 1, 0]]]
  g := ![![![1, 0, 0], ![-59, 61, 0], ![-57, 0, 61]], ![![-1, 1, 0], ![1, -2, 1], ![-60, 68, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-1, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-1, 1, 0]] 
 ![![61, 0, 0], ![60, 1, 0], ![60, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-1, 1, 0], ![0, -1, 1], ![238, 68, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![183, 0, 0]], ![![2, -1, 0], ![62, 0, 0]], ![![2, -1, 0], ![62, 1, 0]]]
  g := ![![![1, 0, 0], ![-60, 61, 0], ![-60, 0, 61]], ![![-1, 1, 0], ![0, -1, 1], ![-62, 68, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![3, 1, 0]] ![![61, 0, 0], ![-2, 1, 0]]
  ![![61, 0, 0], ![-67, 1, 1]] where
 M := ![![![183, 61, 0], ![-6, 1, 1]]]
 hmul := by decide  
 g := ![![![![3, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-67, 1, 1]] ![![61, 0, 0], ![-1, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-61, 61, 0]], ![![-4087, 61, 61], ![305, 0, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-1, 1, 0]]], ![![![-67, 1, 1]], ![![5, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [29, 23, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 63, 42], [61, 3, 25], [0, 1]]
 g := ![![[53, 56, 19], [16, 38, 17], [24, 15], [39, 26], [65, 1], []], ![[8, 22, 36, 58], [29, 8, 25, 41], [25, 62], [36, 35], [28, 9], [22, 22]], ![[43, 30, 62, 60], [48, 31, 8, 10], [47, 23], [42, 19], [7, 16], [39, 22]]]
 h' := ![![[4, 63, 42], [5, 58, 32], [56, 5, 34], [22, 53, 22], [58, 17, 48], [0, 0, 1], [0, 1]], ![[61, 3, 25], [31, 58, 53], [33, 62, 44], [17, 46, 14], [18, 32, 54], [48, 30, 3], [4, 63, 42]], ![[0, 1], [60, 18, 49], [48, 0, 56], [2, 35, 31], [58, 18, 32], [44, 37, 63], [61, 3, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 30], []]
 b := ![[], [63, 30, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [29, 23, 2, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-104453, -46297, -5427]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1559, -691, -81]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![9, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![9, 1, 0]] 
 ![![71, 0, 0], ![9, 1, 0], ![61, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![9, 1, 0], ![0, 9, 1], ![238, 68, 9]]]
  hmulB := by decide  
  f := ![![![55, 6, 0], ![-426, 0, 0]], ![![-9, -1, 0], ![72, 0, 0]], ![![47, 5, 0], ![-364, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 71, 0], ![-61, 0, 71]], ![![0, 1, 0], ![-2, 9, 1], ![-13, 68, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![75, 29, 3]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![75, 29, 3]] 
 ![![71, 0, 0], ![26, 1, 0], ![34, 0, 1]] where
  M :=![![![75, 29, 3], ![714, 279, 29], ![6902, 2686, 279]]]
  hmulB := by decide  
  f := ![![![-53, -33, 4]], ![![-6, -9, 1]], ![![-136, -34, 5]]]
  g := ![![![-11, 29, 3], ![-106, 279, 29], ![-1020, 2686, 279]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-35, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-35, 1, 0]] 
 ![![71, 0, 0], ![36, 1, 0], ![53, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-35, 1, 0], ![0, -35, 1], ![238, 68, -35]]]
  hmulB := by decide  
  f := ![![![2486, -71, 0], ![5041, 0, 0]], ![![1296, -37, 0], ![2628, 0, 0]], ![![1908, -54, 0], ![3869, 1, 0]]]
  g := ![![![1, 0, 0], ![-36, 71, 0], ![-53, 0, 71]], ![![-1, 1, 0], ![17, -35, 1], ![-5, 68, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![9, 1, 0]] ![![75, 29, 3]]
  ![![71, 0, 0], ![-50, -36, 1]] where
 M := ![![![5325, 2059, 213]], ![![1389, 540, 56]]]
 hmul := by decide  
 g := ![![![![75, 29, 3], ![0, 0, 0]]], ![![![59, 36, 0], ![56, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-50, -36, 1]] ![![71, 0, 0], ![-35, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2485, 71, 0]], ![![-3550, -2556, 71], ![1988, 1278, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-35, 1, 0]]], ![![![-50, -36, 1]], ![![28, 18, -1]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![34, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![34, 1, 0]] 
 ![![73, 0, 0], ![34, 1, 0], ![12, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![34, 1, 0], ![0, 34, 1], ![238, 68, 34]]]
  hmulB := by decide  
  f := ![![![749, 22, 0], ![-1606, 0, 0]], ![![306, 9, 0], ![-656, 0, 0]], ![![84, 2, 0], ![-180, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 73, 0], ![-12, 0, 73]], ![![0, 1, 0], ![-16, 34, 1], ![-34, 68, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![589441929, 229627446, 23847559]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![589441929, 229627446, 23847559]] 
 ![![73, 0, 0], ![54, 1, 0], ![4, 0, 1]] where
  M :=![![![589441929, 229627446, 23847559], ![5675719042, 2211075941, 229627446], ![54651332148, 21290385370, 2211075941]]]
  hmulB := by decide  
  f := ![![![170461, -64856, 4897]], ![![142060, -41079, 2734]], ![![-202108, -48002, 7165]]]
  g := ![![![-163093567, 229627446, 23847559], ![-1570423172, 2211075941, 229627446], ![-15121558652, 21290385370, 2211075941]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-15, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-15, 1, 0]] 
 ![![73, 0, 0], ![58, 1, 0], ![67, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-15, 1, 0], ![0, -15, 1], ![238, 68, -15]]]
  hmulB := by decide  
  f := ![![![706, -47, 0], ![3431, 0, 0]], ![![556, -37, 0], ![2702, 0, 0]], ![![664, -44, 0], ![3227, 1, 0]]]
  g := ![![![1, 0, 0], ![-58, 73, 0], ![-67, 0, 73]], ![![-1, 1, 0], ![11, -15, 1], ![-37, 68, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![34, 1, 0]] ![![589441929, 229627446, 23847559]]
  ![![73, 0, 0], ![-62, 15, 1]] where
 M := ![![![43029260817, 16762803558, 1740871807]], ![![25716744628, 10018409105, 1040444452]]]
 hmul := by decide  
 g := ![![![![371250351, 282415731, 27366778], ![-256902987, 0, 0]]], ![![![221880424, 168787775, 16355950], ![-153539898, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-62, 15, 1]] ![![73, 0, 0], ![-15, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1095, 73, 0]], ![![-4526, 1095, 73], ![1168, -219, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-15, 1, 0]]], ![![![-62, 15, 1]], ![![16, -3, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [56, 44, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 21, 7], [70, 57, 72], [0, 1]]
 g := ![![[3, 37, 19], [46, 56, 52], [47, 58, 11], [2, 40, 1], [60, 1], []], ![[67, 61, 46, 69], [10, 56, 7, 74], [67, 69, 10, 58], [50, 25, 46, 77], [23, 10], [74, 49]], ![[44, 9, 57, 52], [33, 44, 20, 51], [59, 27, 17, 45], [68, 55, 65, 19], [8, 46], [9, 49]]]
 h' := ![![[69, 21, 7], [31, 47, 16], [54, 39, 62], [46, 68, 13], [37, 69, 1], [0, 0, 1], [0, 1]], ![[70, 57, 72], [32, 19, 56], [77, 70, 15], [40, 49, 32], [43, 6, 66], [64, 58, 57], [69, 21, 7]], ![[0, 1], [29, 13, 7], [21, 49, 2], [18, 41, 34], [20, 4, 12], [51, 21, 21], [70, 57, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 9], []]
 b := ![[], [41, 5, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [56, 44, 19, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2810662, 1083801, 101357]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![35578, 13719, 1283]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB148I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB148I1 : PrimesBelowBoundCertificateInterval O 31 79 148 where
  m := 11
  g := ![2, 2, 3, 3, 2, 1, 3, 1, 3, 3, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB148I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![61, 61, 61]
    · exact ![300763]
    · exact ![71, 71, 71]
    · exact ![73, 73, 73]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N1, I43N0, I43N1, I43N2, I47N0, I47N1, I53N1, I61N0, I61N1, I61N2, I71N0, I71N1, I71N2, I73N0, I73N1, I73N2]
  Il := ![[I37N1], [I41N1], [I43N0, I43N1, I43N2], [I47N0, I47N1, I47N1], [I53N1], [], [I61N0, I61N1, I61N2], [], [I71N0, I71N1, I71N2], [I73N0, I73N1, I73N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
