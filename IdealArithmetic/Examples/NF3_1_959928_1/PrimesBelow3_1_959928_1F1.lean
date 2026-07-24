
import IdealArithmetic.Examples.NF3_1_959928_1.RI3_1_959928_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![11, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![11, 1, 0]] 
 ![![37, 0, 0], ![11, 1, 0], ![8, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![11, 1, 0], ![0, 12, 2], ![246, 48, 11]]]
  hmulB := by decide  
  f := ![![![122, 11, 0], ![-407, 0, 0]], ![![22, 2, 0], ![-73, 0, 0]], ![![24, -4, -1], ![-80, 19, 0]]]
  g := ![![![1, 0, 0], ![-11, 37, 0], ![-8, 0, 37]], ![![0, 1, 0], ![-4, 12, 2], ![-10, 48, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-6, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-6, 1, 0]] 
 ![![37, 0, 0], ![31, 1, 0], ![22, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-6, 1, 0], ![0, -5, 2], ![246, 48, -6]]]
  hmulB := by decide  
  f := ![![![199, -33, 0], ![1221, 0, 0]], ![![169, -28, 0], ![1037, 0, 0]], ![![118, -17, -1], ![724, 19, 0]]]
  g := ![![![1, 0, 0], ![-31, 37, 0], ![-22, 0, 37]], ![![-1, 1, 0], ![3, -5, 2], ![-30, 48, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![11, 1, 0]] ![![37, 0, 0], ![-6, 1, 0]]
  ![![37, 0, 0], ![-33, 3, 1]] where
 M := ![![![1369, 0, 0], ![-222, 37, 0]], ![![407, 37, 0], ![-66, 6, 2]]]
 hmul := by decide  
 g := ![![![![37, 0, 0], ![0, 0, 0]], ![![27, -2, -1], ![37, 0, 0]]], ![![![11, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-33, 3, 1]] ![![37, 0, 0], ![-6, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-222, 37, 0]], ![![-1221, 111, 37], ![444, 0, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-6, 1, 0]]], ![![![-33, 3, 1]], ![![12, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![0, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![0, 1, 0]] 
 ![![41, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![0, 1, 0], ![0, 1, 2], ![246, 48, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -1], ![20, 21, 0]]]
  g := ![![![1, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![0, 1, 0], ![0, 1, 2], ![6, 48, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![18, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![18, 1, 0]] 
 ![![41, 0, 0], ![18, 1, 0], ![34, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![18, 1, 0], ![0, 19, 2], ![246, 48, 18]]]
  hmulB := by decide  
  f := ![![![217, 12, 0], ![-492, 0, 0]], ![![90, 5, 0], ![-204, 0, 0]], ![![158, -1, -1], ![-358, 21, 0]]]
  g := ![![![1, 0, 0], ![-18, 41, 0], ![-34, 0, 41]], ![![0, 1, 0], ![-10, 19, 2], ![-30, 48, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-19, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-19, 1, 0]] 
 ![![41, 0, 0], ![22, 1, 0], ![34, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-19, 1, 0], ![0, -18, 2], ![246, 48, -19]]]
  hmulB := by decide  
  f := ![![![400, -21, 0], ![861, 0, 0]], ![![248, -13, 0], ![534, 0, 0]], ![![366, -10, -1], ![788, 21, 0]]]
  g := ![![![1, 0, 0], ![-22, 41, 0], ![-34, 0, 41]], ![![-1, 1, 0], ![8, -18, 2], ![-4, 48, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![0, 1, 0]] ![![41, 0, 0], ![18, 1, 0]]
  ![![41, 0, 0], ![-41, -11, 1]] where
 M := ![![![1681, 0, 0], ![738, 41, 0]], ![![0, 41, 0], ![0, 19, 2]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![18, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-41, -11, 1]] ![![41, 0, 0], ![-19, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-779, 41, 0]], ![![-1681, -451, 41], ![1025, 205, -41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-19, 1, 0]]], ![![![-41, -11, 1]], ![![25, 5, -1]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [9, 33, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 22, 29], [32, 20, 14], [0, 1]]
 g := ![![[31, 5, 16], [13, 19, 10], [11, 36], [2, 11, 1], []], ![[39, 10, 1, 3], [2, 38, 9, 42], [18, 9], [24, 31, 20, 33], [35, 24]], ![[30, 2, 7, 41], [29, 23, 13, 13], [6, 38], [37, 26, 31, 25], [7, 24]]]
 h' := ![![[22, 22, 29], [12, 16, 39], [10, 7, 15], [25, 7, 37], [0, 0, 1], [0, 1]], ![[32, 20, 14], [32, 29, 40], [33, 0, 30], [25, 35, 40], [40, 27, 20], [22, 22, 29]], ![[0, 1], [34, 41, 7], [29, 36, 41], [30, 1, 9], [15, 16, 22], [32, 20, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 37], []]
 b := ![[], [16, 32, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [9, 33, 32, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1240077, -400674, -61662]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28839, -9318, -1434]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀


def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-681892, -205891, -33785]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-681892, -205891, -33785]] 
 ![![47, 0, 0], ![4, 1, 0], ![37, 0, 1]] where
  M :=![![![-681892, -205891, -33785], ![-8311110, -2509463, -411782], ![-46493631, -14038323, -2303572]]]
  hmulB := by decide  
  f := ![![![19750, 97, -307]], ![![74, 117, -22]], ![![16859, -628, -135]]]
  g := ![![![29611, -205891, -33785], ![360908, -2509463, -411782], ![2018975, -14038323, -2303572]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![21, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![21, 1, 0]] 
 ![![47, 0, 0], ![21, 1, 0], ![4, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![21, 1, 0], ![0, 22, 2], ![246, 48, 21]]]
  hmulB := by decide  
  f := ![![![106, 5, 0], ![-235, 0, 0]], ![![42, 2, 0], ![-93, 0, 0]], ![![-16, -12, -1], ![36, 24, 0]]]
  g := ![![![1, 0, 0], ![-21, 47, 0], ![-4, 0, 47]], ![![0, 1, 0], ![-10, 22, 2], ![-18, 48, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-681892, -205891, -33785]] ![![47, 0, 0], ![21, 1, 0]]
  ![![47, 0, 0], ![-52, 13, 1]] where
 M := ![![![-32048924, -9676877, -1587895], ![-22630842, -6833174, -1121267]]]
 hmul := by decide  
 g := ![![![![-346856, -289650, -40228], ![302821, 0, 0]], ![![-244894, -204540, -28407], ![213862, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-52, 13, 1]] ![![47, 0, 0], ![21, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![987, 47, 0]], ![![-2444, 611, 47], ![-846, 282, 47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![21, 1, 0]]], ![![![-52, 13, 1]], ![![-18, 6, 1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-157969686323, -47697489626, -7826761198]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-157969686323, -47697489626, -7826761198]] 
 ![![53, 0, 0], ![0, 53, 0], ![33, 23, 1]] where
  M :=![![![-157969686323, -47697489626, -7826761198], ![-1925383254708, -581351713453, -95394979252], ![-10770890820642, -3252171129402, -533654223827]]]
  hmulB := by decide  
  f := ![![![-601459, 75002, -4586]], ![![-1128156, -746585, 150004]], ![![-505305, -220007, 46739]]]
  g := ![![![1892706287, 2496566376, -7826761198], ![23068887936, 30428920931, -95394979252], ![129050916333, 170224075823, -533654223827]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [43, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 52], [0, 1]]
 g := ![![[49, 37], [7], [25, 38], [29], [13, 1]], ![[0, 16], [7], [42, 15], [29], [26, 52]]]
 h' := ![![[13, 52], [30, 14], [38, 22], [18, 12], [24, 20], [0, 1]], ![[0, 1], [0, 39], [6, 31], [15, 41], [19, 33], [13, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [31, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [43, 40, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4, 2391, 922]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-574, -355, 922]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![601459, -75002, 4586]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![601459, -75002, 4586]] 
 ![![53, 0, 0], ![7, 1, 0], ![25, 0, 1]] where
  M :=![![![601459, -75002, 4586], ![1128156, 746585, -150004], ![-19014570, -3036018, 821587]]]
  hmulB := by decide  
  f := ![![![157969686323, 47697489626, 7826761198]], ![![57191906773, 17268568695, 2833628446]], ![![277738358089, 83860535284, 13760816109]]]
  g := ![![![19091, -75002, 4586], ![-6563, 746585, -150004], ![-345323, -3036018, 821587]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-157969686323, -47697489626, -7826761198]] ![![601459, -75002, 4586]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-12, -25, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-12, -25, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![47, 34, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-12, -25, 1], ![246, 11, -50], ![-6273, -1077, 36]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -34, 59]], ![![-1, -1, 1], ![44, 29, -50], ![-135, -39, 36]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [2, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 58], [0, 1]]
 g := ![![[35, 41], [38, 35], [1], [33, 1], [48, 1]], ![[56, 18], [7, 24], [1], [22, 58], [37, 58]]]
 h' := ![![[48, 58], [42, 10], [47, 34], [52, 1], [22, 1], [0, 1]], ![[0, 1], [50, 49], [27, 25], [41, 58], [11, 58], [48, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [14, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [2, 11, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3271, 123, 165]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-76, -93, 165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-9, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-9, 1, 0]] 
 ![![59, 0, 0], ![50, 1, 0], ![23, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-9, 1, 0], ![0, -8, 2], ![246, 48, -9]]]
  hmulB := by decide  
  f := ![![![451, -50, 0], ![2950, 0, 0]], ![![370, -41, 0], ![2420, 0, 0]], ![![181, -16, -1], ![1184, 30, 0]]]
  g := ![![![1, 0, 0], ![-50, 59, 0], ![-23, 0, 59]], ![![-1, 1, 0], ![6, -8, 2], ![-33, 48, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-12, -25, 1]] ![![59, 0, 0], ![-9, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-531, 59, 0]], ![![-708, -1475, 59], ![354, 236, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-9, 1, 0]]], ![![![-12, -25, 1]], ![![6, 4, -1]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-16, 19, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-16, 19, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![45, 19, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-16, 19, 1], ![246, 51, 38], ![4551, 1035, 32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -19, 61]], ![![-1, 0, 1], ![-24, -11, 38], ![51, 7, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [31, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 60], [0, 1]]
 g := ![![[], [39], [0, 41], [0, 46], [0, 1]], ![[], [39], [0, 20], [0, 15], [0, 60]]]
 h' := ![![[0, 60], [11], [0, 10], [0, 38], [0, 30], [0, 1]], ![[0, 1], [11], [0, 51], [0, 23], [0, 31], [0, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [0, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [31, 0, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1877, 4035, 1198]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-853, -307, 1198]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![23, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![23, 1, 0]] 
 ![![61, 0, 0], ![23, 1, 0], ![29, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![23, 1, 0], ![0, 24, 2], ![246, 48, 23]]]
  hmulB := by decide  
  f := ![![![93, 4, 0], ![-244, 0, 0]], ![![23, 1, 0], ![-60, 0, 0]], ![![51, -10, -1], ![-134, 31, 0]]]
  g := ![![![1, 0, 0], ![-23, 61, 0], ![-29, 0, 61]], ![![0, 1, 0], ![-10, 24, 2], ![-25, 48, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-16, 19, 1]] ![![61, 0, 0], ![23, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1403, 61, 0]], ![![-976, 1159, 61], ![-122, 488, 61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![23, 1, 0]]], ![![![-16, 19, 1]], ![![-2, 8, 1]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-40, 12, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-40, 12, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![27, 12, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-40, 12, 1], ![246, 20, 24], ![2829, 699, 8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -12, 67]], ![![-1, 0, 1], ![-6, -4, 24], ![39, 9, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [15, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 66], [0, 1]]
 g := ![![[19, 9], [57, 37], [40], [26], [21], [1]], ![[0, 58], [31, 30], [40], [26], [21], [1]]]
 h' := ![![[50, 66], [16, 64], [28, 29], [5, 24], [44, 19], [52, 50], [0, 1]], ![[0, 1], [0, 3], [4, 38], [66, 43], [56, 48], [6, 17], [50, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [64, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [15, 17, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1860, 1653, 389]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-129, -45, 389]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-24, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-24, 1, 0]] 
 ![![67, 0, 0], ![43, 1, 0], ![59, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-24, 1, 0], ![0, -23, 2], ![246, 48, -24]]]
  hmulB := by decide  
  f := ![![![769, -32, 0], ![2144, 0, 0]], ![![505, -21, 0], ![1408, 0, 0]], ![![665, -16, -1], ![1854, 34, 0]]]
  g := ![![![1, 0, 0], ![-43, 67, 0], ![-59, 0, 67]], ![![-1, 1, 0], ![13, -23, 2], ![-6, 48, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-40, 12, 1]] ![![67, 0, 0], ![-24, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1608, 67, 0]], ![![-2680, 804, 67], ![1206, -268, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-24, 1, 0]]], ![![![-40, 12, 1]], ![![18, -4, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-7, 23, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-7, 23, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![64, 23, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-7, 23, 1], ![246, 64, 46], ![5535, 1227, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -23, 71]], ![![-1, 0, 1], ![-38, -14, 46], ![41, 4, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [19, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 70], [0, 1]]
 g := ![![[50, 15], [15, 40], [48, 57], [43], [19], [1]], ![[0, 56], [0, 31], [0, 14], [43], [19], [1]]]
 h' := ![![[44, 70], [70, 21], [11, 53], [35, 46], [0, 16], [52, 44], [0, 1]], ![[0, 1], [0, 50], [0, 18], [0, 25], [65, 55], [0, 27], [44, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [64, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [19, 27, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![152444, 95543, 22577]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18204, -5968, 22577]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![25, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![25, 1, 0]] 
 ![![71, 0, 0], ![25, 1, 0], ![30, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![25, 1, 0], ![0, 26, 2], ![246, 48, 25]]]
  hmulB := by decide  
  f := ![![![801, 32, 0], ![-2272, 0, 0]], ![![275, 11, 0], ![-780, 0, 0]], ![![330, 0, -1], ![-936, 36, 0]]]
  g := ![![![1, 0, 0], ![-25, 71, 0], ![-30, 0, 71]], ![![0, 1, 0], ![-10, 26, 2], ![-24, 48, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-7, 23, 1]] ![![71, 0, 0], ![25, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![1775, 71, 0]], ![![-497, 1633, 71], ![71, 639, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![25, 1, 0]]], ![![![-7, 23, 1]], ![![1, 9, 1]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-3, 32, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-3, 32, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![70, 32, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-3, 32, 1], ![246, 77, 64], ![7749, 1659, 45]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-70, -32, 73]], ![![-1, 0, 1], ![-58, -27, 64], ![63, 3, 45]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [63, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 72], [0, 1]]
 g := ![![[58, 25], [3], [61], [2, 4], [16], [1]], ![[31, 48], [3], [61], [59, 69], [16], [1]]]
 h' := ![![[69, 72], [28, 68], [61, 21], [20, 34], [41, 2], [10, 69], [0, 1]], ![[0, 1], [48, 5], [50, 52], [30, 39], [33, 71], [26, 4], [69, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [26, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [63, 4, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![921, 323, 58]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43, -21, 58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![9, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![9, 1, 0]] 
 ![![73, 0, 0], ![9, 1, 0], ![28, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![9, 1, 0], ![0, 10, 2], ![246, 48, 9]]]
  hmulB := by decide  
  f := ![![![532, 59, 0], ![-4307, 0, 0]], ![![54, 6, 0], ![-437, 0, 0]], ![![190, 16, -1], ![-1538, 37, 0]]]
  g := ![![![1, 0, 0], ![-9, 73, 0], ![-28, 0, 73]], ![![0, 1, 0], ![-2, 10, 2], ![-6, 48, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-3, 32, 1]] ![![73, 0, 0], ![9, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![657, 73, 0]], ![![-219, 2336, 73], ![219, 365, 73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![9, 1, 0]]], ![![![-3, 32, 1]], ![![3, 5, 1]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![10, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![10, 1, 0]] 
 ![![79, 0, 0], ![10, 1, 0], ![24, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![10, 1, 0], ![0, 11, 2], ![246, 48, 10]]]
  hmulB := by decide  
  f := ![![![61, 6, 0], ![-474, 0, 0]], ![![-10, -1, 0], ![80, 0, 0]], ![![16, -4, -1], ![-124, 40, 0]]]
  g := ![![![1, 0, 0], ![-10, 79, 0], ![-24, 0, 79]], ![![0, 1, 0], ![-2, 11, 2], ![-6, 48, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![28, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![28, 1, 0]] 
 ![![79, 0, 0], ![28, 1, 0], ![68, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![28, 1, 0], ![0, 29, 2], ![246, 48, 28]]]
  hmulB := by decide  
  f := ![![![1009, 36, 0], ![-2844, 0, 0]], ![![308, 11, 0], ![-868, 0, 0]], ![![860, 16, -1], ![-2424, 40, 0]]]
  g := ![![![1, 0, 0], ![-28, 79, 0], ![-68, 0, 79]], ![![0, 1, 0], ![-12, 29, 2], ![-38, 48, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-39, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-39, 1, 0]] 
 ![![79, 0, 0], ![40, 1, 0], ![49, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-39, 1, 0], ![0, -38, 2], ![246, 48, -39]]]
  hmulB := by decide  
  f := ![![![3082, -79, 0], ![6241, 0, 0]], ![![1600, -41, 0], ![3240, 0, 0]], ![![1960, -31, -1], ![3969, 40, 0]]]
  g := ![![![1, 0, 0], ![-40, 79, 0], ![-49, 0, 79]], ![![-1, 1, 0], ![18, -38, 2], ![3, 48, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![10, 1, 0]] ![![79, 0, 0], ![28, 1, 0]]
  ![![79, 0, 0], ![-18, -20, 1]] where
 M := ![![![6241, 0, 0], ![2212, 79, 0]], ![![790, 79, 0], ![280, 39, 2]]]
 hmul := by decide  
 g := ![![![![79, 0, 0], ![0, 0, 0]], ![![28, 1, 0], ![0, 0, 0]]], ![![![10, 1, 0], ![0, 0, 0]], ![![4, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-18, -20, 1]] ![![79, 0, 0], ![-39, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-3081, 79, 0]], ![![-1422, -1580, 79], ![948, 790, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-39, 1, 0]]], ![![![-18, -20, 1]], ![![12, 10, -1]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB278I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB278I1 : PrimesBelowBoundCertificateInterval O 31 79 278 where
  m := 11
  g := ![3, 3, 1, 3, 2, 2, 2, 2, 2, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB278I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0, I47N1, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
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
    · exact ![37, 37, 37]
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![79, 79, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
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
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I37N0, I37N1, I41N0, I41N1, I41N2, I47N0, I47N1, I53N1, I59N1, I61N1, I67N1, I71N1, I73N1, I79N0, I79N1, I79N2]
  Il := ![[I37N0, I37N1, I37N1], [I41N0, I41N1, I41N2], [], [I47N0, I47N1, I47N1], [I53N1], [I59N1], [I61N1], [I67N1], [I71N1], [I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
