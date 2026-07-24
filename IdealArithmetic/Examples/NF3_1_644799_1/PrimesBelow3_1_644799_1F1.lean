
import IdealArithmetic.Examples.NF3_1_644799_1.RI3_1_644799_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![12, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![12, 1, 0]] 
 ![![37, 0, 0], ![12, 1, 0], ![11, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![12, 1, 0], ![-3, 10, 9], ![-156, 1, 15]]]
  hmulB := by decide  
  f := ![![![3409, -12262, -11016], ![814, 45288, 0]], ![![1104, -3967, -3564], ![260, 14652, 0]], ![![1007, -3646, -3275], ![262, 13464, 0]]]
  g := ![![![1, 0, 0], ![-12, 37, 0], ![-11, 0, 37]], ![![0, 1, 0], ![-6, 10, 9], ![-9, 1, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![12, 1, 0]] ![![37, 0, 0], ![12, 1, 0]]
  ![![37, 0, 0], ![-9, -14, 1]] where
 M := ![![![1369, 0, 0], ![444, 37, 0]], ![![444, 37, 0], ![141, 22, 9]]]
 hmul := by decide  
 g := ![![![![37, 0, 0], ![0, 0, 0]], ![![12, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![6, 4, 0], ![9, 0, 0]]]]
 hle2 := by decide  
def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-9, -14, 1]] ![![37, 0, 0], ![12, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![444, 37, 0]], ![![-333, -518, 37], ![-222, -148, -111]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![12, 1, 0]]], ![![![-9, -14, 1]], ![![-6, -4, -3]]]]
 hle2 := by decide  

def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N0, I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N0
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![20, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![20, 1, 0]] 
 ![![41, 0, 0], ![20, 1, 0], ![28, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![20, 1, 0], ![-3, 18, 9], ![-156, 1, 23]]]
  hmulB := by decide  
  f := ![![![1710, -11948, -5967], ![574, 27183, 0]], ![![829, -5821, -2907], ![288, 13243, 0]], ![![1160, -8160, -4075], ![408, 18564, 0]]]
  g := ![![![1, 0, 0], ![-20, 41, 0], ![-28, 0, 41]], ![![0, 1, 0], ![-15, 18, 9], ![-20, 1, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-16, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-16, 1, 0]] 
 ![![41, 0, 0], ![25, 1, 0], ![36, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-16, 1, 0], ![-3, -18, 9], ![-156, 1, -13]]]
  hmulB := by decide  
  f := ![![![261, 1657, -828], ![-41, 3772, 0]], ![![169, 1008, -504], ![1, 2296, 0]], ![![228, 1455, -727], ![-39, 3312, 0]]]
  g := ![![![1, 0, 0], ![-25, 41, 0], ![-36, 0, 41]], ![![-1, 1, 0], ![3, -18, 9], ![7, 1, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-5, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-5, 1, 0]] 
 ![![41, 0, 0], ![36, 1, 0], ![14, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-5, 1, 0], ![-3, -7, 9], ![-156, 1, -2]]]
  hmulB := by decide  
  f := ![![![-685, -1626, 2088], ![82, -9512, 0]], ![![-603, -1422, 1827], ![42, -8323, 0]], ![![-235, -555, 713], ![19, -3248, 0]]]
  g := ![![![1, 0, 0], ![-36, 41, 0], ![-14, 0, 41]], ![![-1, 1, 0], ![3, -7, 9], ![-4, 1, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![20, 1, 0]] ![![41, 0, 0], ![-16, 1, 0]]
  ![![41, 0, 0], ![-4, -18, 1]] where
 M := ![![![1681, 0, 0], ![-656, 41, 0]], ![![820, 41, 0], ![-323, 2, 9]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![-12, 19, -1], ![41, 0, 0]]], ![![![20, 1, 0], ![0, 0, 0]], ![![-7, 4, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-4, -18, 1]] ![![41, 0, 0], ![-5, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-205, 41, 0]], ![![-164, -738, 41], ![-82, 123, -164]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-5, 1, 0]]], ![![![-4, -18, 1]], ![![-2, 3, -4]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-8, 15, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-8, 15, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![35, 15, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-8, 15, 1], ![-201, -37, 138], ![-2427, -2, 40]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -15, 43]], ![![-1, 0, 1], ![-117, -49, 138], ![-89, -14, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [22, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 42], [0, 1]]
 g := ![![[23, 31], [27, 35], [24], [1, 14], [1]], ![[32, 12], [33, 8], [24], [12, 29], [1]]]
 h' := ![![[10, 42], [8, 17], [42, 11], [21, 14], [21, 10], [0, 1]], ![[0, 1], [6, 26], [23, 32], [32, 29], [35, 33], [10, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [8, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [22, 33, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5350, -3804, -159]
  a := ![5, 3, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, -33, -159]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-9, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-9, 1, 0]] 
 ![![43, 0, 0], ![34, 1, 0], ![3, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-9, 1, 0], ![-3, -11, 9], ![-156, 1, -6]]]
  hmulB := by decide  
  f := ![![![781, 2928, -2394], ![-86, 11438, 0]], ![![622, 2311, -1890], ![-42, 9030, 0]], ![![57, 204, -167], ![6, 798, 0]]]
  g := ![![![1, 0, 0], ![-34, 43, 0], ![-3, 0, 43]], ![![-1, 1, 0], ![8, -11, 9], ![-4, 1, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-8, 15, 1]] ![![43, 0, 0], ![-9, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-387, 43, 0]], ![![-344, 645, 43], ![-129, -172, 129]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-9, 1, 0]]], ![![![-8, 15, 1]], ![![-3, -4, 3]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![11, -6, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![11, -6, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![11, 41, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![11, -6, 1], ![-138, 24, -51], ![849, -23, -4]]]
  hmulB := by decide  
  f := ![![![-10, 6, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -41, 47]], ![![0, -1, 1], ![9, 45, -51], ![19, 3, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [3, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 46], [0, 1]]
 g := ![![[4, 16], [16, 17], [32, 34], [36, 3], [1]], ![[0, 31], [0, 30], [0, 13], [0, 44], [1]]]
 h' := ![![[35, 46], [46, 43], [45, 39], [33, 38], [44, 35], [0, 1]], ![[0, 1], [0, 4], [0, 8], [0, 9], [0, 12], [35, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [17, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [3, 12, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![340, -3484, 424]
  a := ![-5, -4, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-92, -444, 424]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![4, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![4, 1, 0]] 
 ![![47, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![4, 1, 0], ![-3, 2, 9], ![-156, 1, 7]]]
  hmulB := by decide  
  f := ![![![-931, 625, 2808], ![-47, -14664, 0]], ![![-78, 52, 234], ![1, -1222, 0]], ![![-80, 53, 239], ![5, -1248, 0]]]
  g := ![![![1, 0, 0], ![-4, 47, 0], ![-4, 0, 47]], ![![0, 1, 0], ![-1, 2, 9], ![-4, 1, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![11, -6, 1]] ![![47, 0, 0], ![4, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![188, 47, 0]], ![![517, -282, 47], ![-94, 0, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![4, 1, 0]]], ![![![11, -6, 1]], ![![-2, 0, -1]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [49, 50, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 0, 16], [38, 52, 37], [0, 1]]
 g := ![![[4, 49, 4], [15, 40], [4, 36, 40], [7, 1], [1]], ![[12, 39, 29, 52], [39, 9], [33, 52, 34, 49], [50, 36], [51, 52, 15, 15]], ![[44, 14, 26, 46], [37, 46], [10, 0, 22, 25], [42, 25], [25, 6, 12, 38]]]
 h' := ![![[16, 0, 16], [51, 51, 2], [16, 25, 26], [44, 49, 27], [4, 3, 1], [0, 1]], ![[38, 52, 37], [35, 33, 19], [41, 5, 3], [37, 48, 15], [7, 43, 47], [16, 0, 16]], ![[0, 1], [26, 22, 32], [39, 23, 24], [24, 9, 11], [11, 7, 5], [38, 52, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 3], []]
 b := ![[], [4, 23, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [49, 50, 52, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-744976957, 15605161, 37564121]
  a := ![1, 1, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14056169, 294437, 708757]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [22, 34, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 19, 42], [23, 39, 17], [0, 1]]
 g := ![![[33, 29, 26], [35, 44, 53], [25, 49], [14, 21, 25], [1]], ![[34, 43, 6, 8], [23, 36, 12, 34], [44, 27], [5, 31, 53, 37], [9, 53, 50, 43]], ![[32, 7, 30, 25], [56, 39, 47, 22], [57, 27], [20, 51, 8, 51], [41, 48, 27, 16]]]
 h' := ![![[41, 19, 42], [56, 46, 47], [32, 23, 17], [46, 18, 7], [37, 25, 5], [0, 1]], ![[23, 39, 17], [12, 22, 48], [2, 51, 36], [12, 13, 26], [47, 4, 6], [41, 19, 42]], ![[0, 1], [20, 50, 23], [36, 44, 6], [46, 28, 26], [55, 30, 48], [23, 39, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 41], []]
 b := ![[], [53, 9, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [22, 34, 54, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21370626, -46315, 185260]
  a := ![7, 5, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-362214, -785, 3140]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-14, -8, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-14, -8, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![47, 53, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-14, -8, 1], ![-132, 3, -69], ![1161, -25, -35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -53, 61]], ![![-1, -1, 1], ![51, 60, -69], ![46, 30, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [18, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 60], [0, 1]]
 g := ![![[44, 41], [13], [13, 22], [47, 45], [1, 1]], ![[24, 20], [13], [35, 39], [31, 16], [2, 60]]]
 h' := ![![[1, 60], [49, 38], [10, 47], [8, 49], [43, 44], [0, 1]], ![[0, 1], [26, 23], [57, 14], [57, 12], [26, 17], [1, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [6, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [18, 60, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5219, -3723, -564]
  a := ![5, 3, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![349, 429, -564]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![8, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![8, 1, 0]] 
 ![![61, 0, 0], ![8, 1, 0], ![35, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![8, 1, 0], ![-3, 6, 9], ![-156, 1, 11]]]
  hmulB := by decide  
  f := ![![![882, -1796, -2691], ![122, 18239, 0]], ![![109, -235, -351], ![62, 2379, 0]], ![![502, -1031, -1544], ![101, 10465, 0]]]
  g := ![![![1, 0, 0], ![-8, 61, 0], ![-35, 0, 61]], ![![0, 1, 0], ![-6, 6, 9], ![-9, 1, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-14, -8, 1]] ![![61, 0, 0], ![8, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![488, 61, 0]], ![![-854, -488, 61], ![-244, -61, -61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![8, 1, 0]]], ![![![-14, -8, 1]], ![![-4, -1, -1]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![2, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![2, 1, 0]] 
 ![![67, 0, 0], ![2, 1, 0], ![22, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![2, 1, 0], ![-3, 0, 9], ![-156, 1, 5]]]
  hmulB := by decide  
  f := ![![![4485, -2, -13464], ![134, 100232, 0]], ![![130, -1, -396], ![68, 2948, 0]], ![![1472, -1, -4421], ![67, 32912, 0]]]
  g := ![![![1, 0, 0], ![-2, 67, 0], ![-22, 0, 67]], ![![0, 1, 0], ![-3, 0, 9], ![-4, 1, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![27, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![27, 1, 0]] 
 ![![67, 0, 0], ![27, 1, 0], ![14, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![27, 1, 0], ![-3, 25, 9], ![-156, 1, 30]]]
  hmulB := by decide  
  f := ![![![-848, 7753, 2790], ![-201, -20770, 0]], ![![-345, 3101, 1116], ![-66, -8308, 0]], ![![-178, 1620, 583], ![-40, -4340, 0]]]
  g := ![![![1, 0, 0], ![-27, 67, 0], ![-14, 0, 67]], ![![0, 1, 0], ![-12, 25, 9], ![-9, 1, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-30, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-30, 1, 0]] 
 ![![67, 0, 0], ![37, 1, 0], ![27, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-30, 1, 0], ![-3, -32, 9], ![-156, 1, -27]]]
  hmulB := by decide  
  f := ![![![-3002, -36205, 10179], ![871, -75777, 0]], ![![-1661, -19975, 5616], ![470, -41808, 0]], ![![-1212, -14590, 4102], ![346, -30537, 0]]]
  g := ![![![1, 0, 0], ![-37, 67, 0], ![-27, 0, 67]], ![![-1, 1, 0], ![14, -32, 9], ![8, 1, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![2, 1, 0]] ![![67, 0, 0], ![27, 1, 0]]
  ![![67, 0, 0], ![28, 3, 1]] where
 M := ![![![4489, 0, 0], ![1809, 67, 0]], ![![134, 67, 0], ![51, 27, 9]]]
 hmul := by decide  
 g := ![![![![39, -3, -1], ![67, 0, 0]], ![![-1, -2, -1], ![67, 0, 0]]], ![![![-26, -2, -1], ![67, 0, 0]], ![![-3, 0, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![28, 3, 1]] ![![67, 0, 0], ![-30, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-2010, 67, 0]], ![![1876, 201, 67], ![-1005, -67, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-30, 1, 0]]], ![![![28, 3, 1]], ![![-15, -1, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-32, -11, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-32, -11, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![39, 60, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-32, -11, 1], ![-123, -9, -96], ![1629, -28, -62]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -60, 71]], ![![-1, -1, 1], ![51, 81, -96], ![57, 52, -62]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [69, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 70], [0, 1]]
 g := ![![[15, 30], [23, 40], [30, 16], [4], [48], [1]], ![[63, 41], [16, 31], [13, 55], [4], [48], [1]]]
 h' := ![![[30, 70], [46, 39], [60, 18], [68, 4], [29, 69], [2, 30], [0, 1]], ![[0, 1], [9, 32], [32, 53], [46, 67], [40, 2], [50, 41], [30, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [69, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [69, 41, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-526518, -266621, 29389]
  a := ![-41, -21, 124]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23559, -28591, 29389]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![25, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![25, 1, 0]] 
 ![![71, 0, 0], ![25, 1, 0], ![62, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![25, 1, 0], ![-3, 23, 9], ![-156, 1, 28]]]
  hmulB := by decide  
  f := ![![![4922, -41003, -16038], ![1207, 126522, 0]], ![![1731, -14427, -5643], ![427, 44517, 0]], ![![4309, -35805, -14005], ![1023, 110484, 0]]]
  g := ![![![1, 0, 0], ![-25, 71, 0], ![-62, 0, 71]], ![![0, 1, 0], ![-16, 23, 9], ![-27, 1, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-32, -11, 1]] ![![71, 0, 0], ![25, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![1775, 71, 0]], ![![-2272, -781, 71], ![-923, -284, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![25, 1, 0]]], ![![![-32, -11, 1]], ![![-13, -4, -1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![12, 18, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![12, 18, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![12, 18, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![12, 18, 1], ![-210, -23, 165], ![-2895, 1, 69]]]
  hmulB := by decide  
  f := ![![![-11, -18, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -18, 73]], ![![0, 0, 1], ![-30, -41, 165], ![-51, -17, 69]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [14, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 72], [0, 1]]
 g := ![![[5, 64], [72], [19], [15, 37], [9], [1]], ![[51, 9], [72], [19], [53, 36], [9], [1]]]
 h' := ![![[3, 72], [2, 8], [34, 27], [9, 47], [70, 16], [59, 3], [0, 1]], ![[0, 1], [26, 65], [42, 46], [4, 26], [45, 57], [68, 70], [3, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [31, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [14, 70, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3262, -1170, 665]
  a := ![-3, -1, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-154, -180, 665]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-19, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-19, 1, 0]] 
 ![![73, 0, 0], ![54, 1, 0], ![4, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-19, 1, 0], ![-3, -21, 9], ![-156, 1, -16]]]
  hmulB := by decide  
  f := ![![![-2300, -16911, 7245], ![438, -58765, 0]], ![![-1708, -12499, 5355], ![293, -43435, 0]], ![![-119, -927, 397], ![51, -3220, 0]]]
  g := ![![![1, 0, 0], ![-54, 73, 0], ![-4, 0, 73]], ![![-1, 1, 0], ![15, -21, 9], ![-2, 1, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![12, 18, 1]] ![![73, 0, 0], ![-19, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1387, 73, 0]], ![![876, 1314, 73], ![-438, -365, 146]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-19, 1, 0]]], ![![![12, 18, 1]], ![![-6, -5, 2]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![11, 33, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![11, 33, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![11, 33, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![11, 33, 1], ![-255, -54, 300], ![-5235, 16, 113]]]
  hmulB := by decide  
  f := ![![![-10, -33, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -33, 79]], ![![0, 0, 1], ![-45, -126, 300], ![-82, -47, 113]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [39, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 78], [0, 1]]
 g := ![![[17, 72], [8, 46], [22, 18], [78, 20], [13], [1]], ![[76, 7], [4, 33], [17, 61], [11, 59], [13], [1]]]
 h' := ![![[48, 78], [4, 54], [11, 58], [39, 52], [66, 40], [40, 48], [0, 1]], ![[0, 1], [68, 25], [30, 21], [7, 27], [11, 39], [53, 31], [48, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [19, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [39, 31, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12892, -10157, 1593]
  a := ![-8, -5, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-385, -794, 1593]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![16, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![16, 1, 0]] 
 ![![79, 0, 0], ![16, 1, 0], ![45, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![16, 1, 0], ![-3, 14, 9], ![-156, 1, 19]]]
  hmulB := by decide  
  f := ![![![-449, 2100, 1350], ![0, -11850, 0]], ![![-90, 420, 270], ![1, -2370, 0]], ![![-259, 1196, 769], ![16, -6750, 0]]]
  g := ![![![1, 0, 0], ![-16, 79, 0], ![-45, 0, 79]], ![![0, 1, 0], ![-8, 14, 9], ![-13, 1, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![11, 33, 1]] ![![79, 0, 0], ![16, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![1264, 79, 0]], ![![869, 2607, 79], ![-79, 474, 316]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![16, 1, 0]]], ![![![11, 33, 1]], ![![-1, 6, 4]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB228I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB228I1 : PrimesBelowBoundCertificateInterval O 31 79 228 where
  m := 11
  g := ![3, 3, 2, 2, 1, 1, 2, 3, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB228I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N0, I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
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
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N0
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
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
  β := ![I37N0, I41N0, I41N1, I41N2, I43N1, I47N1, I61N1, I67N0, I67N1, I67N2, I71N1, I73N1, I79N1]
  Il := ![[I37N0, I37N0, I37N0], [I41N0, I41N1, I41N2], [I43N1], [I47N1], [], [], [I61N1], [I67N0, I67N1, I67N2], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
