
import IdealArithmetic.Examples.NF3_1_532652_1.RI3_1_532652_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 8, -3]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![193, 8, -3]] 
 ![![37, 0, 0], ![6, 1, 0], ![1, 0, 1]] where
  M :=![![![193, 8, -3], ![-726, 1, 8], ![1936, -214, 1]]]
  hmulB := by decide  
  f := ![![![1713, 634, 67]], ![![716, 265, 28]], ![![4193, 1552, 164]]]
  g := ![![![4, 8, -3], ![-20, 1, 8], ![87, -214, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-3, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-3, 1, 0]] 
 ![![37, 0, 0], ![34, 1, 0], ![28, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-3, 1, 0], ![0, -3, 1], ![242, 64, -3]]]
  hmulB := by decide  
  f := ![![![82, -27, 0], ![999, 0, 0]], ![![76, -25, 0], ![926, 0, 0]], ![![64, -21, 0], ![780, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 37, 0], ![-28, 0, 37]], ![![-1, 1, 0], ![2, -3, 1], ![-50, 64, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![193, 8, -3]] ![![37, 0, 0], ![-3, 1, 0]]
  ![![37, 0, 0], ![-55, 3, 1]] where
 M := ![![![7141, 296, -111], ![-1305, -23, 17]]]
 hmul := by decide  
 g := ![![![![83, 14, -1], ![-74, 0, 0]], ![![-10, -2, 0], ![17, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-55, 3, 1]] ![![37, 0, 0], ![-3, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-111, 37, 0]], ![![-2035, 111, 37], ![407, 0, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-3, 1, 0]]], ![![![-55, 3, 1]], ![![11, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-20, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-20, 1, 0]] 
 ![![41, 0, 0], ![21, 1, 0], ![10, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-20, 1, 0], ![0, -20, 1], ![242, 64, -20]]]
  hmulB := by decide  
  f := ![![![821, -41, 0], ![1681, 0, 0]], ![![441, -22, 0], ![903, 0, 0]], ![![210, -10, 0], ![430, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 41, 0], ![-10, 0, 41]], ![![-1, 1, 0], ![10, -20, 1], ![-22, 64, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-15, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-15, 1, 0]] 
 ![![41, 0, 0], ![26, 1, 0], ![21, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-15, 1, 0], ![0, -15, 1], ![242, 64, -15]]]
  hmulB := by decide  
  f := ![![![256, -17, 0], ![697, 0, 0]], ![![166, -11, 0], ![452, 0, 0]], ![![126, -8, 0], ![343, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 41, 0], ![-21, 0, 41]], ![![-1, 1, 0], ![9, -15, 1], ![-27, 64, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-6, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-6, 1, 0]] 
 ![![41, 0, 0], ![35, 1, 0], ![5, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-6, 1, 0], ![0, -6, 1], ![242, 64, -6]]]
  hmulB := by decide  
  f := ![![![55, -9, 0], ![369, 0, 0]], ![![49, -8, 0], ![329, 0, 0]], ![![7, -1, 0], ![47, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 41, 0], ![-5, 0, 41]], ![![-1, 1, 0], ![5, -6, 1], ![-48, 64, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-20, 1, 0]] ![![41, 0, 0], ![-15, 1, 0]]
  ![![41, 0, 0], ![-28, 6, 1]] where
 M := ![![![1681, 0, 0], ![-615, 41, 0]], ![![-820, 41, 0], ![300, -35, 1]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![13, -5, -1], ![41, 0, 0]]], ![![![8, -5, -1], ![41, 0, 0]], ![![8, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-28, 6, 1]] ![![41, 0, 0], ![-6, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-246, 41, 0]], ![![-1148, 246, 41], ![410, 0, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-6, 1, 0]]], ![![![-28, 6, 1]], ![![10, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-50, -10, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-50, -10, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![36, 33, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-50, -10, 1], ![242, 14, -10], ![-2420, -398, 14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -33, 43]], ![![-2, -1, 1], ![14, 8, -10], ![-68, -20, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [15, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 42], [0, 1]]
 g := ![![[14, 23], [6, 16], [31], [18, 25], [1]], ![[0, 20], [0, 27], [31], [14, 18], [1]]]
 h' := ![![[5, 42], [39, 18], [23, 4], [31, 26], [28, 5], [0, 1]], ![[0, 1], [0, 25], [0, 39], [32, 17], [10, 38], [5, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [6, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [15, 38, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![499, 332, 27]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, -13, 27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![10, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![10, 1, 0]] 
 ![![43, 0, 0], ![10, 1, 0], ![29, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![10, 1, 0], ![0, 10, 1], ![242, 64, 10]]]
  hmulB := by decide  
  f := ![![![111, 11, 0], ![-473, 0, 0]], ![![10, 1, 0], ![-42, 0, 0]], ![![73, 7, 0], ![-311, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 43, 0], ![-29, 0, 43]], ![![0, 1, 0], ![-3, 10, 1], ![-16, 64, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-50, -10, 1]] ![![43, 0, 0], ![10, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![430, 43, 0]], ![![-2150, -430, 43], ![-258, -86, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![10, 1, 0]]], ![![![-50, -10, 1]], ![![-6, -2, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, -5, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-39, -5, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![8, 42, 1]] where
  M :=![![![-39, -5, 1], ![242, 25, -5], ![-1210, -78, 25]]]
  hmulB := by decide  
  f := ![![![5, 1, 0]], ![![0, 5, 1]], ![![6, 6, 1]]]
  g := ![![![-1, -1, 1], ![6, 5, -5], ![-30, -24, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [23, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 46], [0, 1]]
 g := ![![[30, 21], [38, 42], [12, 9], [6, 37], [1]], ![[16, 26], [10, 5], [6, 38], [44, 10], [1]]]
 h' := ![![[15, 46], [19, 16], [6, 29], [3, 3], [24, 15], [0, 1]], ![[0, 1], [24, 31], [18, 18], [1, 44], [14, 32], [15, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [4, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [23, 32, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2912, 1350, 670]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-176, -570, 670]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![5, 1, 0]] 
 ![![47, 0, 0], ![5, 1, 0], ![22, 0, 1]] where
  M :=![![![5, 1, 0], ![0, 5, 1], ![242, 64, 5]]]
  hmulB := by decide  
  f := ![![![-39, -5, 1]], ![![1, 0, 0]], ![![-44, -4, 1]]]
  g := ![![![0, 1, 0], ![-1, 5, 1], ![-4, 64, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-39, -5, 1]] ![![5, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-51, 15, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-51, 15, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![2, 15, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-51, 15, 1], ![242, 13, 15], ![3630, 1202, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -15, 53]], ![![-1, 0, 1], ![4, -4, 15], ![68, 19, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [50, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 52], [0, 1]]
 g := ![![[20, 9], [42], [20, 6], [1], [7, 1]], ![[30, 44], [42], [9, 47], [1], [14, 52]]]
 h' := ![![[7, 52], [16, 50], [7, 28], [20, 18], [21, 52], [0, 1]], ![[0, 1], [48, 3], [44, 25], [40, 35], [14, 1], [7, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [34, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [50, 46, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![718, 32, 147]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, -41, 147]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-15, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-15, 1, 0]] 
 ![![53, 0, 0], ![38, 1, 0], ![40, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-15, 1, 0], ![0, -15, 1], ![242, 64, -15]]]
  hmulB := by decide  
  f := ![![![751, -50, 0], ![2650, 0, 0]], ![![556, -37, 0], ![1962, 0, 0]], ![![560, -37, 0], ![1976, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 53, 0], ![-40, 0, 53]], ![![-1, 1, 0], ![10, -15, 1], ![-30, 64, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-51, 15, 1]] ![![53, 0, 0], ![-15, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-795, 53, 0]], ![![-2703, 795, 53], ![1007, -212, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-15, 1, 0]]], ![![![-51, 15, 1]], ![![19, -4, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, -2, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![19, -2, 0]] 
 ![![59, 0, 0], ![20, 1, 0], ![13, 0, 1]] where
  M :=![![![19, -2, 0], ![0, 19, -2], ![-484, -128, 19]]]
  hmulB := by decide  
  f := ![![![105, 38, 4]], ![![52, 19, 2]], ![![179, 66, 7]]]
  g := ![![![1, -2, 0], ![-6, 19, -2], ![31, -128, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 104, -11]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![1, 104, -11]] 
 ![![59, 0, 0], ![49, 1, 0], ![18, 0, 1]] where
  M :=![![![1, 104, -11], ![-2662, -703, 104], ![25168, 3994, -703]]]
  hmulB := by decide  
  f := ![![![-78833, -29178, -3083]], ![![-78117, -28913, -3055]], ![![-143730, -53198, -5621]]]
  g := ![![![-83, 104, -11], ![507, -703, 104], ![-2676, 3994, -703]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![19, -2, 0]] ![![1, 104, -11]]
  ![![5343, 3382, -417]] where
 M := ![![![5343, 3382, -417]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![5343, 3382, -417]] ![![1, 104, -11]]
  ![![59, 0, 0]] where
 M := ![![![-19492597, -3487372, 586106]]]
 hmul := by decide  
 g := ![![![![-330383, -59108, 9934]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![145, 32, -5]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![145, 32, -5]] 
 ![![61, 0, 0], ![2, 1, 0], ![57, 0, 1]] where
  M :=![![![145, 32, -5], ![-1210, -175, 32], ![7744, 838, -175]]]
  hmulB := by decide  
  f := ![![![3809, 1410, 149]], ![![716, 265, 28]], ![![9153, 3388, 358]]]
  g := ![![![6, 32, -5], ![-44, -175, 32], ![263, 838, -175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-1, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-1, 1, 0]] 
 ![![61, 0, 0], ![60, 1, 0], ![60, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-1, 1, 0], ![0, -1, 1], ![242, 64, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![183, 0, 0]], ![![2, -1, 0], ![62, 0, 0]], ![![2, -1, 0], ![62, 1, 0]]]
  g := ![![![1, 0, 0], ![-60, 61, 0], ![-60, 0, 61]], ![![-1, 1, 0], ![0, -1, 1], ![-58, 64, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![145, 32, -5]] ![![61, 0, 0], ![-1, 1, 0]]
  ![![61, 0, 0], ![-63, 1, 1]] where
 M := ![![![8845, 1952, -305], ![-1355, -207, 37]]]
 hmul := by decide  
 g := ![![![![82, 33, -4], ![-61, 0, 0]], ![![16, -4, 0], ![37, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-63, 1, 1]] ![![61, 0, 0], ![-1, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-61, 61, 0]], ![![-3843, 61, 61], ![305, 0, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-1, 1, 0]]], ![![![-63, 1, 1]], ![![5, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N1
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [16, 23, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 36, 8], [24, 30, 59], [0, 1]]
 g := ![![[63, 38, 49], [17, 33, 40], [21, 35], [61, 55], [21, 1], []], ![[0, 9, 64, 34], [66, 48, 7, 38], [62, 6], [48, 47], [25, 29], [44, 64]], ![[64, 26, 30, 15], [41, 36, 65, 64], [22, 47], [49, 10], [18, 23], [60, 64]]]
 h' := ![![[64, 36, 8], [63, 66, 60], [28, 46, 24], [30, 55, 13], [66, 37, 16], [0, 0, 1], [0, 1]], ![[24, 30, 59], [40, 50, 50], [27, 2, 16], [9, 40, 26], [24, 6, 39], [42, 26, 30], [64, 36, 8]], ![[0, 1], [47, 18, 24], [23, 19, 27], [43, 39, 28], [36, 24, 12], [18, 41, 36], [24, 30, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 31], []]
 b := ![[], [51, 5, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [16, 23, 46, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1233872, -639850, -76715]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18416, -9550, -1145]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-40, -38, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-40, -38, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![31, 33, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-40, -38, 1], ![242, 24, -38], ![-9196, -2190, 24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -33, 71]], ![![-1, -1, 1], ![20, 18, -38], ![-140, -42, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [40, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 70], [0, 1]]
 g := ![![[0, 16], [0, 64], [], [], [], [1]], ![[0, 55], [0, 7], [], [], [], [1]]]
 h' := ![![[0, 70], [0, 67], [0, 8], [24], [38], [31], [0, 1]], ![[0, 1], [0, 4], [0, 63], [24], [38], [31], [0, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [0, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [40, 0, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![524, 370, 65]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21, -25, 65]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-33, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-33, 1, 0]] 
 ![![71, 0, 0], ![38, 1, 0], ![47, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-33, 1, 0], ![0, -33, 1], ![242, 64, -33]]]
  hmulB := by decide  
  f := ![![![1387, -42, 0], ![2982, 0, 0]], ![![760, -23, 0], ![1634, 0, 0]], ![![907, -27, 0], ![1950, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 71, 0], ![-47, 0, 71]], ![![-1, 1, 0], ![17, -33, 1], ![-9, 64, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-40, -38, 1]] ![![71, 0, 0], ![-33, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2343, 71, 0]], ![![-2840, -2698, 71], ![1562, 1278, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-33, 1, 0]]], ![![![-40, -38, 1]], ![![22, 18, -1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-14, 14, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-14, 14, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![59, 14, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-14, 14, 1], ![242, 50, 14], ![3388, 1138, 50]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -14, 73]], ![![-1, 0, 1], ![-8, -2, 14], ![6, 6, 50]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [66, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 72], [0, 1]]
 g := ![![[36, 19], [41], [6], [3, 54], [67], [1]], ![[6, 54], [41], [6], [33, 19], [67], [1]]]
 h' := ![![[33, 72], [49, 26], [45, 25], [21, 15], [7, 45], [7, 33], [0, 1]], ![[0, 1], [31, 47], [67, 48], [5, 58], [32, 28], [1, 40], [33, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [38, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [66, 40, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9303, 3472, 467]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-250, -42, 467]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-14, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-14, 1, 0]] 
 ![![73, 0, 0], ![59, 1, 0], ![23, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-14, 1, 0], ![0, -14, 1], ![242, 64, -14]]]
  hmulB := by decide  
  f := ![![![771, -55, 0], ![4015, 0, 0]], ![![617, -44, 0], ![3213, 0, 0]], ![![241, -17, 0], ![1255, 1, 0]]]
  g := ![![![1, 0, 0], ![-59, 73, 0], ![-23, 0, 73]], ![![-1, 1, 0], ![11, -14, 1], ![-44, 64, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-14, 14, 1]] ![![73, 0, 0], ![-14, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1022, 73, 0]], ![![-1022, 1022, 73], ![438, -146, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-14, 1, 0]]], ![![![-14, 14, 1]], ![![6, -2, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![9, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![9, 1, 0]] 
 ![![79, 0, 0], ![9, 1, 0], ![77, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![9, 1, 0], ![0, 9, 1], ![242, 64, 9]]]
  hmulB := by decide  
  f := ![![![343, 38, 0], ![-3002, 0, 0]], ![![27, 3, 0], ![-236, 0, 0]], ![![335, 37, 0], ![-2932, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 79, 0], ![-77, 0, 79]], ![![0, 1, 0], ![-2, 9, 1], ![-13, 64, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![11, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![11, 1, 0]] 
 ![![79, 0, 0], ![11, 1, 0], ![37, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![11, 1, 0], ![0, 11, 1], ![242, 64, 11]]]
  hmulB := by decide  
  f := ![![![331, 30, 0], ![-2370, 0, 0]], ![![33, 3, 0], ![-236, 0, 0]], ![![145, 13, 0], ![-1038, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 79, 0], ![-37, 0, 79]], ![![0, 1, 0], ![-2, 11, 1], ![-11, 64, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-20, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-20, 1, 0]] 
 ![![79, 0, 0], ![59, 1, 0], ![74, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-20, 1, 0], ![0, -20, 1], ![242, 64, -20]]]
  hmulB := by decide  
  f := ![![![121, -6, 0], ![474, 0, 0]], ![![101, -5, 0], ![396, 0, 0]], ![![126, -6, 0], ![494, 1, 0]]]
  g := ![![![1, 0, 0], ![-59, 79, 0], ![-74, 0, 79]], ![![-1, 1, 0], ![14, -20, 1], ![-26, 64, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![9, 1, 0]] ![![79, 0, 0], ![11, 1, 0]]
  ![![79, 0, 0], ![-59, 20, 1]] where
 M := ![![![6241, 0, 0], ![869, 79, 0]], ![![711, 79, 0], ![99, 20, 1]]]
 hmul := by decide  
 g := ![![![![79, 0, 0], ![0, 0, 0]], ![![11, 1, 0], ![0, 0, 0]]], ![![![9, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-59, 20, 1]] ![![79, 0, 0], ![-20, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-1580, 79, 0]], ![![-4661, 1580, 79], ![1422, -395, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-20, 1, 0]]], ![![![-59, 20, 1]], ![![18, -5, 0]]]]
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


lemma PB207I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB207I1 : PrimesBelowBoundCertificateInterval O 31 79 207 where
  m := 11
  g := ![3, 3, 2, 2, 2, 3, 3, 1, 2, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB207I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N1]
    · exact ![I61N0, I61N1, I61N1]
    · exact ![I67N0]
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
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![61, 61, 61]
    · exact ![300763]
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
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
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
  β := ![I37N0, I37N1, I41N0, I41N1, I41N2, I43N1, I47N1, I53N1, I59N0, I59N1, I61N0, I61N1, I71N1, I73N1, I79N0, I79N1, I79N2]
  Il := ![[I37N0, I37N1, I37N1], [I41N0, I41N1, I41N2], [I43N1], [I47N1], [I53N1], [I59N0, I59N1, I59N1], [I61N0, I61N1, I61N1], [], [I71N1], [I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
