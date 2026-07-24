
import IdealArithmetic.Examples.NF3_1_125083_1.RI3_1_125083_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-5, -15, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-5, -15, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![32, 22, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-5, -15, 1], ![70, -12, -14], ![-980, 168, -26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -22, 37]], ![![-1, -1, 1], ![14, 8, -14], ![-4, 20, -26]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [19, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 36], [0, 1]]
 g := ![![[19, 25], [25], [30, 30], [7], [1]], ![[22, 12], [25], [4, 7], [7], [1]]]
 h' := ![![[9, 36], [9, 5], [22, 32], [6, 17], [18, 9], [0, 1]], ![[0, 1], [17, 32], [14, 5], [11, 20], [25, 28], [9, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [24, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [19, 28, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![229, 21, -31]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![33, 19, -31]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![14, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![14, 1, 0]] 
 ![![37, 0, 0], ![14, 1, 0], ![26, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![14, 1, 0], ![0, 14, 1], ![70, -7, 15]]]
  hmulB := by decide  
  f := ![![![85, 6, 0], ![-222, 0, 0]], ![![14, 1, 0], ![-36, 0, 0]], ![![62, 4, 0], ![-162, 1, 0]]]
  g := ![![![1, 0, 0], ![-14, 37, 0], ![-26, 0, 37]], ![![0, 1, 0], ![-6, 14, 1], ![-6, -7, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-5, -15, 1]] ![![37, 0, 0], ![14, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![518, 37, 0]], ![![-185, -555, 37], ![0, -222, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![14, 1, 0]]], ![![![-5, -15, 1]], ![![0, -6, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![9, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![9, 1, 0]] 
 ![![41, 0, 0], ![9, 1, 0], ![1, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![9, 1, 0], ![0, 9, 1], ![70, -7, 10]]]
  hmulB := by decide  
  f := ![![![181, 20, 0], ![-820, 0, 0]], ![![27, 3, 0], ![-122, 0, 0]], ![![-7, -1, 0], ![32, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 41, 0], ![-1, 0, 41]], ![![0, 1, 0], ![-2, 9, 1], ![3, -7, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![11, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![11, 1, 0]] 
 ![![41, 0, 0], ![11, 1, 0], ![2, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![11, 1, 0], ![0, 11, 1], ![70, -7, 12]]]
  hmulB := by decide  
  f := ![![![122, 11, 0], ![-451, 0, 0]], ![![22, 2, 0], ![-81, 0, 0]], ![![-8, -1, 0], ![30, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 41, 0], ![-2, 0, 41]], ![![0, 1, 0], ![-3, 11, 1], ![3, -7, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2063, -327, -114]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-2063, -327, -114]] 
 ![![41, 0, 0], ![20, 1, 0], ![10, 0, 1]] where
  M :=![![![-2063, -327, -114], ![-7980, -1265, -441], ![-30870, -4893, -1706]]]
  hmulB := by decide  
  f := ![![![-277, 60, 3]], ![![-130, 22, 3]], ![![40, 9, -5]]]
  g := ![![![137, -327, -114], ![530, -1265, -441], ![2050, -4893, -1706]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![9, 1, 0]] ![![41, 0, 0], ![11, 1, 0]]
  ![![-277, 60, 3]] where
 M := ![![![1681, 0, 0], ![451, 41, 0]], ![![369, 41, 0], ![99, 20, 1]]]
 hmul := by decide  
 g := ![![![![-84583, -13407, -4674]], ![![-30673, -4862, -1695]]], ![![![-26547, -4208, -1467]], ![![-9627, -1526, -532]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-277, 60, 3]] ![![-2063, -327, -114]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [33, 39, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 11, 33], [23, 31, 10], [0, 1]]
 g := ![![[32, 2, 36], [14, 31, 40], [19, 1], [5, 42, 1], []], ![[22, 11, 40, 37], [40, 15, 36, 5], [16, 31], [22, 19, 24, 22], [24, 14]], ![[22, 14, 25, 9], [11, 34, 12, 35], [20, 23], [14, 21, 2, 6], [4, 14]]]
 h' := ![![[19, 11, 33], [11, 39, 6], [24, 11, 13], [7, 10, 1], [0, 0, 1], [0, 1]], ![[23, 31, 10], [15, 10, 11], [5, 23, 35], [24, 33, 17], [42, 9, 31], [19, 11, 33]], ![[0, 1], [22, 37, 26], [20, 9, 38], [32, 0, 25], [10, 34, 11], [23, 31, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 24], []]
 b := ![[], [19, 17, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [33, 39, 1, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![132784, -27219, 1505]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3088, -633, 35]
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

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![557, 297, -114]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![557, 297, -114]] 
 ![![47, 0, 0], ![0, 47, 0], ![45, 11, 1]] where
  M :=![![![557, 297, -114], ![-7980, 1355, 183], ![12810, -9261, 1538]]]
  hmulB := by decide  
  f := ![![![-80399, -12744, -4443]], ![![-311010, -49298, -17187]], ![![-175365, -27797, -9691]]]
  g := ![![![121, 33, -114], ![-345, -14, 183], ![-1200, -557, 1538]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [43, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 46], [0, 1]]
 g := ![![[28, 14], [3, 12], [29, 32], [7, 42], [1]], ![[45, 33], [31, 35], [41, 15], [11, 5], [1]]]
 h' := ![![[18, 46], [12, 22], [22, 24], [28, 28], [4, 18], [0, 1]], ![[0, 1], [32, 25], [31, 23], [15, 19], [46, 29], [18, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [23, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [43, 29, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2213, -22, 92]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-41, -22, 92]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-80399, -12744, -4443]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-80399, -12744, -4443]] 
 ![![47, 0, 0], ![35, 1, 0], ![44, 0, 1]] where
  M :=![![![-80399, -12744, -4443], ![-311010, -49298, -17187], ![-1203090, -190701, -66485]]]
  hmulB := by decide  
  f := ![![![557, 297, -114]], ![![245, 250, -81]], ![![794, 81, -74]]]
  g := ![![![11939, -12744, -4443], ![46184, -49298, -17187], ![178655, -190701, -66485]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![557, 297, -114]] ![![-80399, -12744, -4443]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![24, 24, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![24, 24, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![24, 24, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![24, 24, 1], ![70, 17, 25], ![1750, -105, 42]]]
  hmulB := by decide  
  f := ![![![-23, -24, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -24, 53]], ![![0, 0, 1], ![-10, -11, 25], ![14, -21, 42]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [29, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 52], [0, 1]]
 g := ![![[17, 11], [15], [43, 13], [13], [37, 1]], ![[0, 42], [15], [47, 40], [13], [21, 52]]]
 h' := ![![[37, 52], [31, 45], [25, 11], [4, 38], [40, 15], [0, 1]], ![[0, 1], [0, 8], [8, 42], [32, 15], [12, 38], [37, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [12, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [29, 16, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![256, 627, -113]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![56, 63, -113]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-25, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-25, 1, 0]] 
 ![![53, 0, 0], ![28, 1, 0], ![11, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-25, 1, 0], ![0, -25, 1], ![70, -7, -24]]]
  hmulB := by decide  
  f := ![![![676, -27, 0], ![1431, 0, 0]], ![![376, -15, 0], ![796, 0, 0]], ![![162, -6, 0], ![343, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 53, 0], ![-11, 0, 53]], ![![-1, 1, 0], ![13, -25, 1], ![10, -7, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![24, 24, 1]] ![![53, 0, 0], ![-25, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1325, 53, 0]], ![![1272, 1272, 53], ![-530, -583, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-25, 1, 0]]], ![![![24, 24, 1]], ![![-10, -11, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![33, 19, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![33, 19, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![33, 19, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![33, 19, 1], ![70, 26, 20], ![1400, -70, 46]]]
  hmulB := by decide  
  f := ![![![-32, -19, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -19, 59]], ![![0, 0, 1], ![-10, -6, 20], ![-2, -16, 46]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [23, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 58], [0, 1]]
 g := ![![[12, 36], [5, 41], [46], [27, 20], [19, 1]], ![[47, 23], [17, 18], [46], [53, 39], [38, 58]]]
 h' := ![![[19, 58], [3, 6], [21, 49], [28, 39], [35, 43], [0, 1]], ![[0, 1], [58, 53], [8, 10], [2, 20], [26, 16], [19, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [56, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [23, 40, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![233, 9, -43]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![28, 14, -43]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-20, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-20, 1, 0]] 
 ![![59, 0, 0], ![39, 1, 0], ![13, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-20, 1, 0], ![0, -20, 1], ![70, -7, -19]]]
  hmulB := by decide  
  f := ![![![101, -5, 0], ![295, 0, 0]], ![![81, -4, 0], ![237, 0, 0]], ![![27, -1, 0], ![79, 1, 0]]]
  g := ![![![1, 0, 0], ![-39, 59, 0], ![-13, 0, 59]], ![![-1, 1, 0], ![13, -20, 1], ![10, -7, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![33, 19, 1]] ![![59, 0, 0], ![-20, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1180, 59, 0]], ![![1947, 1121, 59], ![-590, -354, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-20, 1, 0]]], ![![![33, 19, 1]], ![![-10, -6, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1339, -212, -74]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-1339, -212, -74]] 
 ![![61, 0, 0], ![0, 61, 0], ![42, 21, 1]] where
  M :=![![![-1339, -212, -74], ![-5180, -821, -286], ![-20020, -3178, -1107]]]
  hmulB := by decide  
  f := ![![![1, -8, 2]], ![![140, -13, -6]], ![![42, -7, -1]]]
  g := ![![![29, 22, -74], ![112, 85, -286], ![434, 329, -1107]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [5, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 60], [0, 1]]
 g := ![![[8, 49], [14], [21, 4], [55, 20], [21, 1]], ![[0, 12], [14], [44, 57], [48, 41], [42, 60]]]
 h' := ![![[21, 60], [36, 7], [17, 40], [30, 2], [17, 9], [0, 1]], ![[0, 1], [0, 54], [3, 21], [11, 59], [23, 52], [21, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [27, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [5, 40, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2776, 595, 435]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-254, -140, 435]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 8, -2]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-1, 8, -2]] 
 ![![61, 0, 0], ![39, 1, 0], ![4, 0, 1]] where
  M :=![![![-1, 8, -2], ![-140, 13, 6], ![420, -182, 19]]]
  hmulB := by decide  
  f := ![![![1339, 212, 74]], ![![941, 149, 52]], ![![416, 66, 23]]]
  g := ![![![-5, 8, -2], ![-11, 13, 6], ![122, -182, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-1339, -212, -74]] ![![-1, 8, -2]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [56, 16, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 10, 52], [37, 56, 15], [0, 1]]
 g := ![![[10, 7, 24], [47, 22, 26], [15, 62], [21, 26], [13, 1], []], ![[11, 60, 37, 18], [26, 29, 59, 31], [51, 24], [27, 1], [30, 54], [12, 24]], ![[0, 61, 49, 10], [22, 20, 7, 33], [32, 1], [17, 56], [13, 33], [49, 24]]]
 h' := ![![[43, 10, 52], [48, 66, 52], [24, 33, 48], [44, 22, 14], [9, 4, 19], [0, 0, 1], [0, 1]], ![[37, 56, 15], [38, 13, 46], [51, 42, 49], [48, 2, 52], [32, 60, 66], [38, 61, 56], [43, 10, 52]], ![[0, 1], [0, 55, 36], [34, 59, 37], [33, 43, 1], [28, 3, 49], [32, 6, 10], [37, 56, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 41], []]
 b := ![[], [17, 10, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [56, 16, 54, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25527, 5025, 469]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-381, 75, 7]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [23, 18, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 6, 66], [64, 64, 5], [0, 1]]
 g := ![![[44, 16, 20], [48, 14, 32], [20, 25, 45], [38, 30], [46, 1], []], ![[27, 5, 25, 46], [62, 10, 17, 69], [63, 16, 30, 13], [16, 36], [32, 49], [25, 25]], ![[13, 69, 0, 25], [46, 20, 41, 8], [69, 32, 4, 49], [0, 37], [5, 36], [15, 25]]]
 h' := ![![[53, 6, 66], [32, 41, 34], [37, 7, 48], [27, 60, 51], [7, 1, 39], [0, 0, 1], [0, 1]], ![[64, 64, 5], [61, 13, 54], [4, 43, 55], [62, 46, 53], [69, 29, 6], [33, 37, 64], [53, 6, 66]], ![[0, 1], [47, 17, 54], [51, 21, 39], [60, 36, 38], [29, 41, 26], [59, 34, 6], [64, 64, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 56], []]
 b := ![[], [2, 60, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [23, 18, 25, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41393, 781, 1562]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![583, 11, 22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-10, -8, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-10, -8, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![63, 65, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-10, -8, 1], ![70, -17, -7], ![-490, 119, -24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-63, -65, 73]], ![![-1, -1, 1], ![7, 6, -7], ![14, 23, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [12, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 72], [0, 1]]
 g := ![![[41, 67], [23], [57], [23, 3], [69], [1]], ![[0, 6], [23], [57], [7, 70], [69], [1]]]
 h' := ![![[19, 72], [43, 40], [10, 13], [16, 35], [46, 52], [61, 19], [0, 1]], ![[0, 1], [0, 33], [38, 60], [24, 38], [12, 21], [57, 54], [19, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [60, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [12, 54, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2396, -48, 152]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-164, -136, 152]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![7, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![7, 1, 0]] 
 ![![73, 0, 0], ![7, 1, 0], ![24, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![7, 1, 0], ![0, 7, 1], ![70, -7, 8]]]
  hmulB := by decide  
  f := ![![![134, 19, 0], ![-1387, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![36, 5, 0], ![-372, 1, 0]]]
  g := ![![![1, 0, 0], ![-7, 73, 0], ![-24, 0, 73]], ![![0, 1, 0], ![-1, 7, 1], ![-1, -7, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-10, -8, 1]] ![![73, 0, 0], ![7, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![511, 73, 0]], ![![-730, -584, 73], ![0, -73, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![7, 1, 0]]], ![![![-10, -8, 1]], ![![0, -1, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -2, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![9, -2, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![9, 77, 1]] where
  M :=![![![9, -2, 1], ![70, 2, -1], ![-70, 77, 1]]]
  hmulB := by decide  
  f := ![![![1, 1, 0]], ![![0, 1, 1]], ![![1, 1, 1]]]
  g := ![![![0, -1, 1], ![1, 1, -1], ![-1, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [33, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 78], [0, 1]]
 g := ![![[38, 2], [67, 46], [57, 76], [41, 23], [21], [1]], ![[58, 77], [53, 33], [27, 3], [34, 56], [21], [1]]]
 h' := ![![[10, 78], [1, 9], [15, 58], [69, 47], [1, 24], [46, 10], [0, 1]], ![[0, 1], [12, 70], [42, 21], [65, 32], [4, 55], [67, 69], [10, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [54, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [33, 69, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1029, -18, 88]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, -86, 88]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![1, 1, 0]] 
 ![![79, 0, 0], ![1, 1, 0], ![78, 0, 1]] where
  M :=![![![1, 1, 0], ![0, 1, 1], ![70, -7, 2]]]
  hmulB := by decide  
  f := ![![![9, -2, 1]], ![![1, 0, 0]], ![![8, -1, 1]]]
  g := ![![![0, 1, 0], ![-1, 1, 1], ![-1, -7, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![9, -2, 1]] ![![1, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB101I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB101I1 : PrimesBelowBoundCertificateInterval O 31 79 101 where
  m := 11
  g := ![2, 3, 1, 2, 2, 2, 2, 1, 1, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB101I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0]
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
    · exact ![1369, 37]
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![357911]
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
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N0, I41N1, I41N2, I47N1, I53N1, I59N1, I61N1, I73N1, I79N1]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [], [I47N1], [I53N1], [I59N1], [I61N1], [], [], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
