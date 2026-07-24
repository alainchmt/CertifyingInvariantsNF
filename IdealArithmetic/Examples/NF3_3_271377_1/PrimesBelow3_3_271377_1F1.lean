
import IdealArithmetic.Examples.NF3_3_271377_1.RI3_3_271377_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27889, 26748, 5400]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![27889, 26748, 5400]] 
 ![![37, 0, 0], ![0, 37, 0], ![23, 20, 1]] where
  M :=![![![27889, 26748, 5400], ![248400, 238237, 48096], ![982008, 941832, 190141]]]
  hmulB := by decide  
  f := ![![![7285, 36, -216]], ![![-9936, -23, 288]], ![![-529, 8, 13]]]
  g := ![![![-2603, -2196, 5400], ![-23184, -19559, 48096], ![-91655, -77324, 190141]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [23, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 36], [0, 1]]
 g := ![![[28, 9], [1], [2, 34], [3], [1]], ![[4, 28], [1], [10, 3], [3], [1]]]
 h' := ![![[22, 36], [21, 3], [28, 36], [16, 16], [14, 22], [0, 1]], ![[0, 1], [13, 34], [6, 1], [35, 21], [17, 15], [22, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [1, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [23, 15, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![161, 436, 266]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-161, -132, 266]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7285, 36, -216]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![7285, 36, -216]] 
 ![![37, 0, 0], ![35, 1, 0], ![36, 0, 1]] where
  M :=![![![7285, 36, -216], ![-9936, -23, 288], ![11592, -72, -311]]]
  hmulB := by decide  
  f := ![![![27889, 26748, 5400]], ![![33095, 31741, 6408]], ![![53676, 51480, 10393]]]
  g := ![![![373, 36, -216], ![-527, -23, 288], ![684, -72, -311]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![27889, 26748, 5400]] ![![7285, 36, -216]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [40, 36, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 29, 25], [14, 11, 16], [0, 1]]
 g := ![![[13, 23, 9], [15, 10], [35, 5], [37, 27, 1], []], ![[17, 8, 30, 16], [38, 16], [22, 40], [13, 20, 12, 32], [39, 10]], ![[6, 25, 17, 2], [10, 21], [24, 33], [23, 9, 31, 8], [7, 10]]]
 h' := ![![[13, 29, 25], [33, 23, 38], [10, 1, 16], [37, 7, 28], [0, 0, 1], [0, 1]], ![[14, 11, 16], [36, 4, 9], [30, 39, 37], [7, 36, 32], [3, 16, 11], [13, 29, 25]], ![[0, 1], [33, 14, 35], [33, 1, 29], [38, 39, 22], [39, 25, 29], [14, 11, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 17], []]
 b := ![[], [32, 10, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [40, 36, 14, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12587, 86387, 80934]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-307, 2107, 1974]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [16, 2, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 36, 32], [1, 6, 11], [0, 1]]
 g := ![![[11, 22, 38], [15, 36, 25], [40, 15], [7, 40, 1], []], ![[40, 6, 4, 18], [14, 32, 7, 28], [0, 1], [2, 15, 33, 34], [6, 35]], ![[23, 20, 10, 11], [27, 24, 16, 6], [8, 35], [3, 41, 10, 23], [27, 35]]]
 h' := ![![[39, 36, 32], [18, 2, 34], [36, 19, 38], [17, 34, 12], [0, 0, 1], [0, 1]], ![[1, 6, 11], [42, 29, 10], [16, 39, 19], [39, 20, 42], [6, 0, 6], [39, 36, 32]], ![[0, 1], [29, 12, 42], [17, 28, 29], [39, 32, 32], [42, 0, 36], [1, 6, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 9], []]
 b := ![[], [4, 3, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [16, 2, 3, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-239940, -1548, -19694]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5580, -36, -458]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-783, -10, 22]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-783, -10, 22]] 
 ![![47, 0, 0], ![0, 47, 0], ![5, 38, 1]] where
  M :=![![![-783, -10, 22], ![1012, -45, -42], ![-1472, -208, -3]]]
  hmulB := by decide  
  f := ![![![183, 98, -30]], ![![-1380, -739, 226]], ![![-971, -520, 159]]]
  g := ![![![-19, -18, 22], ![26, 33, -42], ![-31, -2, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [41, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 46], [0, 1]]
 g := ![![[15, 25], [45, 36], [32, 21], [29, 16], [1]], ![[9, 22], [42, 11], [42, 26], [12, 31], [1]]]
 h' := ![![[43, 46], [35, 5], [4, 6], [33, 16], [6, 43], [0, 1]], ![[0, 1], [15, 42], [27, 41], [16, 31], [22, 4], [43, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [14, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [41, 4, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![179, 458, 299]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28, -232, 299]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-183, -98, 30]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-183, -98, 30]] 
 ![![47, 0, 0], ![19, 1, 0], ![45, 0, 1]] where
  M :=![![![-183, -98, 30], ![1380, 739, -226], ![-5888, -3152, 965]]]
  hmulB := by decide  
  f := ![![![783, 10, -22]], ![![295, 5, -8]], ![![781, 14, -21]]]
  g := ![![![7, -98, 30], ![-53, 739, -226], ![225, -3152, 965]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-783, -10, 22]] ![![-183, -98, 30]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5437, -30, 162]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-5437, -30, 162]] 
 ![![53, 0, 0], ![6, 1, 0], ![32, 0, 1]] where
  M :=![![![-5437, -30, 162], ![7452, 41, -222], ![-8832, -48, 263]]]
  hmulB := by decide  
  f := ![![![127, 114, 18]], ![![30, 29, 6]], ![![160, 144, 23]]]
  g := ![![![-197, -30, 162], ![270, 41, -222], ![-320, -48, 263]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-193, 0, 6]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-193, 0, 6]] 
 ![![53, 0, 0], ![22, 1, 0], ![12, 0, 1]] where
  M :=![![![-193, 0, 6], ![276, 11, -6], ![-276, 36, 17]]]
  hmulB := by decide  
  f := ![![![403, 216, -66]], ![![110, 59, -18]], ![![336, 180, -55]]]
  g := ![![![-5, 0, 6], ![2, 11, -6], ![-24, 36, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1159, 618, -192]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![1159, 618, -192]] 
 ![![53, 0, 0], ![25, 1, 0], ![46, 0, 1]] where
  M :=![![![1159, 618, -192], ![-8832, -4751, 1428], ![37260, 19860, -6179]]]
  hmulB := by decide  
  f := ![![![-996349, -5502, 29688]], ![![-444209, -2453, 13236]], ![![-895298, -4944, 26677]]]
  g := ![![![-103, 618, -192], ![835, -4751, 1428], ![-3302, 19860, -6179]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-5437, -30, 162]] ![![-193, 0, 6]]
  ![![996349, 5502, -29688]] where
 M := ![![![996349, 5502, -29688]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![996349, 5502, -29688]] ![![1159, 618, -192]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [22, 36, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 33, 52], [42, 25, 7], [0, 1]]
 g := ![![[11, 36, 3], [38, 30, 51], [1, 45], [50, 50, 57], [1]], ![[58, 32, 45, 10], [10, 54, 4, 42], [49, 17], [35, 49, 5, 58], [45, 17, 55, 11]], ![[58, 38, 19, 46], [51, 11, 21, 46], [56, 16], [12, 44, 28, 35], [46, 33, 34, 48]]]
 h' := ![![[53, 33, 52], [49, 14, 48], [6, 44, 13], [21, 3, 35], [37, 23, 36], [0, 1]], ![[42, 25, 7], [6, 29, 40], [10, 6, 17], [12, 50, 28], [33, 36, 31], [53, 33, 52]], ![[0, 1], [53, 16, 30], [34, 9, 29], [26, 6, 55], [34, 0, 51], [42, 25, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 49], []]
 b := ![[], [27, 32, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [22, 36, 23, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30300512, 36797710, 12395428]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![513568, 623690, 210092]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [3, 22, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 35, 22], [24, 25, 39], [0, 1]]
 g := ![![[47, 46, 39], [17, 3], [57, 25, 27], [39, 27, 25], [1]], ![[7, 39, 9, 12], [21, 5], [51, 48, 10, 49], [11, 54, 34, 41], [19, 24, 55, 34]], ![[59, 9, 59, 42], [15, 19], [44, 24, 56, 22], [42, 40, 21, 4], [55, 48, 18, 27]]]
 h' := ![![[42, 35, 22], [32, 41, 51], [12, 38, 53], [5, 46, 24], [58, 39, 5], [0, 1]], ![[24, 25, 39], [7, 34, 42], [3, 14, 26], [42, 7, 26], [38, 22, 7], [42, 35, 22]], ![[0, 1], [25, 47, 29], [58, 9, 43], [47, 8, 11], [56, 0, 49], [24, 25, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 57], []]
 b := ![[], [0, 34, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [3, 22, 56, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15860, 15982, 3843]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![260, 262, 63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18449, 17694, 3572]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![18449, 17694, 3572]] 
 ![![67, 0, 0], ![0, 67, 0], ![49, 29, 1]] where
  M :=![![![18449, 17694, 3572], ![164312, 157591, 31816], ![649612, 623028, 125775]]]
  hmulB := by decide  
  f := ![![![-18669, -102, 556]], ![![25576, 133, -760]], ![![-3035, -19, 91]]]
  g := ![![![-2337, -1282, 3572], ![-20816, -11419, 31816], ![-82289, -45141, 125775]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [3, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 66], [0, 1]]
 g := ![![[56, 19], [11, 24], [9], [47], [17], [1]], ![[13, 48], [66, 43], [9], [47], [17], [1]]]
 h' := ![![[33, 66], [34, 32], [64, 52], [15, 3], [25, 28], [64, 33], [0, 1]], ![[0, 1], [18, 35], [38, 15], [47, 64], [11, 39], [14, 34], [33, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [20, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [3, 34, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![233, 1281, 1033]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-752, -428, 1033]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18669, -102, 556]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-18669, -102, 556]] 
 ![![67, 0, 0], ![10, 1, 0], ![12, 0, 1]] where
  M :=![![![-18669, -102, 556], ![25576, 133, -760], ![-30268, -132, 893]]]
  hmulB := by decide  
  f := ![![![18449, 17694, 3572]], ![![5206, 4993, 1008]], ![![13000, 12468, 2517]]]
  g := ![![![-363, -102, 556], ![498, 133, -760], ![-592, -132, 893]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![18449, 17694, 3572]] ![![-18669, -102, 556]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [50, 53, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 53, 68], [41, 17, 3], [0, 1]]
 g := ![![[53, 51, 40], [37, 35, 64], [59, 34, 9], [36, 27], [18, 1], []], ![[49, 43, 37, 63], [47, 1, 1, 51], [31, 3, 27, 14], [11, 58], [43, 5], [57, 9]], ![[42, 43, 1, 5], [62, 49, 63, 37], [65, 12, 57, 24], [26, 10], [2, 40], [51, 9]]]
 h' := ![![[48, 53, 68], [67, 11, 18], [32, 50, 8], [7, 45, 68], [23, 61, 58], [0, 0, 1], [0, 1]], ![[41, 17, 3], [68, 11, 60], [52, 37, 57], [42, 19, 27], [38, 33, 22], [22, 55, 17], [48, 53, 68]], ![[0, 1], [70, 49, 64], [29, 55, 6], [57, 7, 47], [47, 48, 62], [54, 16, 53], [41, 17, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 57], []]
 b := ![[], [30, 53, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [50, 53, 53, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-933792, -964464, -238418]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13152, -13584, -3358]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [57, 39, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 17, 47], [63, 55, 26], [0, 1]]
 g := ![![[53, 63, 3], [49, 18], [61, 70], [53, 6, 32], [35, 1], []], ![[16, 20, 64, 59], [17, 57], [1, 41], [66, 9, 69, 42], [66, 32], [0, 19]], ![[10, 26, 62, 53], [46, 6], [52, 64], [31, 41, 20, 34], [27, 70], [21, 19]]]
 h' := ![![[45, 17, 47], [45, 1, 52], [8, 65, 50], [45, 65, 17], [49, 38, 18], [0, 0, 1], [0, 1]], ![[63, 55, 26], [51, 47, 60], [12, 22, 38], [19, 17, 48], [30, 5, 2], [54, 9, 55], [45, 17, 47]], ![[0, 1], [4, 25, 34], [61, 59, 58], [18, 64, 8], [71, 30, 53], [71, 64, 17], [63, 55, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 65], []]
 b := ![[], [6, 57, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [57, 39, 38, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4307, 876, 5402]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![59, 12, 74]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3291, -18, 98]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-3291, -18, 98]] 
 ![![79, 0, 0], ![0, 79, 0], ![43, 24, 1]] where
  M :=![![![-3291, -18, 98], ![4508, 23, -134], ![-5336, -24, 157]]]
  hmulB := by decide  
  f := ![![![-5, -6, -2]], ![![-92, -79, -10]], ![![-33, -30, -5]]]
  g := ![![![-95, -30, 98], ![130, 41, -134], ![-153, -48, 157]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [63, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 78], [0, 1]]
 g := ![![[24, 1], [31, 55], [76, 10], [75, 23], [42], [1]], ![[13, 78], [58, 24], [45, 69], [59, 56], [42], [1]]]
 h' := ![![[68, 78], [22, 78], [31, 23], [15, 22], [59, 55], [16, 68], [0, 1]], ![[0, 1], [33, 1], [15, 56], [10, 57], [7, 24], [58, 11], [68, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [23, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [63, 11, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1179, 2216, 1172]
  a := ![1, -5, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-623, -328, 1172]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 6, 2]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![5, 6, 2]] 
 ![![79, 0, 0], ![32, 1, 0], ![25, 0, 1]] where
  M :=![![![5, 6, 2], ![92, 79, 10], ![184, 216, 69]]]
  hmulB := by decide  
  f := ![![![3291, 18, -98]], ![![1276, 7, -38]], ![![1109, 6, -33]]]
  g := ![![![-3, 6, 2], ![-34, 79, 10], ![-107, 216, 69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-3291, -18, 98]] ![![5, 6, 2]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB116I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB116I1 : PrimesBelowBoundCertificateInterval O 31 79 116 where
  m := 11
  g := ![2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB116I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0]
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
    · exact ![68921]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![357911]
    · exact ![389017]
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
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I47N1, I53N0, I53N1, I53N2, I67N1, I79N1]
  Il := ![[I37N1], [], [], [I47N1], [I53N0, I53N1, I53N2], [], [], [I67N1], [], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
