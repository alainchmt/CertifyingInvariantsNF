
import IdealArithmetic.Examples.NF3_1_83820_3.RI3_1_83820_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-30, -13, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-30, -13, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![7, 24, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-30, -13, 1], ![-101, -8, -25], ![1111, -319, -21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -24, 37]], ![![-1, -1, 1], ![2, 16, -25], ![34, 5, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [2, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 36], [0, 1]]
 g := ![![[5, 11], [7], [27, 4], [26], [1]], ![[6, 26], [7], [24, 33], [26], [1]]]
 h' := ![![[27, 36], [16, 14], [20, 28], [26, 2], [35, 27], [0, 1]], ![[0, 1], [24, 23], [36, 9], [6, 35], [24, 10], [27, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [20, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [2, 10, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-490, -52, 78]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28, -52, 78]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-12, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-12, 1, 0]] 
 ![![37, 0, 0], ![25, 1, 0], ![21, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-12, 1, 0], ![1, -12, 2], ![-88, 22, -11]]]
  hmulB := by decide  
  f := ![![![-2, 179, -30], ![37, 555, 0]], ![![3, 119, -20], ![38, 370, 0]], ![![-6, 102, -17], ![6, 315, 0]]]
  g := ![![![1, 0, 0], ![-25, 37, 0], ![-21, 0, 37]], ![![-1, 1, 0], ![7, -12, 2], ![-11, 22, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-30, -13, 1]] ![![37, 0, 0], ![-12, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-444, 37, 0]], ![![-1110, -481, 37], ![259, 148, -37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-12, 1, 0]]], ![![![-30, -13, 1]], ![![7, 4, -1]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [29, 21, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 36, 35], [40, 4, 6], [0, 1]]
 g := ![![[29, 30, 20], [5, 39], [30, 25], [12, 19, 1], []], ![[14, 31, 29, 34], [20, 25], [], [35, 20, 19, 27], [6, 36]], ![[12, 4, 21, 34], [16, 36], [11, 25], [15, 23, 3, 27], [35, 36]]]
 h' := ![![[20, 36, 35], [11, 39, 26], [22, 15, 11], [21, 17, 5], [0, 0, 1], [0, 1]], ![[40, 4, 6], [25, 19, 34], [20, 25, 36], [15, 35], [21, 24, 4], [20, 36, 35]], ![[0, 1], [12, 24, 22], [5, 1, 35], [18, 30, 36], [11, 17, 36], [40, 4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 21], []]
 b := ![[], [39, 12, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [29, 21, 22, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![591507, -289132, 77203]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14427, -7052, 1883]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-10, 16, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-10, 16, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![33, 16, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-10, 16, 1], ![-72, 12, 33], ![-1441, 319, 28]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -16, 43]], ![![-1, 0, 1], ![-27, -12, 33], ![-55, -3, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [42, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 42], [0, 1]]
 g := ![![[29, 36], [5, 9], [16], [23, 24], [1]], ![[41, 7], [8, 34], [16], [31, 19], [1]]]
 h' := ![![[29, 42], [5, 6], [29, 3], [23, 4], [1, 29], [0, 1]], ![[0, 1], [7, 37], [30, 40], [10, 39], [25, 14], [29, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [21, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [42, 14, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-128774, -146768, 103358]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-82316, -41872, 103358]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![10, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![10, 1, 0]] 
 ![![43, 0, 0], ![10, 1, 0], ![15, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![10, 1, 0], ![1, 10, 2], ![-88, 22, 11]]]
  hmulB := by decide  
  f := ![![![-346, -3767, -754], ![-129, 16211, 0]], ![![-87, -870, -174], ![1, 3741, 0]], ![![-120, -1314, -263], ![-48, 5655, 0]]]
  g := ![![![1, 0, 0], ![-10, 43, 0], ![-15, 0, 43]], ![![0, 1, 0], ![-3, 10, 2], ![-11, 22, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-10, 16, 1]] ![![43, 0, 0], ![10, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![430, 43, 0]], ![![-430, 688, 43], ![-172, 172, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![10, 1, 0]]], ![![![-10, 16, 1]], ![![-4, 4, 1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [39, 35, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 33, 44], [24, 13, 3], [0, 1]]
 g := ![![[10, 0, 27], [39, 24, 18], [13, 15, 18], [18, 10, 1], []], ![[12, 39, 12, 40], [7, 25, 35, 15], [29, 44, 12, 23], [42, 19, 26, 10], [33, 9]], ![[26, 36, 6, 18], [23, 2, 42, 27], [17, 14, 9, 6], [43, 3, 16, 24], [27, 9]]]
 h' := ![![[33, 33, 44], [30, 8, 36], [10, 3, 21], [3, 14, 26], [0, 0, 1], [0, 1]], ![[24, 13, 3], [28, 16, 21], [40, 17, 29], [17, 27, 14], [37, 14, 13], [33, 33, 44]], ![[0, 1], [17, 23, 37], [29, 27, 44], [16, 6, 7], [40, 33, 33], [24, 13, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 5], []]
 b := ![[], [7, 12, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [39, 35, 37, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-417266, 183864, -38916]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8878, 3912, -828]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![6, -23, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![6, -23, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![6, 30, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![6, -23, 1], ![-111, 28, -45], ![1991, -539, 5]]]
  hmulB := by decide  
  f := ![![![-5, 23, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -30, 53]], ![![0, -1, 1], ![3, 26, -45], ![37, -13, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [2, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 52], [0, 1]]
 g := ![![[10, 7], [52], [15, 6], [40], [33, 1]], ![[29, 46], [52], [1, 47], [40], [13, 52]]]
 h' := ![![[33, 52], [1, 22], [23, 30], [36, 35], [40, 27], [0, 1]], ![[0, 1], [38, 31], [6, 23], [25, 18], [30, 26], [33, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [47, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [2, 20, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-500, -62, 58]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16, -34, 58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-8, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-8, 1, 0]] 
 ![![53, 0, 0], ![45, 1, 0], ![48, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-8, 1, 0], ![1, -8, 2], ![-88, 22, -7]]]
  hmulB := by decide  
  f := ![![![-685, 5803, -1452], ![265, 38478, 0]], ![![-583, 4924, -1232], ![213, 32648, 0]], ![![-624, 5256, -1315], ![216, 34848, 0]]]
  g := ![![![1, 0, 0], ![-45, 53, 0], ![-48, 0, 53]], ![![-1, 1, 0], ![5, -8, 2], ![-14, 22, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![6, -23, 1]] ![![53, 0, 0], ![-8, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-424, 53, 0]], ![![318, -1219, 53], ![-159, 212, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-8, 1, 0]]], ![![![6, -23, 1]], ![![-3, 4, -1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![0, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![0, 1, 0]] 
 ![![59, 0, 0], ![0, 1, 0], ![30, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![0, 1, 0], ![1, 0, 2], ![-88, 22, 1]]]
  hmulB := by decide  
  f := ![![![0, 0, -2], ![0, 59, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 30, 0]]]
  g := ![![![1, 0, 0], ![0, 59, 0], ![-30, 0, 59]], ![![0, 1, 0], ![-1, 0, 2], ![-2, 22, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![28, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![28, 1, 0]] 
 ![![59, 0, 0], ![28, 1, 0], ![51, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![28, 1, 0], ![1, 28, 2], ![-88, 22, 29]]]
  hmulB := by decide  
  f := ![![![539, 24460, 1748], ![708, -51566, 0]], ![![246, 11586, 828], ![355, -24426, 0]], ![![455, 21143, 1511], ![635, -44574, 0]]]
  g := ![![![1, 0, 0], ![-28, 59, 0], ![-51, 0, 59]], ![![0, 1, 0], ![-15, 28, 2], ![-37, 22, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77308, -28385, 6487]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![77308, -28385, 6487]] 
 ![![59, 0, 0], ![30, 1, 0], ![52, 0, 1]] where
  M :=![![![77308, -28385, 6487], ![-599241, 220022, -50283], ![2283809, -838541, 191637]]]
  hmulB := by decide  
  f := ![![![-1089, 778, 241]], ![![-900, 467, 153]], ![![-2255, 841, 297]]]
  g := ![![![10026, -28385, 6487], ![-77715, 220022, -50283], ![296185, -838541, 191637]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![0, 1, 0]] ![![59, 0, 0], ![28, 1, 0]]
  ![![-1089, 778, 241]] where
 M := ![![![3481, 0, 0], ![1652, 59, 0]], ![![0, 59, 0], ![1, 28, 2]]]
 hmul := by decide  
 g := ![![![![4561172, -1674715, 382733]], ![![1565383, -574758, 131353]]], ![![![-599241, 220022, -50283]], ![![-205658, 75511, -17257]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-1089, 778, 241]] ![![77308, -28385, 6487]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37623, -13814, 3157]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![37623, -13814, 3157]] 
 ![![61, 0, 0], ![0, 61, 0], ![5, 10, 1]] where
  M :=![![![37623, -13814, 3157], ![-291630, 107077, -24471], ![1111451, -408089, 93263]]]
  hmulB := by decide  
  f := ![![![-388, -31, 5]], ![![-471, -278, -57]], ![![-67, -62, -14]]]
  g := ![![![358, -744, 3157], ![-2775, 5767, -24471], ![10576, -21979, 93263]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [45, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 60], [0, 1]]
 g := ![![[35, 19], [39], [19, 12], [8, 42], [11, 1]], ![[0, 42], [39], [29, 49], [43, 19], [22, 60]]]
 h' := ![![[11, 60], [15, 43], [60, 10], [6, 16], [54, 15], [0, 1]], ![[0, 1], [0, 18], [48, 51], [60, 45], [36, 46], [11, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [36, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [45, 50, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9819, 3237, 1196]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-259, -143, 1196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![388, 31, -5]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![388, 31, -5]] 
 ![![61, 0, 0], ![40, 1, 0], ![24, 0, 1]] where
  M :=![![![388, 31, -5], ![471, 278, 57], ![-2563, 847, 309]]]
  hmulB := by decide  
  f := ![![![-37623, 13814, -3157]], ![![-19890, 7303, -1669]], ![![-33023, 12125, -2771]]]
  g := ![![![-12, 31, -5], ![-197, 278, 57], ![-719, 847, 309]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![37623, -13814, 3157]] ![![388, 31, -5]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [31, 14, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 23, 14], [22, 43, 53], [0, 1]]
 g := ![![[31, 52, 60], [51, 22, 29], [57, 49], [5, 35], [66, 1], []], ![[50, 9, 40, 10], [1, 52, 6, 47], [33, 25], [58, 49], [47, 40], [46, 62]], ![[34, 54, 18, 31], [19, 64, 6, 61], [41, 10], [38, 36], [15, 60], [7, 62]]]
 h' := ![![[44, 23, 14], [27, 50, 44], [46, 36, 37], [2, 2, 60], [31, 50, 54], [0, 0, 1], [0, 1]], ![[22, 43, 53], [11, 15, 46], [65, 3, 18], [4, 21, 62], [23, 22, 7], [41, 61, 43], [44, 23, 14]], ![[0, 1], [11, 2, 44], [64, 28, 12], [53, 44, 12], [5, 62, 6], [66, 6, 23], [22, 43, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 5], []]
 b := ![[], [58, 11, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [31, 14, 1, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-224182, 85827, -19497]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3346, 1281, -291]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-849184, 311793, -71256]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-849184, 311793, -71256]] 
 ![![71, 0, 0], ![0, 71, 0], ![60, 62, 1]] where
  M :=![![![-849184, 311793, -71256], ![6582321, -2416816, 552330], ![-25086336, 9210894, -2105023]]]
  hmulB := by decide  
  f := ![![![-2588, 375, 186]], ![![-15993, 1504, 936]], ![![-16704, 1660, 1001]]]
  g := ![![![48256, 66615, -71256], ![-374049, -516356, 552330], ![1425564, 1967920, -2105023]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [58, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 70], [0, 1]]
 g := ![![[31, 60], [47, 36], [27, 15], [12], [32], [1]], ![[0, 11], [0, 35], [37, 56], [12], [32], [1]]]
 h' := ![![[48, 70], [43, 42], [67, 6], [19, 21], [17, 15], [13, 48], [0, 1]], ![[0, 1], [0, 29], [0, 65], [33, 50], [27, 56], [45, 23], [48, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [31, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [58, 23, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1123, -325, 470]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-413, -415, 470]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2588, 375, 186]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-2588, 375, 186]] 
 ![![71, 0, 0], ![17, 1, 0], ![69, 0, 1]] where
  M :=![![![-2588, 375, 186], ![-15993, 1504, 936], ![-39138, 2112, 1879]]]
  hmulB := by decide  
  f := ![![![-849184, 311793, -71256]], ![![-110617, 40615, -9282]], ![![-1178592, 432741, -98897]]]
  g := ![![![-307, 375, 186], ![-1495, 1504, 936], ![-2883, 2112, 1879]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-849184, 311793, -71256]] ![![-2588, 375, 186]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [43, 38, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 1, 54], [12, 71, 19], [0, 1]]
 g := ![![[38, 51, 69], [56, 46], [7, 70], [55, 22, 1], [57, 1], []], ![[13, 24, 39, 36], [26, 3], [62, 61], [57, 14, 56, 70], [66, 4], [26, 69]], ![[20, 47, 34, 67], [13, 1], [41, 46], [6, 40, 63, 25], [49, 1], [61, 69]]]
 h' := ![![[45, 1, 54], [39, 33, 54], [29, 55, 51], [44, 42, 56], [31, 54, 72], [0, 0, 1], [0, 1]], ![[12, 71, 19], [59, 30, 68], [70, 40, 21], [20, 47, 39], [21, 50, 71], [31, 4, 71], [45, 1, 54]], ![[0, 1], [13, 10, 24], [39, 51, 1], [59, 57, 51], [19, 42, 3], [3, 69, 1], [12, 71, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 27], []]
 b := ![[], [15, 69, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [43, 38, 16, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-272947, 180675, -51465]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3739, 2475, -705]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2456, 655, 255]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-2456, 655, 255]] 
 ![![79, 0, 0], ![0, 79, 0], ![4, 32, 1]] where
  M :=![![![-2456, 655, 255], ![-21785, 3154, 1565], ![-66055, 5995, 3809]]]
  hmulB := by decide  
  f := ![![![-33309, 12230, -2795]], ![![258190, -94799, 21665]], ![![90441, -33207, 7589]]]
  g := ![![![-44, -95, 255], ![-355, -594, 1565], ![-1029, -1467, 3809]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [55, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 78], [0, 1]]
 g := ![![[63, 23], [11, 10], [32, 55], [69, 26], [42], [1]], ![[0, 56], [42, 69], [5, 24], [39, 53], [42], [1]]]
 h' := ![![[11, 78], [27, 55], [57, 22], [76, 56], [4, 42], [24, 11], [0, 1]], ![[0, 1], [0, 24], [62, 57], [60, 23], [71, 37], [66, 68], [11, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [35, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [55, 68, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9815, -4588, 1328]
  a := ![4, -10, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![57, -596, 1328]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33309, 12230, -2795]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-33309, 12230, -2795]] 
 ![![79, 0, 0], ![14, 1, 0], ![21, 0, 1]] where
  M :=![![![-33309, 12230, -2795], ![258190, -94799, 21665], ![-984005, 361295, -82569]]]
  hmulB := by decide  
  f := ![![![-2456, 655, 255]], ![![-711, 156, 65]], ![![-1489, 250, 116]]]
  g := ![![![-1846, 12230, -2795], ![14309, -94799, 21665], ![-54534, 361295, -82569]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-2456, 655, 255]] ![![-33309, 12230, -2795]]
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


lemma PB82I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 81 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 81 (by omega)

def PB82I1 : PrimesBelowBoundCertificateInterval O 31 81 82 where
  m := 11
  g := ![2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB82I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
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
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![5041, 71]
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
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
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
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I43N1, I53N1, I59N0, I59N1, I59N2, I61N1, I71N1, I79N1]
  Il := ![[I37N1], [], [I43N1], [], [I53N1], [I59N0, I59N1, I59N2], [I61N1], [], [I71N1], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
