
import IdealArithmetic.Examples.NF3_1_649415_1.RI3_1_649415_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [6, 12, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 35, 2], [6, 1, 35], [0, 1]]
 g := ![![[3], [9, 7], [35, 23, 34], [25, 1], []], ![[32, 19, 10, 24], [28, 12], [20, 27, 2, 2], [22, 1], [18, 4]], ![[0, 6, 28, 13], [6, 34], [0, 6, 6, 31], [20, 4], [22, 4]]]
 h' := ![![[19, 35, 2], [16, 22], [12, 1, 28], [35, 27, 21], [0, 0, 1], [0, 1]], ![[6, 1, 35], [27, 30, 7], [11, 30, 30], [15, 7, 1], [31, 17, 1], [19, 35, 2]], ![[0, 1], [0, 22, 30], [31, 6, 16], [31, 3, 15], [15, 20, 35], [6, 1, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 35], []]
 b := ![[], [23, 19, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [6, 12, 12, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-703703, -61050, -19055]
  a := ![-2, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19019, -1650, -515]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![10, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![10, 1, 0]] 
 ![![41, 0, 0], ![10, 1, 0], ![7, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![10, 1, 0], ![2, 9, 5], ![157, 8, 11]]]
  hmulB := by decide  
  f := ![![![1967, 9639, 5365], ![738, -43993, 0]], ![![472, 2344, 1305], ![206, -10701, 0]], ![![329, 1645, 916], ![154, -7511, 0]]]
  g := ![![![1, 0, 0], ![-10, 41, 0], ![-7, 0, 41]], ![![0, 1, 0], ![-3, 9, 5], ![0, 8, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-107, 3, 3]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-107, 3, 3]] 
 ![![41, 0, 0], ![33, 1, 0], ![27, 0, 1]] where
  M :=![![![-107, 3, 3], ![477, -86, 18], ![669, 123, -80]]]
  hmulB := by decide  
  f := ![![![-4666, -609, -312]], ![![-4980, -650, -333]], ![![-5907, -771, -395]]]
  g := ![![![-7, 3, 3], ![69, -86, 18], ![-30, 123, -80]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-2, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-2, 1, 0]] 
 ![![41, 0, 0], ![39, 1, 0], ![32, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-2, 1, 0], ![2, -3, 5], ![157, 8, -1]]]
  hmulB := by decide  
  f := ![![![799, -1199, 2000], ![-41, -16400, 0]], ![![759, -1139, 1900], ![-40, -15580, 0]], ![![624, -936, 1561], ![-24, -12800, 0]]]
  g := ![![![1, 0, 0], ![-39, 41, 0], ![-32, 0, 41]], ![![-1, 1, 0], ![-1, -3, 5], ![-3, 8, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![10, 1, 0]] ![![-107, 3, 3]]
  ![![41, 0, 0], ![9, -8, 1]] where
 M := ![![![-4387, 123, 123]], ![![-593, -56, 48]]]
 hmul := by decide  
 g := ![![![![-107, 3, 3], ![0, 0, 0]]], ![![![-16, 0, 1], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![9, -8, 1]] ![![41, 0, 0], ![-2, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-82, 41, 0]], ![![369, -328, 41], ![123, 41, -41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-2, 1, 0]]], ![![![9, -8, 1]], ![![3, 1, -1]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [31, 31, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 40, 8], [17, 2, 35], [0, 1]]
 g := ![![[10, 39, 14], [34, 22, 35], [26, 10], [33, 8, 1], []], ![[38, 8, 6, 39], [21, 13, 35, 2], [28, 6], [8, 30, 1, 32], [34, 21]], ![[35, 19, 15, 31], [33, 31, 0, 17], [0, 11], [4, 14, 0, 14], [7, 21]]]
 h' := ![![[34, 40, 8], [21, 20, 10], [6, 0, 32], [9, 19, 28], [0, 0, 1], [0, 1]], ![[17, 2, 35], [1, 28, 8], [2, 15, 21], [28, 26, 36], [16, 26, 2], [34, 40, 8]], ![[0, 1], [6, 38, 25], [31, 28, 33], [26, 41, 22], [29, 17, 40], [17, 2, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 28], []]
 b := ![[], [2, 26, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [31, 31, 35, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8803089, 1285141, 32809]
  a := ![5, -5, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![204723, 29887, 763]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![2, -10, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![2, -10, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![2, 37, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![2, -10, 1], ![137, 20, -49], ![-1504, -47, 0]]]
  hmulB := by decide  
  f := ![![![-1, 10, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -37, 47]], ![![0, -1, 1], ![5, 39, -49], ![-32, -1, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [21, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 46], [0, 1]]
 g := ![![[0, 9], [0, 27], [0, 42], [], [1]], ![[0, 38], [0, 20], [0, 5], [], [1]]]
 h' := ![![[0, 46], [0, 44], [0, 11], [0, 18], [26], [0, 1]], ![[0, 1], [0, 3], [0, 36], [0, 29], [26], [0, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [0, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [21, 0, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1088335, 579213, 158556]
  a := ![-66, 2, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16409, -112497, 158556]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![2, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![2, 1, 0]] 
 ![![47, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![2, 1, 0], ![2, 1, 5], ![157, 8, 3]]]
  hmulB := by decide  
  f := ![![![-1, -1, 0], ![47, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-2, -1, -2], ![28, 19, 0]]]
  g := ![![![1, 0, 0], ![-2, 47, 0], ![0, 0, 47]], ![![0, 1, 0], ![0, 1, 5], ![3, 8, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![2, -10, 1]] ![![47, 0, 0], ![2, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![94, 47, 0]], ![![94, -470, 47], ![141, 0, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![2, 1, 0]]], ![![![2, -10, 1]], ![![3, 0, -1]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [45, 47, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 22, 12], [20, 30, 41], [0, 1]]
 g := ![![[16, 4, 47], [33, 28], [33, 20, 44], [21, 15], [1]], ![[46, 15, 15, 39], [42, 13], [11, 23, 51, 30], [51, 49], [44, 12, 36, 32]], ![[29, 26, 33, 31], [16, 36], [37, 27, 32, 20], [37, 16], [13, 11, 9, 21]]]
 h' := ![![[22, 22, 12], [0, 19, 43], [52, 16, 9], [20, 24, 37], [8, 6, 42], [0, 1]], ![[20, 30, 41], [28, 19, 34], [13, 38, 38], [30, 38, 20], [29, 27, 7], [22, 22, 12]], ![[0, 1], [23, 15, 29], [52, 52, 6], [3, 44, 49], [48, 20, 4], [20, 30, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 37], []]
 b := ![[], [48, 3, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [45, 47, 11, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9898969, -1077384, -38319]
  a := ![-5, 4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-186773, -20328, -723]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![18, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![18, 1, 0]] 
 ![![59, 0, 0], ![18, 1, 0], ![10, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![18, 1, 0], ![2, 17, 5], ![157, 8, 19]]]
  hmulB := by decide  
  f := ![![![-2297, -22269, -6555], ![-1062, 77349, 0]], ![![-708, -6778, -1995], ![-294, 23541, 0]], ![![-400, -3775, -1111], ![-145, 13110, 0]]]
  g := ![![![1, 0, 0], ![-18, 59, 0], ![-10, 0, 59]], ![![0, 1, 0], ![-6, 17, 5], ![-3, 8, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-15, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-15, 1, 0]] 
 ![![59, 0, 0], ![44, 1, 0], ![35, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-15, 1, 0], ![2, -16, 5], ![157, 8, -14]]]
  hmulB := by decide  
  f := ![![![2196, -19345, 6050], ![-885, -71390, 0]], ![![1640, -14421, 4510], ![-648, -53218, 0]], ![![1305, -11476, 3589], ![-516, -42350, 0]]]
  g := ![![![1, 0, 0], ![-44, 59, 0], ![-35, 0, 59]], ![![-1, 1, 0], ![9, -16, 5], ![5, 8, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-3, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-3, 1, 0]] 
 ![![59, 0, 0], ![56, 1, 0], ![57, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-3, 1, 0], ![2, -4, 5], ![157, 8, -2]]]
  hmulB := by decide  
  f := ![![![3187, -6392, 7995], ![-236, -94341, 0]], ![![3023, -6064, 7585], ![-235, -89503, 0]], ![![3078, -6175, 7724], ![-247, -91143, 0]]]
  g := ![![![1, 0, 0], ![-56, 59, 0], ![-57, 0, 59]], ![![-1, 1, 0], ![-1, -4, 5], ![-3, 8, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![18, 1, 0]] ![![59, 0, 0], ![-15, 1, 0]]
  ![![59, 0, 0], ![-30, 24, 1]] where
 M := ![![![3481, 0, 0], ![-885, 59, 0]], ![![1062, 59, 0], ![-268, 2, 5]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![15, -23, -1], ![59, 0, 0]]], ![![![18, 1, 0], ![0, 0, 0]], ![![-2, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-30, 24, 1]] ![![59, 0, 0], ![-3, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-177, 59, 0]], ![![-1770, 1416, 59], ![295, -118, 118]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-3, 1, 0]]], ![![![-30, 24, 1]], ![![5, -2, 2]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [32, 6, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 23, 27], [22, 37, 34], [0, 1]]
 g := ![![[11, 12, 57], [10, 52], [20, 37, 42], [5, 47, 15], [1]], ![[52, 41, 13, 1], [4, 1], [40, 48, 29, 16], [55, 23, 58, 34], [44, 16, 49, 41]], ![[43, 51, 11, 27], [0, 48], [40, 8, 36, 57], [45, 8, 60, 15], [52, 20, 21, 20]]]
 h' := ![![[14, 23, 27], [31, 2, 39], [31, 18, 33], [23, 39, 46], [29, 55, 36], [0, 1]], ![[22, 37, 34], [46, 47, 33], [28, 16, 60], [25, 52, 10], [55, 60, 11], [14, 23, 27]], ![[0, 1], [22, 12, 50], [49, 27, 29], [38, 31, 5], [17, 7, 14], [22, 37, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34], []]
 b := ![[], [40, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [32, 6, 25, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-682163, -50325, -16165]
  a := ![-2, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11183, -825, -265]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [31, 3, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 46, 18], [33, 20, 49], [0, 1]]
 g := ![![[62, 50, 6], [44, 12, 39], [20, 40], [64, 19], [54, 1], []], ![[40, 56, 53, 3], [3, 51, 3, 3], [61, 39], [5, 65], [21, 65], [57, 56]], ![[30, 47, 29, 59], [49, 34, 25, 39], [56, 9], [21, 10], [7, 39], [26, 56]]]
 h' := ![![[21, 46, 18], [43, 54, 26], [42, 2, 46], [27, 39, 43], [1, 8, 32], [0, 0, 1], [0, 1]], ![[33, 20, 49], [0, 52, 18], [58, 36, 18], [41, 55, 21], [14, 29, 47], [14, 25, 20], [21, 46, 18]], ![[0, 1], [4, 28, 23], [61, 29, 3], [16, 40, 3], [8, 30, 55], [15, 42, 46], [33, 20, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 52], []]
 b := ![[], [17, 63, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [31, 3, 13, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12155743, 1831512, 843195]
  a := ![3, 18, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![181429, 27336, 12585]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![26, 16, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![26, 16, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![26, 16, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![26, 16, 1], ![189, 18, 81], ![2578, 161, 50]]]
  hmulB := by decide  
  f := ![![![-25, -16, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -16, 71]], ![![0, 0, 1], ![-27, -18, 81], ![18, -9, 50]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [34, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 70], [0, 1]]
 g := ![![[57, 57], [6, 20], [], [32], [15], [1]], ![[67, 14], [12, 51], [], [32], [15], [1]]]
 h' := ![![[50, 70], [9, 46], [0, 37], [26], [7, 48], [37, 50], [0, 1]], ![[0, 1], [37, 25], [4, 34], [26], [64, 23], [52, 21], [50, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [70, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [34, 21, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5546, 1213, 311]
  a := ![-3, 4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-192, -53, 311]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-10, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-10, 1, 0]] 
 ![![71, 0, 0], ![61, 1, 0], ![21, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-10, 1, 0], ![2, -11, 5], ![157, 8, -9]]]
  hmulB := by decide  
  f := ![![![-725, 4155, -1890], ![213, 26838, 0]], ![![-627, 3562, -1620], ![143, 23004, 0]], ![![-215, 1229, -559], ![59, 7938, 0]]]
  g := ![![![1, 0, 0], ![-61, 71, 0], ![-21, 0, 71]], ![![-1, 1, 0], ![8, -11, 5], ![-2, 8, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![26, 16, 1]] ![![71, 0, 0], ![-10, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-710, 71, 0]], ![![1846, 1136, 71], ![-71, -142, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-10, 1, 0]]], ![![![26, 16, 1]], ![![-1, -2, 1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-23, -24, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-23, -24, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![50, 49, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-23, -24, 1], ![109, 9, -119], ![-3702, -159, -39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-50, -49, 73]], ![![-1, -1, 1], ![83, 80, -119], ![-24, 24, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [2, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 72], [0, 1]]
 g := ![![[36, 37], [71], [70], [70, 9], [1], [1]], ![[0, 36], [71], [70], [6, 64], [1], [1]]]
 h' := ![![[1, 72], [16, 57], [42, 12], [6, 56], [2, 70], [71, 1], [0, 1]], ![[0, 1], [0, 16], [54, 61], [62, 17], [72, 3], [72, 72], [1, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [52, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [2, 72, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3768, 3059, 1585]
  a := ![4, -1, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1034, -1022, 1585]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-27, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-27, 1, 0]] 
 ![![73, 0, 0], ![46, 1, 0], ![39, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-27, 1, 0], ![2, -28, 5], ![157, 8, -26]]]
  hmulB := by decide  
  f := ![![![379, -6046, 1080], ![-146, -15768, 0]], ![![246, -3807, 680], ![-72, -9928, 0]], ![![201, -3230, 577], ![-82, -8424, 0]]]
  g := ![![![1, 0, 0], ![-46, 73, 0], ![-39, 0, 73]], ![![-1, 1, 0], ![15, -28, 5], ![11, 8, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-23, -24, 1]] ![![73, 0, 0], ![-27, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1971, 73, 0]], ![![-1679, -1752, 73], ![730, 657, -146]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-27, 1, 0]]], ![![![-23, -24, 1]], ![![10, 9, -2]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [34, 71, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 23, 4], [28, 55, 75], [0, 1]]
 g := ![![[78, 49, 1], [19, 39, 72], [50, 6, 44], [67, 7, 45], [62, 1], []], ![[67, 51, 72, 46], [71, 17, 20, 65], [20, 12, 55, 44], [27, 48, 31, 44], [4, 23], [70, 16]], ![[8, 13, 15, 34], [29, 75, 59, 57], [53, 64, 0, 35], [42, 54, 5, 14], [13, 55], [78, 16]]]
 h' := ![![[34, 23, 4], [65, 33, 1], [38, 49, 54], [13, 54, 26], [25, 67, 60], [0, 0, 1], [0, 1]], ![[28, 55, 75], [42, 48, 29], [72, 21, 6], [45, 57, 66], [42, 40, 13], [40, 0, 55], [34, 23, 4]], ![[0, 1], [69, 77, 49], [78, 9, 19], [41, 47, 66], [26, 51, 6], [28, 0, 23], [28, 55, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 15], []]
 b := ![[], [54, 18, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [34, 71, 17, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5695821, -521400, -161160]
  a := ![-5, 0, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-72099, -6600, -2040]
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



lemma PB229I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB229I1 : PrimesBelowBoundCertificateInterval O 31 79 229 where
  m := 11
  g := ![1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB229I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
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
    · exact ![50653]
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![59, 59, 59]
    · exact ![226981]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
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
  β := ![I41N0, I41N1, I41N2, I47N1, I59N0, I59N1, I59N2, I71N1, I73N1]
  Il := ![[], [I41N0, I41N1, I41N2], [], [I47N1], [], [I59N0, I59N1, I59N2], [], [], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
