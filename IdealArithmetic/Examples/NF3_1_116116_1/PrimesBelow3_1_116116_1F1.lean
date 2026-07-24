
import IdealArithmetic.Examples.NF3_1_116116_1.RI3_1_116116_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![10, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![10, 1, 0]] 
 ![![37, 0, 0], ![10, 1, 0], ![6, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![10, 1, 0], ![1, 10, 2], ![67, -11, 11]]]
  hmulB := by decide  
  f := ![![![-161, -1818, -364], ![-74, 6734, 0]], ![![-49, -490, -98], ![1, 1813, 0]], ![![-28, -295, -59], ![-5, 1092, 0]]]
  g := ![![![1, 0, 0], ![-10, 37, 0], ![-6, 0, 37]], ![![0, 1, 0], ![-3, 10, 2], ![3, -11, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![12, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![12, 1, 0]] 
 ![![37, 0, 0], ![12, 1, 0], ![21, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![12, 1, 0], ![1, 12, 2], ![67, -11, 13]]]
  hmulB := by decide  
  f := ![![![-883, -13039, -2176], ![-629, 40256, 0]], ![![-292, -4219, -704], ![-184, 13024, 0]], ![![-507, -7401, -1235], ![-339, 22848, 0]]]
  g := ![![![1, 0, 0], ![-12, 37, 0], ![-21, 0, 37]], ![![0, 1, 0], ![-5, 12, 2], ![-2, -11, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![14, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![14, 1, 0]] 
 ![![37, 0, 0], ![14, 1, 0], ![32, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![14, 1, 0], ![1, 14, 2], ![67, -11, 15]]]
  hmulB := by decide  
  f := ![![![179, 3467, 496], ![185, -9176, 0]], ![![65, 1300, 186], ![75, -3441, 0]], ![![148, 2998, 429], ![178, -7936, 0]]]
  g := ![![![1, 0, 0], ![-14, 37, 0], ![-32, 0, 37]], ![![0, 1, 0], ![-7, 14, 2], ![-7, -11, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![10, 1, 0]] ![![37, 0, 0], ![12, 1, 0]]
  ![![37, 0, 0], ![5, 11, 1]] where
 M := ![![![1369, 0, 0], ![444, 37, 0]], ![![370, 37, 0], ![121, 22, 2]]]
 hmul := by decide  
 g := ![![![![32, -11, -1], ![37, 0, 0]], ![![7, -10, -1], ![37, 0, 0]]], ![![![5, -10, -1], ![37, 0, 0]], ![![3, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![5, 11, 1]] ![![37, 0, 0], ![14, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![518, 37, 0]], ![![185, 407, 37], ![148, 148, 37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![14, 1, 0]]], ![![![5, 11, 1]], ![![4, 4, 1]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [2, 23, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 18, 35], [15, 22, 6], [0, 1]]
 g := ![![[8, 20, 23], [40, 8], [19, 4], [19, 40, 1], []], ![[34, 29, 3, 35], [3, 5], [34, 39], [25, 8, 9, 7], [35, 36]], ![[35, 25, 2, 35], [9, 36], [15, 40], [34, 36, 11, 17], [23, 36]]]
 h' := ![![[25, 18, 35], [23, 36, 8], [12, 20, 34], [3, 16, 2], [0, 0, 1], [0, 1]], ![[15, 22, 6], [33, 12, 1], [30, 35, 13], [37, 6, 30], [22, 23, 22], [25, 18, 35]], ![[0, 1], [27, 34, 32], [2, 27, 35], [27, 19, 9], [15, 18, 18], [15, 22, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 35], []]
 b := ![[], [1, 1, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [2, 23, 1, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5289, 2665, -1804]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-129, 65, -44]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![16, -15, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![16, -15, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![16, 28, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![16, -15, 1], ![52, 5, -29], ![-977, 193, -10]]]
  hmulB := by decide  
  f := ![![![-15, 15, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -28, 43]], ![![0, -1, 1], ![12, 19, -29], ![-19, 11, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [33, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 42], [0, 1]]
 g := ![![[40, 15], [11, 6], [17], [6, 40], [1]], ![[20, 28], [3, 37], [17], [10, 3], [1]]]
 h' := ![![[13, 42], [24, 12], [29, 7], [17, 19], [10, 13], [0, 1]], ![[0, 1], [8, 31], [34, 36], [6, 24], [7, 30], [13, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [5, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [33, 30, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-539, 852, -117]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31, 96, -117]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-14, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-14, 1, 0]] 
 ![![43, 0, 0], ![29, 1, 0], ![10, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-14, 1, 0], ![1, -14, 2], ![67, -11, -13]]]
  hmulB := by decide  
  f := ![![![-85, 1594, -228], ![86, 4902, 0]], ![![-47, 1062, -152], ![87, 3268, 0]], ![![-10, 370, -53], ![50, 1140, 0]]]
  g := ![![![1, 0, 0], ![-29, 43, 0], ![-10, 0, 43]], ![![-1, 1, 0], ![9, -14, 2], ![12, -11, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![16, -15, 1]] ![![43, 0, 0], ![-14, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-602, 43, 0]], ![![688, -645, 43], ![-172, 215, -43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-14, 1, 0]]], ![![![16, -15, 1]], ![![-4, 5, -1]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [16, 12, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 22, 9], [15, 24, 38], [0, 1]]
 g := ![![[31, 1, 8], [20, 0, 7], [14, 19, 4], [15, 36, 1], []], ![[6, 30, 22, 34], [9, 1, 41, 3], [23, 4, 30, 7], [26, 34, 26, 14], [22, 34]], ![[13, 10, 37, 39], [43, 41, 32, 26], [19, 24, 8, 35], [21, 12, 0, 15], [40, 34]]]
 h' := ![![[21, 22, 9], [9, 22, 33], [11, 23, 17], [42, 43, 45], [0, 0, 1], [0, 1]], ![[15, 24, 38], [24, 35, 3], [33, 34, 4], [15, 9, 10], [42, 22, 24], [21, 22, 9]], ![[0, 1], [39, 37, 11], [22, 37, 26], [13, 42, 39], [8, 25, 22], [15, 24, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 13], []]
 b := ![[], [37, 39, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [16, 12, 11, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-481113808, 156335536, -42197070]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10236464, 3326288, -897810]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [21, 44, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 16, 22], [45, 36, 31], [0, 1]]
 g := ![![[35, 44, 25], [20, 16], [32, 46, 11], [34, 1], [1]], ![[16, 48, 18, 26], [16, 7], [16, 23, 19, 35], [14, 9], [44, 15, 23, 48]], ![[16, 44, 4, 45], [5, 6], [38, 5, 16, 26], [12, 4], [27, 33, 9, 5]]]
 h' := ![![[7, 16, 22], [28, 9, 48], [17, 22, 49], [45, 13, 45], [32, 9, 52], [0, 1]], ![[45, 36, 31], [50, 35, 18], [11, 21, 22], [28, 23, 51], [2, 48, 3], [7, 16, 22]], ![[0, 1], [8, 9, 40], [31, 10, 35], [3, 17, 10], [34, 49, 51], [45, 36, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 1], []]
 b := ![[], [1, 41, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [21, 44, 1, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-250107, 83316, -17278]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4719, 1572, -326]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![5, 20, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![5, 20, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![5, 20, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![5, 20, 1], ![87, -6, 41], ![1368, -192, 14]]]
  hmulB := by decide  
  f := ![![![-4, -20, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -20, 59]], ![![0, 0, 1], ![-2, -14, 41], ![22, -8, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [25, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 58], [0, 1]]
 g := ![![[31, 26], [41, 4], [49], [10, 46], [51, 1]], ![[0, 33], [9, 55], [49], [55, 13], [43, 58]]]
 h' := ![![[51, 58], [37, 12], [33, 2], [45, 7], [23, 39], [0, 1]], ![[0, 1], [0, 47], [17, 57], [48, 52], [6, 20], [51, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [33, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [25, 8, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![399, 62, -50]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 18, -50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![18, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![18, 1, 0]] 
 ![![59, 0, 0], ![18, 1, 0], ![45, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![18, 1, 0], ![1, 18, 2], ![67, -11, 19]]]
  hmulB := by decide  
  f := ![![![-239, -4966, -552], ![-118, 16284, 0]], ![![-84, -1512, -168], ![1, 4956, 0]], ![![-189, -3788, -421], ![-68, 12420, 0]]]
  g := ![![![1, 0, 0], ![-18, 59, 0], ![-45, 0, 59]], ![![0, 1, 0], ![-7, 18, 2], ![-10, -11, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![5, 20, 1]] ![![59, 0, 0], ![18, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1062, 59, 0]], ![![295, 1180, 59], ![177, 354, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![18, 1, 0]]], ![![![5, 20, 1]], ![![3, 6, 1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![28, 24, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![28, 24, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![28, 24, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![28, 24, 1], ![91, 17, 49], ![1636, -236, 41]]]
  hmulB := by decide  
  f := ![![![-27, -24, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -24, 61]], ![![0, 0, 1], ![-21, -19, 49], ![8, -20, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [8, 60, 1] where
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
 g := ![![[38, 15], [42], [32, 12], [39, 49], [1, 1]], ![[53, 46], [42], [44, 49], [27, 12], [2, 60]]]
 h' := ![![[1, 60], [52, 36], [49, 46], [54, 16], [53, 54], [0, 1]], ![[0, 1], [27, 25], [34, 15], [9, 45], [46, 7], [1, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [59, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [8, 60, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8383, 214, 929]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-289, -362, 929]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![12, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![12, 1, 0]] 
 ![![61, 0, 0], ![12, 1, 0], ![20, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![12, 1, 0], ![1, 12, 2], ![67, -11, 13]]]
  hmulB := by decide  
  f := ![![![-2239, -28882, -4816], ![-854, 146888, 0]], ![![-449, -5674, -946], ![-121, 28853, 0]], ![![-740, -9470, -1579], ![-250, 48160, 0]]]
  g := ![![![1, 0, 0], ![-12, 61, 0], ![-20, 0, 61]], ![![0, 1, 0], ![-3, 12, 2], ![-1, -11, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![28, 24, 1]] ![![61, 0, 0], ![12, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![732, 61, 0]], ![![1708, 1464, 61], ![427, 305, 61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![12, 1, 0]]], ![![![28, 24, 1]], ![![7, 5, 1]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [45, 9, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 13, 39], [21, 53, 28], [0, 1]]
 g := ![![[8, 31, 29], [56, 33, 14], [47, 23], [13, 49], [63, 1], []], ![[44, 53, 58, 60], [24, 51, 50, 29], [8, 16], [39, 65], [38, 62], [22, 47]], ![[28, 56, 42, 51], [16, 1, 65, 11], [28, 59], [20, 59], [49, 35], [33, 47]]]
 h' := ![![[42, 13, 39], [26, 46, 30], [62, 36, 58], [57, 66, 31], [46, 58, 7], [0, 0, 1], [0, 1]], ![[21, 53, 28], [53, 14, 34], [35, 0, 56], [23, 58, 63], [61, 46, 20], [37, 52, 53], [42, 13, 39]], ![[0, 1], [23, 7, 3], [30, 31, 20], [33, 10, 40], [53, 30, 40], [28, 15, 13], [21, 53, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 64], []]
 b := ![[], [30, 0, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [45, 9, 4, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-98758, 22713, 804]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1474, 339, 12]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [64, 36, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 44, 38], [12, 26, 33], [0, 1]]
 g := ![![[7, 25, 60], [32, 49, 9], [40, 24, 8], [52, 49], [61, 1], []], ![[47, 53, 8, 58], [49, 23, 2, 5], [24, 49, 21, 6], [50, 29], [17, 37], [51, 24]], ![[19, 64, 47, 67], [32, 0, 53, 46], [24, 57, 22, 59], [49, 5], [18, 19], [56, 24]]]
 h' := ![![[49, 44, 38], [11, 59, 42], [67, 35, 3], [10, 57, 47], [1, 12, 64], [0, 0, 1], [0, 1]], ![[12, 26, 33], [26, 44, 68], [45, 29, 59], [14, 41, 51], [27, 54, 61], [60, 17, 26], [49, 44, 38]], ![[0, 1], [14, 39, 32], [36, 7, 9], [42, 44, 44], [14, 5, 17], [39, 54, 44], [12, 26, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 38], []]
 b := ![[], [3, 9, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [64, 36, 10, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![83070, -25773, 10934]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1170, -363, 154]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![6, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![6, 1, 0]] 
 ![![73, 0, 0], ![6, 1, 0], ![19, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![6, 1, 0], ![1, 6, 2], ![67, -11, 7]]]
  hmulB := by decide  
  f := ![![![-243, -1464, -488], ![0, 17812, 0]], ![![-20, -120, -40], ![1, 1460, 0]], ![![-63, -381, -127], ![-3, 4636, 0]]]
  g := ![![![1, 0, 0], ![-6, 73, 0], ![-19, 0, 73]], ![![0, 1, 0], ![-1, 6, 2], ![0, -11, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![31, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![31, 1, 0]] 
 ![![73, 0, 0], ![31, 1, 0], ![31, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![31, 1, 0], ![1, 31, 2], ![67, -11, 32]]]
  hmulB := by decide  
  f := ![![![-848, -37839, -2442], ![-876, 89133, 0]], ![![-363, -16053, -1036], ![-364, 37814, 0]], ![![-372, -16069, -1037], ![-344, 37851, 0]]]
  g := ![![![1, 0, 0], ![-31, 73, 0], ![-31, 0, 73]], ![![0, 1, 0], ![-14, 31, 2], ![-8, -11, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![35, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![35, 1, 0]] 
 ![![73, 0, 0], ![35, 1, 0], ![45, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![35, 1, 0], ![1, 35, 2], ![67, -11, 36]]]
  hmulB := by decide  
  f := ![![![-1354, -75577, -4320], ![-1679, 157680, 0]], ![![-650, -36214, -2070], ![-802, 75555, 0]], ![![-850, -46589, -2663], ![-1003, 97200, 0]]]
  g := ![![![1, 0, 0], ![-35, 73, 0], ![-45, 0, 73]], ![![0, 1, 0], ![-18, 35, 2], ![-16, -11, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![6, 1, 0]] ![![73, 0, 0], ![31, 1, 0]]
  ![![73, 0, 0], ![-16, -18, 1]] where
 M := ![![![5329, 0, 0], ![2263, 73, 0]], ![![438, 73, 0], ![187, 37, 2]]]
 hmul := by decide  
 g := ![![![![73, 0, 0], ![0, 0, 0]], ![![31, 1, 0], ![0, 0, 0]]], ![![![6, 1, 0], ![0, 0, 0]], ![![3, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-16, -18, 1]] ![![73, 0, 0], ![35, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![2555, 73, 0]], ![![-1168, -1314, 73], ![-511, -657, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![35, 1, 0]]], ![![![-16, -18, 1]], ![![-7, -9, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![45, 18, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![45, 18, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![45, 18, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![45, 18, 1], ![85, 34, 37], ![1234, -170, 52]]]
  hmulB := by decide  
  f := ![![![-44, -18, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -18, 79]], ![![0, 0, 1], ![-20, -8, 37], ![-14, -14, 52]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [15, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 78], [0, 1]]
 g := ![![[55, 42], [13, 5], [75, 62], [50, 50], [40], [1]], ![[7, 37], [75, 74], [38, 17], [38, 29], [40], [1]]]
 h' := ![![[44, 78], [42, 68], [60, 20], [40, 33], [20, 45], [64, 44], [0, 1]], ![[0, 1], [32, 11], [71, 59], [70, 46], [25, 34], [25, 35], [44, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [61, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [15, 35, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![565, 700, -400]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![235, 100, -400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-37, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-37, 1, 0]] 
 ![![79, 0, 0], ![42, 1, 0], ![27, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-37, 1, 0], ![1, -37, 2], ![67, -11, -36]]]
  hmulB := by decide  
  f := ![![![-1420, 84041, -4544], ![1817, 179488, 0]], ![![-762, 44647, -2414], ![949, 95353, 0]], ![![-490, 28723, -1553], ![611, 61344, 0]]]
  g := ![![![1, 0, 0], ![-42, 79, 0], ![-27, 0, 79]], ![![-1, 1, 0], ![19, -37, 2], ![19, -11, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![45, 18, 1]] ![![79, 0, 0], ![-37, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-2923, 79, 0]], ![![3555, 1422, 79], ![-1580, -632, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-37, 1, 0]]], ![![![45, 18, 1]], ![![-20, -8, 0]]]]
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


lemma PB97I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB97I1 : PrimesBelowBoundCertificateInterval O 31 79 97 where
  m := 11
  g := ![3, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB97I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![357911]
    · exact ![73, 73, 73]
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
      exact NI37N2
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
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I37N2, I43N1, I59N1, I61N1, I73N0, I73N1, I73N2, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [], [I43N1], [], [], [I59N1], [I61N1], [], [], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
