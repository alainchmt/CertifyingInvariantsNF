
import IdealArithmetic.Examples.NF3_1_304535_3.RI3_1_304535_3
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [24, 28, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 4, 27], [30, 32, 10], [0, 1]]
 g := ![![[13, 21, 16], [21, 36], [35, 23, 30], [14, 1], []], ![[10, 3, 31, 30], [30, 34], [27, 33, 32, 36], [33, 25], [25, 26]], ![[17, 8, 33, 34], [30, 26], [15, 11, 24, 1], [0, 16], [5, 26]]]
 h' := ![![[21, 4, 27], [24, 7, 4], [11, 31, 31], [34, 28, 20], [0, 0, 1], [0, 1]], ![[30, 32, 10], [16, 29, 21], [25, 30, 16], [32, 6, 27], [26, 28, 32], [21, 4, 27]], ![[0, 1], [24, 1, 12], [35, 13, 27], [9, 3, 27], [3, 9, 4], [30, 32, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 25], []]
 b := ![[], [36, 5, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [24, 28, 23, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4329, 0, -333]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![117, 0, -9]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![5, -4, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![5, -4, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![5, 37, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![5, -4, 1], ![105, -2, -20], ![-420, 49, -2]]]
  hmulB := by decide  
  f := ![![![-4, 4, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -37, 41]], ![![0, -1, 1], ![5, 18, -20], ![-10, 3, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [7, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 40], [0, 1]]
 g := ![![[17, 33], [37], [18], [8, 16], [1]], ![[26, 8], [37], [18], [31, 25], [1]]]
 h' := ![![[4, 40], [30, 22], [17, 18], [26, 10], [34, 4], [0, 1]], ![[0, 1], [36, 19], [7, 23], [25, 31], [9, 37], [4, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [27, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [7, 37, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1289, 203, 62]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39, -51, 62]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![20, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![20, 1, 0]] 
 ![![41, 0, 0], ![20, 1, 0], ![2, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![20, 1, 0], ![0, 20, 5], ![105, -7, 20]]]
  hmulB := by decide  
  f := ![![![181, 9, 0], ![-369, 0, 0]], ![![60, 3, 0], ![-122, 0, 0]], ![![2, -16, -4], ![-4, 33, 0]]]
  g := ![![![1, 0, 0], ![-20, 41, 0], ![-2, 0, 41]], ![![0, 1, 0], ![-10, 20, 5], ![5, -7, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![5, -4, 1]] ![![41, 0, 0], ![20, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![820, 41, 0]], ![![205, -164, 41], ![205, -82, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![20, 1, 0]]], ![![![5, -4, 1]], ![![5, -2, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-14, 20, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-14, 20, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![29, 20, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-14, 20, 1], ![105, -21, 100], ![2100, -119, -21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -20, 43]], ![![-1, 0, 1], ![-65, -47, 100], ![63, 7, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [38, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 42], [0, 1]]
 g := ![![[39, 17], [33, 21], [4], [13, 13], [1]], ![[0, 26], [0, 22], [4], [11, 30], [1]]]
 h' := ![![[23, 42], [36, 19], [31, 8], [22, 2], [5, 23], [0, 1]], ![[0, 1], [0, 24], [0, 35], [25, 41], [18, 20], [23, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [2, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [38, 20, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2644, -73, 106]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, -51, 106]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-14, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-14, 1, 0]] 
 ![![43, 0, 0], ![29, 1, 0], ![21, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-14, 1, 0], ![0, -14, 5], ![105, -7, -14]]]
  hmulB := by decide  
  f := ![![![589, -42, 0], ![1806, 0, 0]], ![![407, -29, 0], ![1248, 0, 0]], ![![287, -12, -3], ![880, 26, 0]]]
  g := ![![![1, 0, 0], ![-29, 43, 0], ![-21, 0, 43]], ![![-1, 1, 0], ![7, -14, 5], ![14, -7, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-14, 20, 1]] ![![43, 0, 0], ![-14, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-602, 43, 0]], ![![-602, 860, 43], ![301, -301, 86]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-14, 1, 0]]], ![![![-14, 20, 1]], ![![7, -7, 2]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [30, 4, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 24, 22], [16, 22, 25], [0, 1]]
 g := ![![[10, 6, 21], [14, 23, 3], [44, 11, 14], [0, 45, 1], []], ![[16, 10, 6, 43], [17, 36, 33, 30], [22, 10, 10, 38], [41, 0, 19, 26], [41, 14]], ![[44, 33, 37, 21], [28, 12, 40, 25], [44, 40, 26, 32], [46, 4, 3, 18], [38, 14]]]
 h' := ![![[29, 24, 22], [3, 22, 31], [43, 11, 12], [0, 13, 25], [0, 0, 1], [0, 1]], ![[16, 22, 25], [3, 8, 38], [18, 43, 36], [5, 20, 37], [34, 9, 22], [29, 24, 22]], ![[0, 1], [23, 17, 25], [45, 40, 46], [10, 14, 32], [9, 38, 24], [16, 22, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 28], []]
 b := ![[], [38, 15, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [30, 4, 2, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-81968, 9447, 1504]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1744, 201, 32]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-15, -12, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-15, -12, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![38, 41, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-15, -12, 1], ![105, -22, -60], ![-1260, 105, -22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -41, 53]], ![![-1, -1, 1], ![45, 46, -60], ![-8, 19, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [45, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 52], [0, 1]]
 g := ![![[18, 6], [1], [30, 25], [17], [38, 1]], ![[34, 47], [1], [26, 28], [17], [23, 52]]]
 h' := ![![[38, 52], [50, 35], [28, 52], [14, 5], [39, 21], [0, 1]], ![[0, 1], [2, 18], [43, 1], [45, 48], [42, 32], [38, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [35, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [45, 15, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![255, -8, -17]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17, 13, -17]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![7, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![7, 1, 0]] 
 ![![53, 0, 0], ![7, 1, 0], ![22, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![7, 1, 0], ![0, 7, 5], ![105, -7, 7]]]
  hmulB := by decide  
  f := ![![![211, 30, 0], ![-1590, 0, 0]], ![![21, 3, 0], ![-158, 0, 0]], ![![86, 8, -3], ![-648, 32, 0]]]
  g := ![![![1, 0, 0], ![-7, 53, 0], ![-22, 0, 53]], ![![0, 1, 0], ![-3, 7, 5], ![0, -7, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-15, -12, 1]] ![![53, 0, 0], ![7, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![371, 53, 0]], ![![-795, -636, 53], ![0, -106, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![7, 1, 0]]], ![![![-15, -12, 1]], ![![0, -2, -1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-7, -3, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-7, -3, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![52, 56, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-7, -3, 1], ![105, -14, -15], ![-315, 42, -14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -56, 59]], ![![-1, -1, 1], ![15, 14, -15], ![7, 14, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [42, 8, 1] where
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
 g := ![![[3, 27], [17, 36], [28], [56, 12], [51, 1]], ![[23, 32], [24, 23], [28], [19, 47], [43, 58]]]
 h' := ![![[51, 58], [53, 26], [9, 53], [8, 21], [41, 22], [0, 1]], ![[0, 1], [22, 33], [57, 6], [17, 38], [42, 37], [51, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [50, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [42, 8, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4041, -55, 1808]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1525, -1717, 1808]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![15, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![15, 1, 0]] 
 ![![59, 0, 0], ![15, 1, 0], ![14, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![15, 1, 0], ![0, 15, 5], ![105, -7, 15]]]
  hmulB := by decide  
  f := ![![![31, 2, 0], ![-118, 0, 0]], ![![-15, -1, 0], ![60, 0, 0]], ![![-14, -4, -1], ![56, 12, 0]]]
  g := ![![![1, 0, 0], ![-15, 59, 0], ![-14, 0, 59]], ![![0, 1, 0], ![-5, 15, 5], ![0, -7, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-7, -3, 1]] ![![59, 0, 0], ![15, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![885, 59, 0]], ![![-413, -177, 59], ![0, -59, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![15, 1, 0]]], ![![![-7, -3, 1]], ![![0, -1, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-12, -17, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-12, -17, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![49, 44, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-12, -17, 1], ![105, -19, -85], ![-1785, 140, -19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -44, 61]], ![![-1, -1, 1], ![70, 61, -85], ![-14, 16, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [36, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 60], [0, 1]]
 g := ![![[27, 39], [47], [38, 46], [40, 34], [4, 1]], ![[0, 22], [47], [39, 15], [54, 27], [8, 60]]]
 h' := ![![[4, 60], [21, 10], [35, 48], [24, 30], [39, 41], [0, 1]], ![[0, 1], [0, 51], [44, 13], [22, 31], [20, 20], [4, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [40, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [36, 57, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-650, 228, -17]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, 16, -17]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![24, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![24, 1, 0]] 
 ![![61, 0, 0], ![24, 1, 0], ![19, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![24, 1, 0], ![0, 24, 5], ![105, -7, 24]]]
  hmulB := by decide  
  f := ![![![433, 18, 0], ![-1098, 0, 0]], ![![168, 7, 0], ![-426, 0, 0]], ![![127, -14, -4], ![-322, 49, 0]]]
  g := ![![![1, 0, 0], ![-24, 61, 0], ![-19, 0, 61]], ![![0, 1, 0], ![-11, 24, 5], ![-3, -7, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-12, -17, 1]] ![![61, 0, 0], ![24, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1464, 61, 0]], ![![-732, -1037, 61], ![-183, -427, -61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![24, 1, 0]]], ![![![-12, -17, 1]], ![![-3, -7, -1]]]]
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
 ![![67, 0, 0], ![2, 1, 0], ![26, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![2, 1, 0], ![0, 2, 5], ![105, -7, 2]]]
  hmulB := by decide  
  f := ![![![65, 32, 0], ![-2144, 0, 0]], ![![-2, -1, 0], ![68, 0, 0]], ![![22, 10, -2], ![-724, 27, 0]]]
  g := ![![![1, 0, 0], ![-2, 67, 0], ![-26, 0, 67]], ![![0, 1, 0], ![-2, 2, 5], ![1, -7, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![29, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![29, 1, 0]] 
 ![![67, 0, 0], ![29, 1, 0], ![6, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![29, 1, 0], ![0, 29, 5], ![105, -7, 29]]]
  hmulB := by decide  
  f := ![![![610, 21, 0], ![-1407, 0, 0]], ![![232, 8, 0], ![-535, 0, 0]], ![![20, -11, -2], ![-46, 27, 0]]]
  g := ![![![1, 0, 0], ![-29, 67, 0], ![-6, 0, 67]], ![![0, 1, 0], ![-13, 29, 5], ![2, -7, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-31, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-31, 1, 0]] 
 ![![67, 0, 0], ![36, 1, 0], ![49, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-31, 1, 0], ![0, -31, 5], ![105, -7, -31]]]
  hmulB := by decide  
  f := ![![![652, -21, 0], ![1407, 0, 0]], ![![404, -13, 0], ![872, 0, 0]], ![![512, -4, -2], ![1105, 27, 0]]]
  g := ![![![1, 0, 0], ![-36, 67, 0], ![-49, 0, 67]], ![![-1, 1, 0], ![13, -31, 5], ![28, -7, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![2, 1, 0]] ![![67, 0, 0], ![29, 1, 0]]
  ![![67, 0, 0], ![25, 33, 1]] where
 M := ![![![4489, 0, 0], ![1943, 67, 0]], ![![134, 67, 0], ![58, 31, 5]]]
 hmul := by decide  
 g := ![![![![42, -33, -1], ![67, 0, 0]], ![![4, -32, -1], ![67, 0, 0]]], ![![![-23, -32, -1], ![67, 0, 0]], ![![-1, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![25, 33, 1]] ![![67, 0, 0], ![-31, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-2077, 67, 0]], ![![1675, 2211, 67], ![-670, -1005, 134]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-31, 1, 0]]], ![![![25, 33, 1]], ![![-10, -15, 2]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-10, 5, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-10, 5, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![61, 5, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-10, 5, 1], ![105, -17, 25], ![525, -14, -17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-61, -5, 71]], ![![-1, 0, 1], ![-20, -2, 25], ![22, 1, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [69, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 70], [0, 1]]
 g := ![![[26, 15], [58, 36], [25, 54], [32], [6], [1]], ![[25, 56], [13, 35], [64, 17], [32], [6], [1]]]
 h' := ![![[52, 70], [45, 50], [50, 6], [36, 57], [16, 23], [2, 52], [0, 1]], ![[0, 1], [18, 21], [7, 65], [18, 14], [5, 48], [8, 19], [52, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [24, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [69, 19, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![489, 75, 15]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, 0, 15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-25, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-25, 1, 0]] 
 ![![71, 0, 0], ![46, 1, 0], ![17, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-25, 1, 0], ![0, -25, 5], ![105, -7, -25]]]
  hmulB := by decide  
  f := ![![![1601, -64, 0], ![4544, 0, 0]], ![![1026, -41, 0], ![2912, 0, 0]], ![![377, 5, -4], ![1070, 57, 0]]]
  g := ![![![1, 0, 0], ![-46, 71, 0], ![-17, 0, 71]], ![![-1, 1, 0], ![15, -25, 5], ![12, -7, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-10, 5, 1]] ![![71, 0, 0], ![-25, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1775, 71, 0]], ![![-710, 355, 71], ![355, -142, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-25, 1, 0]]], ![![![-10, 5, 1]], ![![5, -2, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![38, 14, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![38, 14, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![38, 14, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![38, 14, 1], ![105, 31, 70], ![1470, -77, 31]]]
  hmulB := by decide  
  f := ![![![-37, -14, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -14, 73]], ![![0, 0, 1], ![-35, -13, 70], ![4, -7, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [68, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 72], [0, 1]]
 g := ![![[6, 49], [49], [32], [51, 4], [24], [1]], ![[16, 24], [49], [32], [25, 69], [24], [1]]]
 h' := ![![[30, 72], [42, 66], [69, 66], [36, 18], [72, 71], [5, 30], [0, 1]], ![[0, 1], [51, 7], [5, 7], [65, 55], [12, 2], [29, 43], [30, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [4, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [68, 43, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4042, -106, 566]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-350, -110, 566]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![3, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![3, 1, 0]] 
 ![![73, 0, 0], ![3, 1, 0], ![42, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![3, 1, 0], ![0, 3, 5], ![105, -7, 3]]]
  hmulB := by decide  
  f := ![![![136, 45, 0], ![-3285, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![78, 24, -3], ![-1884, 44, 0]]]
  g := ![![![1, 0, 0], ![-3, 73, 0], ![-42, 0, 73]], ![![0, 1, 0], ![-3, 3, 5], ![0, -7, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![38, 14, 1]] ![![73, 0, 0], ![3, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![219, 73, 0]], ![![2774, 1022, 73], ![219, 73, 73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![3, 1, 0]]], ![![![38, 14, 1]], ![![3, 1, 1]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [41, 68, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 62, 7], [68, 16, 72], [0, 1]]
 g := ![![[55, 8, 52], [78, 45, 65], [52, 78, 67], [42, 60, 16], [25, 1], []], ![[60, 8, 73, 15], [58, 50, 12, 34], [22, 60, 75, 37], [42, 14, 69, 66], [17, 19], [39, 49]], ![[65, 60, 38, 10], [58, 50, 24, 40], [62, 59, 70, 13], [43, 34, 46, 21], [53, 52], [53, 49]]]
 h' := ![![[36, 62, 7], [41, 41, 17], [1, 0, 67], [16, 60, 15], [2, 76, 4], [0, 0, 1], [0, 1]], ![[68, 16, 72], [0, 62, 6], [3, 73, 45], [1, 54, 28], [25, 53, 43], [13, 40, 16], [36, 62, 7]], ![[0, 1], [19, 55, 56], [56, 6, 46], [18, 44, 36], [43, 29, 32], [2, 39, 62], [68, 16, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 50], []]
 b := ![[], [69, 35, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [41, 68, 54, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3397, 1185, 1422]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43, 15, 18]
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



lemma PB157I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB157I1 : PrimesBelowBoundCertificateInterval O 31 79 157 where
  m := 11
  g := ![1, 2, 2, 1, 2, 2, 2, 3, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB157I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N2]
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
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
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
  β := ![I41N1, I43N1, I53N1, I59N1, I61N1, I67N0, I67N1, I67N2, I71N1, I73N1]
  Il := ![[], [I41N1], [I43N1], [], [I53N1], [I59N1], [I61N1], [I67N0, I67N1, I67N2], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
