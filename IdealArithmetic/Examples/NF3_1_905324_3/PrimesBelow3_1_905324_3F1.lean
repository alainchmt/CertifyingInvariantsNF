
import IdealArithmetic.Examples.NF3_1_905324_3.RI3_1_905324_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![26, 7, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![26, 7, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![26, 7, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![26, 7, 1], ![182, 12, 7], ![1274, 84, 12]]]
  hmulB := by decide  
  f := ![![![-25, -7, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -7, 37]], ![![0, 0, 1], ![0, -1, 7], ![26, 0, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [2, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 36], [0, 1]]
 g := ![![[32, 11], [7], [10, 4], [26], [1]], ![[31, 26], [7], [13, 33], [26], [1]]]
 h' := ![![[10, 36], [16, 23], [17, 28], [26, 35], [35, 10], [0, 1]], ![[0, 1], [24, 14], [1, 9], [6, 2], [24, 27], [10, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [17, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [2, 27, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![366, 127, -40]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38, 11, -40]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-7, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-7, 1, 0]] 
 ![![37, 0, 0], ![30, 1, 0], ![25, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-7, 1, 0], ![0, -7, 1], ![182, -14, -7]]]
  hmulB := by decide  
  f := ![![![141, -20, 0], ![740, 0, 0]], ![![120, -17, 0], ![630, 0, 0]], ![![93, -13, 0], ![488, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 37, 0], ![-25, 0, 37]], ![![-1, 1, 0], ![5, -7, 1], ![21, -14, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![26, 7, 1]] ![![37, 0, 0], ![-7, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-259, 37, 0]], ![![962, 259, 37], ![0, -37, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-7, 1, 0]]], ![![![26, 7, 1]], ![![0, -1, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-7, 15, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-7, 15, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![34, 15, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-7, 15, 1], ![182, -21, 15], ![2730, -28, -21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -15, 41]], ![![-1, 0, 1], ![-8, -6, 15], ![84, 7, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [21, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 40], [0, 1]]
 g := ![![[27, 2], [1], [1], [8, 8], [1]], ![[0, 39], [1], [1], [23, 33], [1]]]
 h' := ![![[7, 40], [4, 17], [36, 40], [37, 1], [20, 7], [0, 1]], ![[0, 1], [0, 24], [29, 1], [3, 40], [28, 34], [7, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [8, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [21, 34, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2196, 1742, -26]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32, 52, -26]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-15, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-15, 1, 0]] 
 ![![41, 0, 0], ![26, 1, 0], ![21, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-15, 1, 0], ![0, -15, 1], ![182, -14, -15]]]
  hmulB := by decide  
  f := ![![![256, -17, 0], ![697, 0, 0]], ![![166, -11, 0], ![452, 0, 0]], ![![126, -8, 0], ![343, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 41, 0], ![-21, 0, 41]], ![![-1, 1, 0], ![9, -15, 1], ![21, -14, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-7, 15, 1]] ![![41, 0, 0], ![-15, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-615, 41, 0]], ![![-287, 615, 41], ![287, -246, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-15, 1, 0]]], ![![![-7, 15, 1]], ![![7, -6, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [11, 0, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 2, 5], [17, 40, 38], [0, 1]]
 g := ![![[36, 1, 21], [37, 27, 40], [11, 10], [21, 8, 1], []], ![[14, 2, 0, 18], [16, 9, 4, 3], [25, 21], [6, 23, 33, 2], [5, 25]], ![[31, 1, 21, 38], [33, 34, 28, 23], [16, 13], [9, 12, 15, 23], [15, 25]]]
 h' := ![![[34, 2, 5], [23, 40, 35], [6, 40, 13], [27, 41, 28], [0, 0, 1], [0, 1]], ![[17, 40, 38], [14, 31, 9], [27, 36, 32], [42, 17, 35], [26, 33, 40], [34, 2, 5]], ![[0, 1], [12, 15, 42], [19, 10, 41], [25, 28, 23], [38, 10, 2], [17, 40, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13], []]
 b := ![[], [11, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [11, 0, 35, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-102211, -20038, -5375]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2377, -466, -125]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [19, 15, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 33, 23], [17, 13, 24], [0, 1]]
 g := ![![[26, 35, 37], [38, 42, 3], [31, 21, 27], [34, 40, 1], []], ![[25, 42, 33, 22], [16, 1, 9, 23], [33, 25, 39, 40], [30, 37, 24, 33], [24, 12]], ![[5, 25, 10, 28], [37, 14, 24, 37], [2, 38, 35, 37], [45, 40, 30, 4], [23, 12]]]
 h' := ![![[23, 33, 23], [30, 9, 32], [22, 32, 12], [12, 46, 36], [0, 0, 1], [0, 1]], ![[17, 13, 24], [35, 24, 12], [36, 43, 46], [32, 30, 22], [26, 37, 13], [23, 33, 23]], ![[0, 1], [6, 14, 3], [12, 19, 36], [25, 18, 36], [40, 10, 33], [17, 13, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 36], []]
 b := ![[], [29, 3, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [19, 15, 7, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-973840, 158484, -1598]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20720, 3372, -34]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![4, 19, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![4, 19, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![4, 19, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![4, 19, 1], ![182, -10, 19], ![3458, -84, -10]]]
  hmulB := by decide  
  f := ![![![-3, -19, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -19, 53]], ![![0, 0, 1], ![2, -7, 19], ![66, 2, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [50, 16, 1] where
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
 g := ![![[30, 1], [10], [], [36], [37, 1]], ![[14, 52], [10], [], [36], [21, 52]]]
 h' := ![![[37, 52], [30, 52], [0, 40], [27], [5, 47], [0, 1]], ![[0, 1], [46, 1], [49, 13], [27], [48, 6], [37, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [30, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [50, 16, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![414, 138, -29]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, 13, -29]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-19, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-19, 1, 0]] 
 ![![53, 0, 0], ![34, 1, 0], ![10, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-19, 1, 0], ![0, -19, 1], ![182, -14, -19]]]
  hmulB := by decide  
  f := ![![![419, -22, 0], ![1166, 0, 0]], ![![286, -15, 0], ![796, 0, 0]], ![![102, -5, 0], ![284, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 53, 0], ![-10, 0, 53]], ![![-1, 1, 0], ![12, -19, 1], ![16, -14, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![4, 19, 1]] ![![53, 0, 0], ![-19, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1007, 53, 0]], ![![212, 1007, 53], ![106, -371, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-19, 1, 0]]], ![![![4, 19, 1]], ![![2, -7, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-9, 6, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-9, 6, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![50, 6, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-9, 6, 1], ![182, -23, 6], ![1092, 98, -23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-50, -6, 59]], ![![-1, 0, 1], ![-2, -1, 6], ![38, 4, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [41, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 58], [0, 1]]
 g := ![![[23, 36], [20, 7], [46], [42, 7], [1, 1]], ![[0, 23], [27, 52], [46], [49, 52], [2, 58]]]
 h' := ![![[1, 58], [6, 53], [5, 19], [48, 20], [18, 19], [0, 1]], ![[0, 1], [0, 6], [24, 40], [9, 39], [37, 40], [1, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [38, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [41, 58, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7016, 790, 407]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-226, -28, 407]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-6, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-6, 1, 0]] 
 ![![59, 0, 0], ![53, 1, 0], ![23, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-6, 1, 0], ![0, -6, 1], ![182, -14, -6]]]
  hmulB := by decide  
  f := ![![![73, -12, 0], ![708, 0, 0]], ![![67, -11, 0], ![650, 0, 0]], ![![37, -6, 0], ![360, 1, 0]]]
  g := ![![![1, 0, 0], ![-53, 59, 0], ![-23, 0, 59]], ![![-1, 1, 0], ![5, -6, 1], ![18, -14, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-9, 6, 1]] ![![59, 0, 0], ![-6, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-354, 59, 0]], ![![-531, 354, 59], ![236, -59, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-6, 1, 0]]], ![![![-9, 6, 1]], ![![4, -1, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![34, -9, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![34, -9, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![34, 52, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![34, -9, 1], ![182, 20, -9], ![-1638, 308, 20]]]
  hmulB := by decide  
  f := ![![![-33, 9, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -52, 61]], ![![0, -1, 1], ![8, 8, -9], ![-38, -12, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [43, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 60], [0, 1]]
 g := ![![[21, 9], [36], [13, 41], [2, 14], [12, 1]], ![[7, 52], [36], [17, 20], [48, 47], [24, 60]]]
 h' := ![![[12, 60], [16, 3], [51, 55], [36, 23], [33, 40], [0, 1]], ![[0, 1], [52, 58], [40, 6], [7, 38], [25, 21], [12, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [17, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [43, 49, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1097, 407, -52]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 51, -52]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![9, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![9, 1, 0]] 
 ![![61, 0, 0], ![9, 1, 0], ![41, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![9, 1, 0], ![0, 9, 1], ![182, -14, 9]]]
  hmulB := by decide  
  f := ![![![253, 28, 0], ![-1708, 0, 0]], ![![27, 3, 0], ![-182, 0, 0]], ![![173, 19, 0], ![-1168, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 61, 0], ![-41, 0, 61]], ![![0, 1, 0], ![-2, 9, 1], ![-1, -14, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![34, -9, 1]] ![![61, 0, 0], ![9, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![549, 61, 0]], ![![2074, -549, 61], ![488, -61, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![9, 1, 0]]], ![![![34, -9, 1]], ![![8, -1, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [4, 41, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 46, 64], [3, 20, 3], [0, 1]]
 g := ![![[65, 19, 9], [61, 49, 60], [24, 59], [12, 35], [11, 1], []], ![[16, 32, 46, 16], [27, 24, 51, 25], [33, 19], [47, 21], [8, 65], [24, 9]], ![[12, 46, 10, 2], [39, 16, 23, 57], [27, 25], [50, 29], [25, 39], [18, 9]]]
 h' := ![![[8, 46, 64], [24, 9, 3], [48, 6, 44], [12, 12, 27], [23, 14, 13], [0, 0, 1], [0, 1]], ![[3, 20, 3], [0, 31, 33], [28, 41, 58], [48, 53, 35], [54, 34, 17], [35, 51, 20], [8, 46, 64]], ![[0, 1], [63, 27, 31], [41, 20, 32], [22, 2, 5], [50, 19, 37], [4, 16, 46], [3, 20, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 11], []]
 b := ![[], [53, 52, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [4, 41, 56, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![275370, 335, 670]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4110, 5, 10]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-93, 24, -1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-93, 24, -1]] 
 ![![71, 0, 0], ![0, 71, 0], ![22, 47, 1]] where
  M :=![![![-93, 24, -1], ![-182, -79, 24], ![4368, -518, -79]]]
  hmulB := by decide  
  f := ![![![-263, -34, -7]], ![![-1274, -165, -34]], ![![-1012, -131, -27]]]
  g := ![![![-1, 1, -1], ![-10, -17, 24], ![86, 45, -79]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [56, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 70], [0, 1]]
 g := ![![[41, 27], [42, 16], [], [50], [8], [1]], ![[32, 44], [13, 55], [], [50], [8], [1]]]
 h' := ![![[47, 70], [62, 13], [0, 4], [69], [61, 11], [15, 47], [0, 1]], ![[0, 1], [34, 58], [46, 67], [69], [10, 60], [23, 24], [47, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [8, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [56, 24, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7172, 1008, 100]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-132, -52, 100]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 34, 7]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![263, 34, 7]] 
 ![![71, 0, 0], ![24, 1, 0], ![63, 0, 1]] where
  M :=![![![263, 34, 7], ![1274, 165, 34], ![6188, 798, 165]]]
  hmulB := by decide  
  f := ![![![93, -24, 1]], ![![34, -7, 0]], ![![21, -14, 2]]]
  g := ![![![-14, 34, 7], ![-68, 165, 34], ![-329, 798, 165]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-93, 24, -1]] ![![263, 34, 7]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![18, 2, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![18, 2, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![18, 2, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![18, 2, 1], ![182, 4, 2], ![364, 154, 4]]]
  hmulB := by decide  
  f := ![![![-17, -2, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -2, 73]], ![![0, 0, 1], ![2, 0, 2], ![4, 2, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [11, 4, 1] where
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
 g := ![![[7, 72], [70], [67], [20, 65], [16], [1]], ![[11, 1], [70], [67], [52, 8], [16], [1]]]
 h' := ![![[69, 72], [69, 27], [67, 17], [72, 40], [18, 24], [62, 69], [0, 1]], ![[0, 1], [34, 46], [72, 56], [58, 33], [68, 49], [5, 4], [69, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [21, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [11, 4, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-132, 180, 17]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, 2, 17]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-2, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-2, 1, 0]] 
 ![![73, 0, 0], ![71, 1, 0], ![69, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-2, 1, 0], ![0, -2, 1], ![182, -14, -2]]]
  hmulB := by decide  
  f := ![![![79, -39, 0], ![2847, 0, 0]], ![![77, -38, 0], ![2775, 0, 0]], ![![75, -37, 0], ![2703, 1, 0]]]
  g := ![![![1, 0, 0], ![-71, 73, 0], ![-69, 0, 73]], ![![-1, 1, 0], ![1, -2, 1], ![18, -14, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![18, 2, 1]] ![![73, 0, 0], ![-2, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-146, 73, 0]], ![![1314, 146, 73], ![146, 0, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-2, 1, 0]]], ![![![18, 2, 1]], ![![2, 0, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [56, 33, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 24, 64], [7, 54, 15], [0, 1]]
 g := ![![[56, 13, 40], [32, 17, 73], [34, 25, 36], [12, 23, 5], [31, 1], []], ![[73, 47, 45, 23], [34, 67, 52, 13], [64, 50, 54, 49], [56, 36, 46, 31], [18, 72], [14, 67]], ![[65, 30, 22, 14], [16, 28, 74, 39], [74, 39, 3, 57], [12, 31, 1, 3], [38, 23], [63, 67]]]
 h' := ![![[24, 24, 64], [25, 31, 35], [71, 26, 51], [39, 58, 73], [2, 27, 59], [0, 0, 1], [0, 1]], ![[7, 54, 15], [46, 66, 3], [41, 13, 73], [72, 14, 70], [70, 31, 16], [29, 19, 54], [24, 24, 64]], ![[0, 1], [58, 61, 41], [21, 40, 34], [68, 7, 15], [14, 21, 4], [76, 60, 24], [7, 54, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 64], []]
 b := ![[], [66, 51, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [56, 33, 48, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![60198, -2054, -1738]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![762, -26, -22]
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



lemma PB270I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB270I1 : PrimesBelowBoundCertificateInterval O 31 79 270 where
  m := 11
  g := ![2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB270I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
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
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
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
  β := ![I37N1, I41N1, I53N1, I59N1, I61N1, I71N1, I73N1]
  Il := ![[I37N1], [I41N1], [], [], [I53N1], [I59N1], [I61N1], [], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
