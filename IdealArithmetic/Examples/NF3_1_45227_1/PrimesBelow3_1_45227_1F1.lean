
import IdealArithmetic.Examples.NF3_1_45227_1.RI3_1_45227_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![15, -17, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![15, -17, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![15, 20, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![15, -17, 1], ![-10, -1, -50], ![-122, 269, -18]]]
  hmulB := by decide  
  f := ![![![-14, 17, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -20, 37]], ![![0, -1, 1], ![20, 27, -50], ![4, 17, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [6, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 36], [0, 1]]
 g := ![![[8, 36], [36], [21, 3], [10], [1]], ![[19, 1], [36], [25, 34], [10], [1]]]
 h' := ![![[26, 36], [9, 6], [22, 31], [13, 22], [31, 26], [0, 1]], ![[0, 1], [17, 31], [14, 6], [30, 15], [4, 11], [26, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [14, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [6, 11, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12, -132, -162]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![66, 84, -162]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![13, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![13, 1, 0]] 
 ![![37, 0, 0], ![13, 1, 0], ![18, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![13, 1, 0], ![1, 13, 3], ![7, -16, 14]]]
  hmulB := by decide  
  f := ![![![-254, -4155, -960], ![-185, 11840, 0]], ![![-99, -1455, -336], ![-36, 4144, 0]], ![![-132, -2022, -467], ![-66, 5760, 0]]]
  g := ![![![1, 0, 0], ![-13, 37, 0], ![-18, 0, 37]], ![![0, 1, 0], ![-6, 13, 3], ![-1, -16, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![15, -17, 1]] ![![37, 0, 0], ![13, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![481, 37, 0]], ![![555, -629, 37], ![185, -222, -37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![13, 1, 0]]], ![![![15, -17, 1]], ![![5, -6, -1]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [28, 27, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 12, 6], [26, 28, 35], [0, 1]]
 g := ![![[0, 1, 9], [10, 21], [14, 18], [34, 26, 1], []], ![[2, 20, 19, 38], [36, 9], [14, 21], [17, 21, 2, 30], [14, 36]], ![[32, 10, 27, 24], [2, 40], [5, 4], [25, 16, 22, 38], [26, 36]]]
 h' := ![![[0, 12, 6], [9, 9, 3], [17, 5, 12], [32, 35, 31], [0, 0, 1], [0, 1]], ![[26, 28, 35], [22, 9, 15], [28, 33, 38], [16, 12, 12], [18, 8, 28], [0, 12, 6]], ![[0, 1], [5, 23, 23], [15, 3, 32], [27, 35, 39], [30, 33, 12], [26, 28, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 5], []]
 b := ![[], [19, 7, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [28, 27, 15, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![35178, -35711, 73021]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![858, -871, 1781]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [33, 41, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 42, 3], [19, 0, 40], [0, 1]]
 g := ![![[41, 22, 11], [7, 17, 1], [21, 25], [3, 42, 1], []], ![[31, 11, 5, 34], [9, 29, 1, 37], [15, 15], [6, 29], [28, 9]], ![[9, 15, 12, 23], [12, 42, 0, 13], [3, 6], [42, 14, 5, 40], [34, 9]]]
 h' := ![![[23, 42, 3], [27, 33, 22], [35, 9, 1], [30, 39, 5], [0, 0, 1], [0, 1]], ![[19, 0, 40], [8, 17, 13], [19, 5, 27], [27, 31, 31], [35, 14], [23, 42, 3]], ![[0, 1], [37, 36, 8], [4, 29, 15], [19, 16, 7], [13, 29, 42], [19, 0, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 13], []]
 b := ![[], [17, 18, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [33, 41, 1, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-56545172, -193601007, -511622127]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1315004, -4502349, -11898189]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [46, 0, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 2, 21], [16, 44, 26], [0, 1]]
 g := ![![[15, 17, 9], [28, 41, 14], [38, 39, 36], [21, 31, 1], []], ![[23, 2, 2, 27], [36, 43, 29, 4], [22, 30, 11, 3], [43, 3, 44, 1], [31, 18]], ![[35, 26, 41, 41], [4, 20, 40, 33], [10, 41, 31, 39], [0, 46, 35, 10], [26, 18]]]
 h' := ![![[15, 2, 21], [28, 28, 44], [38, 10, 25], [21, 31, 41], [0, 0, 1], [0, 1]], ![[16, 44, 26], [9, 10, 33], [8, 43, 41], [31, 17, 11], [21, 31, 44], [15, 2, 21]], ![[0, 1], [6, 9, 17], [10, 41, 28], [0, 46, 42], [0, 16, 2], [16, 44, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 20], []]
 b := ![[], [5, 1, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [46, 0, 16, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-28294, 5123, -96021]
  a := ![-2, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-602, 109, -2043]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![35, 14, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![35, 14, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![35, 14, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![35, 14, 1], ![21, 19, 43], ![95, -227, 33]]]
  hmulB := by decide  
  f := ![![![-34, -14, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -14, 53]], ![![0, 0, 1], ![-28, -11, 43], ![-20, -13, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [33, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 52], [0, 1]]
 g := ![![[25, 37], [43], [10, 42], [43], [23, 1]], ![[28, 16], [43], [22, 11], [43], [46, 52]]]
 h' := ![![[23, 52], [50, 14], [41, 34], [36, 25], [36, 19], [0, 1]], ![[0, 1], [1, 39], [28, 19], [28, 28], [49, 34], [23, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [7, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [33, 30, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20, -151, -219]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![145, 55, -219]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![10, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![10, 1, 0]] 
 ![![53, 0, 0], ![10, 1, 0], ![20, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![10, 1, 0], ![1, 10, 3], ![7, -16, 11]]]
  hmulB := by decide  
  f := ![![![-143, -1440, -432], ![0, 7632, 0]], ![![-27, -270, -81], ![1, 1431, 0]], ![![-60, -544, -163], ![32, 2880, 0]]]
  g := ![![![1, 0, 0], ![-10, 53, 0], ![-20, 0, 53]], ![![0, 1, 0], ![-3, 10, 3], ![-1, -16, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![35, 14, 1]] ![![53, 0, 0], ![10, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![530, 53, 0]], ![![1855, 742, 53], ![371, 159, 53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![10, 1, 0]]], ![![![35, 14, 1]], ![![7, 3, 1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![28, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![28, 1, 0]] 
 ![![59, 0, 0], ![28, 1, 0], ![34, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![28, 1, 0], ![1, 28, 3], ![7, -16, 29]]]
  hmulB := by decide  
  f := ![![![539, 24460, 2622], ![708, -51566, 0]], ![![246, 11586, 1242], ![355, -24426, 0]], ![![294, 14095, 1511], ![443, -29716, 0]]]
  g := ![![![1, 0, 0], ![-28, 59, 0], ![-34, 0, 59]], ![![0, 1, 0], ![-15, 28, 3], ![-9, -16, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-15, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-15, 1, 0]] 
 ![![59, 0, 0], ![44, 1, 0], ![4, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-15, 1, 0], ![1, -15, 3], ![7, -16, -14]]]
  hmulB := by decide  
  f := ![![![776, -13193, 2640], ![-413, -51920, 0]], ![![582, -9835, 1968], ![-294, -38704, 0]], ![![61, -895, 179], ![5, -3520, 0]]]
  g := ![![![1, 0, 0], ![-44, 59, 0], ![-4, 0, 59]], ![![-1, 1, 0], ![11, -15, 3], ![13, -16, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-14, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-14, 1, 0]] 
 ![![59, 0, 0], ![45, 1, 0], ![53, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-14, 1, 0], ![1, -14, 3], ![7, -16, -13]]]
  hmulB := by decide  
  f := ![![![-496, 7933, -1701], ![295, 33453, 0]], ![![-375, 6044, -1296], ![237, 25488, 0]], ![![-442, 7126, -1528], ![280, 30051, 0]]]
  g := ![![![1, 0, 0], ![-45, 59, 0], ![-53, 0, 59]], ![![-1, 1, 0], ![8, -14, 3], ![24, -16, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![28, 1, 0]] ![![59, 0, 0], ![-15, 1, 0]]
  ![![59, 0, 0], ![-2, 24, 1]] where
 M := ![![![3481, 0, 0], ![-885, 59, 0]], ![![1652, 59, 0], ![-419, 13, 3]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![-13, -23, -1], ![59, 0, 0]]], ![![![28, 1, 0], ![0, 0, 0]], ![![-7, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-2, 24, 1]] ![![59, 0, 0], ![-14, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-826, 59, 0]], ![![-118, 1416, 59], ![59, -354, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-14, 1, 0]]], ![![![-2, 24, 1]], ![![1, -6, 1]]]]
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


lemma PB61I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 60 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 60 (by omega)

def PB61I1 : PrimesBelowBoundCertificateInterval O 31 60 61 where
  m := 6
  g := ![2, 1, 1, 1, 2, 3]
  P := ![37, 41, 43, 47, 53, 59]
  hP := PB61I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1369, 37]
    · exact ![68921]
    · exact ![79507]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
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
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
  β := ![I37N1, I53N1, I59N0, I59N1, I59N2]
  Il := ![[I37N1], [], [], [], [I53N1], [I59N0, I59N1, I59N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
