
import IdealArithmetic.Examples.NF3_1_406700_5.RI3_1_406700_5
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [29, 18, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 28, 18], [21, 8, 19], [0, 1]]
 g := ![![[32, 26, 26], [10, 33], [3, 31, 26], [18, 1], []], ![[33, 29, 4, 31], [20, 7], [12, 32, 10, 20], [10, 27], [32, 28]], ![[20, 7, 24, 23], [2, 9], [20, 0, 36, 5], [16, 7], [31, 28]]]
 h' := ![![[34, 28, 18], [27, 26, 10], [24, 25, 12], [33, 17, 10], [0, 0, 1], [0, 1]], ![[21, 8, 19], [9, 5, 30], [21, 10, 28], [5, 12, 16], [6, 35, 8], [34, 28, 18]], ![[0, 1], [26, 6, 34], [11, 2, 34], [28, 8, 11], [23, 2, 28], [21, 8, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 20], []]
 b := ![[], [15, 4, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [29, 18, 19, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3552, -11988, -2553]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![96, -324, -69]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [7, 16, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 9, 36], [22, 31, 5], [0, 1]]
 g := ![![[32, 7, 16], [4, 9], [11, 36], [34, 3, 1], []], ![[12, 8, 4, 36], [2, 16], [21, 37], [3, 22, 31, 33], [26, 25]], ![[23, 4, 34, 2], [6, 1], [31, 2], [8, 36, 38, 36], [16, 25]]]
 h' := ![![[22, 9, 36], [18, 0, 4], [28, 3, 3], [8, 9, 6], [0, 0, 1], [0, 1]], ![[22, 31, 5], [37, 40, 1], [16, 16, 37], [9, 18, 18], [15, 10, 31], [22, 9, 36]], ![[0, 1], [30, 1, 36], [21, 22, 1], [19, 14, 17], [3, 31, 9], [22, 31, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 24], []]
 b := ![[], [40, 34, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [7, 16, 38, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3239, -23780, 44280]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![79, -580, 1080]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![18, -17, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![18, -17, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![18, 26, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![18, -17, 1], ![13, -29, -16], ![-208, 765, -45]]]
  hmulB := by decide  
  f := ![![![-17, 17, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -26, 43]], ![![0, -1, 1], ![7, 9, -16], ![14, 45, -45]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [15, 20, 1] where
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
 g := ![![[30, 23], [24, 9], [17], [39, 13], [1]], ![[0, 20], [16, 34], [17], [37, 30], [1]]]
 h' := ![![[23, 42], [27, 25], [34, 3], [17, 24], [28, 23], [0, 1]], ![[0, 1], [0, 18], [17, 40], [10, 19], [41, 20], [23, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [5, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [15, 20, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2818, -48, 61]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![40, -38, 61]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![16, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![16, 1, 0]] 
 ![![43, 0, 0], ![16, 1, 0], ![2, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![16, 1, 0], ![0, 16, 1], ![13, -47, 17]]]
  hmulB := by decide  
  f := ![![![241, 15, 0], ![-645, 0, 0]], ![![80, 5, 0], ![-214, 0, 0]], ![![6, 0, 0], ![-16, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 43, 0], ![-2, 0, 43]], ![![0, 1, 0], ![-6, 16, 1], ![17, -47, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![18, -17, 1]] ![![43, 0, 0], ![16, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![688, 43, 0]], ![![774, -731, 43], ![301, -301, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![16, 1, 0]]], ![![![18, -17, 1]], ![![7, -7, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![44, -21, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![44, -21, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![44, 26, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![44, -21, 1], ![13, -3, -20], ![-260, 953, -23]]]
  hmulB := by decide  
  f := ![![![-43, 21, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -26, 47]], ![![0, -1, 1], ![19, 11, -20], ![16, 33, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [29, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 46], [0, 1]]
 g := ![![[26, 18], [8, 37], [23, 17], [14, 4], [1]], ![[37, 29], [28, 10], [36, 30], [6, 43], [1]]]
 h' := ![![[45, 46], [3, 26], [38, 32], [17, 39], [18, 45], [0, 1]], ![[0, 1], [45, 21], [21, 15], [33, 8], [22, 2], [45, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [21, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [29, 2, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![71, -20, -431]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![405, 238, -431]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![20, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![20, 1, 0]] 
 ![![47, 0, 0], ![20, 1, 0], ![23, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![20, 1, 0], ![0, 20, 1], ![13, -47, 21]]]
  hmulB := by decide  
  f := ![![![281, 14, 0], ![-658, 0, 0]], ![![100, 5, 0], ![-234, 0, 0]], ![![129, 6, 0], ![-302, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 47, 0], ![-23, 0, 47]], ![![0, 1, 0], ![-9, 20, 1], ![10, -47, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![44, -21, 1]] ![![47, 0, 0], ![20, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![940, 47, 0]], ![![2068, -987, 47], ![893, -423, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![20, 1, 0]]], ![![![44, -21, 1]], ![![19, -9, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![16, 23, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![16, 23, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![16, 23, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![16, 23, 1], ![13, -31, 24], ![312, -1115, -7]]]
  hmulB := by decide  
  f := ![![![-15, -23, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -23, 53]], ![![0, 0, 1], ![-7, -11, 24], ![8, -18, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [10, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 52], [0, 1]]
 g := ![![[5, 16], [9], [27, 47], [1], [3, 1]], ![[0, 37], [9], [9, 6], [1], [6, 52]]]
 h' := ![![[3, 52], [41, 4], [48, 50], [42, 10], [23, 52], [0, 1]], ![[0, 1], [0, 49], [39, 3], [19, 43], [20, 1], [3, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [17, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [10, 50, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![49, -178, -93]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, 37, -93]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-24, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-24, 1, 0]] 
 ![![53, 0, 0], ![29, 1, 0], ![7, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-24, 1, 0], ![0, -24, 1], ![13, -47, -23]]]
  hmulB := by decide  
  f := ![![![1201, -50, 0], ![2650, 0, 0]], ![![649, -27, 0], ![1432, 0, 0]], ![![155, -6, 0], ![342, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 53, 0], ![-7, 0, 53]], ![![-1, 1, 0], ![13, -24, 1], ![29, -47, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![16, 23, 1]] ![![53, 0, 0], ![-24, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1272, 53, 0]], ![![848, 1219, 53], ![-371, -583, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-24, 1, 0]]], ![![![16, 23, 1]], ![![-7, -11, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-29, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-29, 1, 0]] 
 ![![59, 0, 0], ![30, 1, 0], ![44, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-29, 1, 0], ![0, -29, 1], ![13, -47, -28]]]
  hmulB := by decide  
  f := ![![![1712, -59, 0], ![3481, 0, 0]], ![![900, -31, 0], ![1830, 0, 0]], ![![1320, -45, 0], ![2684, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 59, 0], ![-44, 0, 59]], ![![-1, 1, 0], ![14, -29, 1], ![45, -47, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-21, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-21, 1, 0]] 
 ![![59, 0, 0], ![38, 1, 0], ![31, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-21, 1, 0], ![0, -21, 1], ![13, -47, -20]]]
  hmulB := by decide  
  f := ![![![1114, -53, 0], ![3127, 0, 0]], ![![736, -35, 0], ![2066, 0, 0]], ![![596, -28, 0], ![1673, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 59, 0], ![-31, 0, 59]], ![![-1, 1, 0], ![13, -21, 1], ![41, -47, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-10, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-10, 1, 0]] 
 ![![59, 0, 0], ![49, 1, 0], ![18, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-10, 1, 0], ![0, -10, 1], ![13, -47, -9]]]
  hmulB := by decide  
  f := ![![![81, -8, 0], ![472, 0, 0]], ![![71, -7, 0], ![414, 0, 0]], ![![42, -4, 0], ![246, 1, 0]]]
  g := ![![![1, 0, 0], ![-49, 59, 0], ![-18, 0, 59]], ![![-1, 1, 0], ![8, -10, 1], ![42, -47, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-29, 1, 0]] ![![59, 0, 0], ![-21, 1, 0]]
  ![![59, 0, 0], ![19, 9, 1]] where
 M := ![![![3481, 0, 0], ![-1239, 59, 0]], ![![-1711, 59, 0], ![609, -50, 1]]]
 hmul := by decide  
 g := ![![![![40, -9, -1], ![59, 0, 0]], ![![-21, 1, 0], ![0, 0, 0]]], ![![![-29, 1, 0], ![0, 0, 0]], ![![-9, -10, -1], ![60, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![19, 9, 1]] ![![59, 0, 0], ![-10, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-590, 59, 0]], ![![1121, 531, 59], ![-177, -118, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-10, 1, 0]]], ![![![19, 9, 1]], ![![-3, -2, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![18, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![18, 1, 0]] 
 ![![61, 0, 0], ![18, 1, 0], ![42, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![18, 1, 0], ![0, 18, 1], ![13, -47, 19]]]
  hmulB := by decide  
  f := ![![![235, 13, 0], ![-793, 0, 0]], ![![54, 3, 0], ![-182, 0, 0]], ![![150, 8, 0], ![-506, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 61, 0], ![-42, 0, 61]], ![![0, 1, 0], ![-6, 18, 1], ![1, -47, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-12, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-12, 1, 0]] 
 ![![61, 0, 0], ![49, 1, 0], ![39, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-12, 1, 0], ![0, -12, 1], ![13, -47, -11]]]
  hmulB := by decide  
  f := ![![![697, -58, 0], ![3538, 0, 0]], ![![565, -47, 0], ![2868, 0, 0]], ![![459, -38, 0], ![2330, 1, 0]]]
  g := ![![![1, 0, 0], ![-49, 61, 0], ![-39, 0, 61]], ![![-1, 1, 0], ![9, -12, 1], ![45, -47, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-7, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-7, 1, 0]] 
 ![![61, 0, 0], ![54, 1, 0], ![12, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-7, 1, 0], ![0, -7, 1], ![13, -47, -6]]]
  hmulB := by decide  
  f := ![![![274, -39, 0], ![2379, 0, 0]], ![![246, -35, 0], ![2136, 0, 0]], ![![64, -9, 0], ![556, 1, 0]]]
  g := ![![![1, 0, 0], ![-54, 61, 0], ![-12, 0, 61]], ![![-1, 1, 0], ![6, -7, 1], ![43, -47, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![18, 1, 0]] ![![61, 0, 0], ![-12, 1, 0]]
  ![![61, 0, 0], ![28, 6, 1]] where
 M := ![![![3721, 0, 0], ![-732, 61, 0]], ![![1098, 61, 0], ![-216, 6, 1]]]
 hmul := by decide  
 g := ![![![![33, -6, -1], ![61, 0, 0]], ![![-12, 1, 0], ![0, 0, 0]]], ![![![-10, -5, -1], ![61, 0, 0]], ![![-4, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![28, 6, 1]] ![![61, 0, 0], ![-7, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-427, 61, 0]], ![![1708, 366, 61], ![-183, -61, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-7, 1, 0]]], ![![![28, 6, 1]], ![![-3, -1, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![31, -33, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![31, -33, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![31, 34, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![31, -33, 1], ![13, -16, -32], ![-416, 1517, -48]]]
  hmulB := by decide  
  f := ![![![-30, 33, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -34, 67]], ![![0, -1, 1], ![15, 16, -32], ![16, 47, -48]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [12, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 66], [0, 1]]
 g := ![![[63, 40], [39, 10], [25], [37], [26], [1]], ![[40, 27], [50, 57], [25], [37], [26], [1]]]
 h' := ![![[48, 66], [1, 43], [57, 12], [42, 5], [33, 29], [55, 48], [0, 1]], ![[0, 1], [55, 24], [30, 55], [14, 62], [18, 38], [14, 19], [48, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [10, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [12, 19, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![539, -1421, 374]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-165, -211, 374]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![32, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![32, 1, 0]] 
 ![![67, 0, 0], ![32, 1, 0], ![48, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![32, 1, 0], ![0, 32, 1], ![13, -47, 33]]]
  hmulB := by decide  
  f := ![![![641, 20, 0], ![-1340, 0, 0]], ![![288, 9, 0], ![-602, 0, 0]], ![![464, 14, 0], ![-970, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 67, 0], ![-48, 0, 67]], ![![0, 1, 0], ![-16, 32, 1], ![-1, -47, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![31, -33, 1]] ![![67, 0, 0], ![32, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![2144, 67, 0]], ![![2077, -2211, 67], ![1005, -1072, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![32, 1, 0]]], ![![![31, -33, 1]], ![![15, -16, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![54, -31, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![54, -31, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![54, 40, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![54, -31, 1], ![13, 7, -30], ![-390, 1423, -23]]]
  hmulB := by decide  
  f := ![![![-53, 31, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-54, -40, 71]], ![![0, -1, 1], ![23, 17, -30], ![12, 33, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [64, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 70], [0, 1]]
 g := ![![[23, 10], [6, 5], [22, 8], [57], [6], [1]], ![[0, 61], [30, 66], [32, 63], [57], [6], [1]]]
 h' := ![![[19, 70], [42, 9], [12, 17], [18, 24], [20, 25], [7, 19], [0, 1]], ![[0, 1], [0, 62], [51, 54], [48, 47], [69, 46], [13, 52], [19, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [11, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [64, 52, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-52, 398, -93]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![70, 58, -93]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![30, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![30, 1, 0]] 
 ![![71, 0, 0], ![30, 1, 0], ![23, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![30, 1, 0], ![0, 30, 1], ![13, -47, 31]]]
  hmulB := by decide  
  f := ![![![691, 23, 0], ![-1633, 0, 0]], ![![270, 9, 0], ![-638, 0, 0]], ![![223, 7, 0], ![-527, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 71, 0], ![-23, 0, 71]], ![![0, 1, 0], ![-13, 30, 1], ![10, -47, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![54, -31, 1]] ![![71, 0, 0], ![30, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![2130, 71, 0]], ![![3834, -2201, 71], ![1633, -923, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![30, 1, 0]]], ![![![54, -31, 1]], ![![23, -13, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![53, 2, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![53, 2, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![53, 2, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![53, 2, 1], ![13, 6, 3], ![39, -128, 9]]]
  hmulB := by decide  
  f := ![![![-52, -2, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -2, 73]], ![![0, 0, 1], ![-2, 0, 3], ![-6, -2, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [54, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 72], [0, 1]]
 g := ![![[66, 23], [2], [18], [13, 27], [23], [1]], ![[0, 50], [2], [18], [72, 46], [23], [1]]]
 h' := ![![[13, 72], [50, 13], [31, 41], [28, 50], [68, 63], [19, 13], [0, 1]], ![[0, 1], [0, 60], [53, 32], [21, 23], [11, 10], [42, 60], [13, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [37, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [54, 60, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![158, -264, -59]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![45, -2, -59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-3, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-3, 1, 0]] 
 ![![73, 0, 0], ![70, 1, 0], ![64, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-3, 1, 0], ![0, -3, 1], ![13, -47, -2]]]
  hmulB := by decide  
  f := ![![![154, -51, 0], ![3723, 0, 0]], ![![148, -49, 0], ![3578, 0, 0]], ![![136, -45, 0], ![3288, 1, 0]]]
  g := ![![![1, 0, 0], ![-70, 73, 0], ![-64, 0, 73]], ![![-1, 1, 0], ![2, -3, 1], ![47, -47, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![53, 2, 1]] ![![73, 0, 0], ![-3, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-219, 73, 0]], ![![3869, 146, 73], ![-146, 0, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-3, 1, 0]]], ![![![53, 2, 1]], ![![-2, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![45, -13, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![45, -13, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![45, 66, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![45, -13, 1], ![13, -2, -12], ![-156, 577, -14]]]
  hmulB := by decide  
  f := ![![![-44, 13, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -66, 79]], ![![0, -1, 1], ![7, 10, -12], ![6, 19, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [12, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 78], [0, 1]]
 g := ![![[50, 67], [44, 20], [3, 20], [72, 25], [76], [1]], ![[61, 12], [52, 59], [11, 59], [3, 54], [76], [1]]]
 h' := ![![[32, 78], [25, 15], [43, 39], [5, 39], [22, 5], [67, 32], [0, 1]], ![[0, 1], [31, 64], [27, 40], [68, 40], [24, 74], [64, 47], [32, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [35, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [12, 47, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-358, 1234, -22]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, 34, -22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![12, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![12, 1, 0]] 
 ![![79, 0, 0], ![12, 1, 0], ![14, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![12, 1, 0], ![0, 12, 1], ![13, -47, 13]]]
  hmulB := by decide  
  f := ![![![325, 27, 0], ![-2133, 0, 0]], ![![36, 3, 0], ![-236, 0, 0]], ![![50, 4, 0], ![-328, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 79, 0], ![-14, 0, 79]], ![![0, 1, 0], ![-2, 12, 1], ![5, -47, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![45, -13, 1]] ![![79, 0, 0], ![12, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![948, 79, 0]], ![![3555, -1027, 79], ![553, -158, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![12, 1, 0]]], ![![![45, -13, 1]], ![![7, -2, 0]]]]
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


lemma PB181I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB181I1 : PrimesBelowBoundCertificateInterval O 31 79 181 where
  m := 11
  g := ![1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB181I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1]
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
    · exact ![50653]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![61, 61, 61]
    · exact ![4489, 67]
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
      exact NI47N1
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
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
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
  β := ![I43N1, I47N1, I53N1, I59N0, I59N1, I59N2, I61N0, I61N1, I61N2, I67N1, I71N1, I73N1, I79N1]
  Il := ![[], [], [I43N1], [I47N1], [I53N1], [I59N0, I59N1, I59N2], [I61N0, I61N1, I61N2], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
