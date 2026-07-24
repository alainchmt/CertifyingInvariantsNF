
import IdealArithmetic.Examples.NF3_1_331240_2.RI3_1_331240_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [19, 31, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 30, 22], [14, 6, 15], [0, 1]]
 g := ![![[28, 0, 30], [35, 30], [22, 31, 36], [0, 1], []], ![[2, 29, 11, 6], [25, 28], [13, 30, 6, 23], [27, 36], [25, 3]], ![[10, 29, 18, 35], [11, 4], [31, 26, 21, 22], [13, 12], [32, 3]]]
 h' := ![![[23, 30, 22], [11, 0, 20], [26, 24, 20], [0, 18, 6], [0, 0, 1], [0, 1]], ![[14, 6, 15], [18, 8, 9], [30, 25, 19], [35, 17, 25], [17, 30, 6], [23, 30, 22]], ![[0, 1], [22, 29, 8], [3, 25, 35], [0, 2, 6], [32, 7, 30], [14, 6, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 15], []]
 b := ![[], [1, 36, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [19, 31, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9277491, -348096, -238761]
  a := ![0, 9, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-250743, -9408, -6453]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [37, 8, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 27, 22], [2, 13, 19], [0, 1]]
 g := ![![[40, 17, 36], [33, 36], [22, 5], [37, 39, 1], []], ![[19, 31, 1, 6], [20, 16], [15, 18], [7, 10, 36, 28], [15, 33]], ![[23, 31, 37, 27], [23, 18], [34, 37], [30, 8, 19, 34], [18, 33]]]
 h' := ![![[37, 27, 22], [19, 37, 35], [16, 19, 6], [25, 24, 28], [0, 0, 1], [0, 1]], ![[2, 13, 19], [30, 9, 39], [27, 27, 4], [7, 20, 31], [35, 1, 13], [37, 27, 22]], ![[0, 1], [6, 36, 8], [18, 36, 31], [28, 38, 23], [35, 40, 27], [2, 13, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 30], []]
 b := ![[], [6, 17, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [37, 8, 2, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3860150, 150921, 80483]
  a := ![-1, -7, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![94150, 3681, 1963]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-20, -3, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-20, -3, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![23, 40, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-20, -3, 1], ![110, -5, -27], ![-220, 10, -32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -40, 43]], ![![-1, -1, 1], ![17, 25, -27], ![12, 30, -32]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [10, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 42], [0, 1]]
 g := ![![[9, 13], [8, 13], [25], [16, 16], [1]], ![[0, 30], [42, 30], [25], [38, 27], [1]]]
 h' := ![![[39, 42], [6, 23], [23, 20], [12, 5], [33, 39], [0, 1]], ![[0, 1], [0, 20], [29, 23], [35, 38], [6, 4], [39, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [36, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [10, 4, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3850, -89, 259]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-49, -243, 259]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-16, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-16, 1, 0]] 
 ![![43, 0, 0], ![27, 1, 0], ![32, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-16, 1, 0], ![0, -21, 11], ![110, 0, -10]]]
  hmulB := by decide  
  f := ![![![689, -43, 0], ![1849, 0, 0]], ![![449, -28, 0], ![1205, 0, 0]], ![![512, -30, -1], ![1374, 4, 0]]]
  g := ![![![1, 0, 0], ![-27, 43, 0], ![-32, 0, 43]], ![![-1, 1, 0], ![5, -21, 11], ![10, 0, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-20, -3, 1]] ![![43, 0, 0], ![-16, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-688, 43, 0]], ![![-860, -129, 43], ![430, 43, -43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-16, 1, 0]]], ![![![-20, -3, 1]], ![![10, 1, -1]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [20, 42, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 23, 42], [30, 23, 5], [0, 1]]
 g := ![![[8, 1, 2], [10, 37, 36], [22, 11, 27], [32, 11, 1], []], ![[18, 3, 27, 14], [23, 43, 45, 7], [24, 30, 9, 6], [2, 16, 28, 34], [45, 25]], ![[36, 24, 24, 41], [13, 18, 38, 38], [10, 43], [40, 42, 32, 13], [35, 25]]]
 h' := ![![[28, 23, 42], [35, 22, 7], [30, 26, 41], [18, 34, 11], [0, 0, 1], [0, 1]], ![[30, 23, 5], [27, 30, 4], [44, 19, 14], [23, 34, 36], [25, 26, 23], [28, 23, 42]], ![[0, 1], [27, 42, 36], [33, 2, 39], [42, 26], [12, 21, 23], [30, 23, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 17], []]
 b := ![[], [18, 20, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [20, 42, 36, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15718351, -411673, -311234]
  a := ![1, 11, -24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-334433, -8759, -6622]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![11, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![11, 1, 0]] 
 ![![53, 0, 0], ![11, 1, 0], ![47, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![11, 1, 0], ![0, 6, 11], ![110, 0, 17]]]
  hmulB := by decide  
  f := ![![![298, 27, 0], ![-1431, 0, 0]], ![![44, 4, 0], ![-211, 0, 0]], ![![268, 21, -6], ![-1287, 29, 0]]]
  g := ![![![1, 0, 0], ![-11, 53, 0], ![-47, 0, 53]], ![![0, 1, 0], ![-11, 6, 11], ![-13, 0, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![20, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![20, 1, 0]] 
 ![![53, 0, 0], ![20, 1, 0], ![45, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![20, 1, 0], ![0, 15, 11], ![110, 0, 26]]]
  hmulB := by decide  
  f := ![![![81, 4, 0], ![-212, 0, 0]], ![![20, 1, 0], ![-52, 0, 0]], ![![65, -5, -6], ![-170, 29, 0]]]
  g := ![![![1, 0, 0], ![-20, 53, 0], ![-45, 0, 53]], ![![0, 1, 0], ![-15, 15, 11], ![-20, 0, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![21, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![21, 1, 0]] 
 ![![53, 0, 0], ![21, 1, 0], ![8, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![21, 1, 0], ![0, 16, 11], ![110, 0, 27]]]
  hmulB := by decide  
  f := ![![![883, 42, 0], ![-2226, 0, 0]], ![![357, 17, 0], ![-900, 0, 0]], ![![100, -4, -6], ![-252, 29, 0]]]
  g := ![![![1, 0, 0], ![-21, 53, 0], ![-8, 0, 53]], ![![0, 1, 0], ![-8, 16, 11], ![-2, 0, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![11, 1, 0]] ![![53, 0, 0], ![20, 1, 0]]
  ![![53, 0, 0], ![20, 12, 1]] where
 M := ![![![2809, 0, 0], ![1060, 53, 0]], ![![583, 53, 0], ![220, 26, 11]]]
 hmul := by decide  
 g := ![![![![33, -12, -1], ![53, 0, 0]], ![![0, -11, -1], ![53, 0, 0]]], ![![![-9, -11, -1], ![53, 0, 0]], ![![0, -2, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![20, 12, 1]] ![![53, 0, 0], ![21, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1113, 53, 0]], ![![1060, 636, 53], ![530, 212, 159]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![21, 1, 0]]], ![![![20, 12, 1]], ![![10, 4, 3]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![13, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![13, 1, 0]] 
 ![![59, 0, 0], ![13, 1, 0], ![12, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![13, 1, 0], ![0, 8, 11], ![110, 0, 19]]]
  hmulB := by decide  
  f := ![![![521, 40, 0], ![-2360, 0, 0]], ![![117, 9, 0], ![-530, 0, 0]], ![![102, 2, -8], ![-462, 43, 0]]]
  g := ![![![1, 0, 0], ![-13, 59, 0], ![-12, 0, 59]], ![![0, 1, 0], ![-4, 8, 11], ![-2, 0, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![22, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![22, 1, 0]] 
 ![![59, 0, 0], ![22, 1, 0], ![25, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![22, 1, 0], ![0, 17, 11], ![110, 0, 28]]]
  hmulB := by decide  
  f := ![![![1035, 47, 0], ![-2773, 0, 0]], ![![374, 17, 0], ![-1002, 0, 0]], ![![405, 6, -8], ![-1085, 43, 0]]]
  g := ![![![1, 0, 0], ![-22, 59, 0], ![-25, 0, 59]], ![![0, 1, 0], ![-11, 17, 11], ![-10, 0, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![23, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![23, 1, 0]] 
 ![![59, 0, 0], ![23, 1, 0], ![16, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![23, 1, 0], ![0, 18, 11], ![110, 0, 29]]]
  hmulB := by decide  
  f := ![![![323, 14, 0], ![-826, 0, 0]], ![![115, 5, 0], ![-294, 0, 0]], ![![72, -10, -8], ![-184, 43, 0]]]
  g := ![![![1, 0, 0], ![-23, 59, 0], ![-16, 0, 59]], ![![0, 1, 0], ![-10, 18, 11], ![-6, 0, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![13, 1, 0]] ![![59, 0, 0], ![22, 1, 0]]
  ![![59, 0, 0], ![26, -8, 1]] where
 M := ![![![3481, 0, 0], ![1298, 59, 0]], ![![767, 59, 0], ![286, 30, 11]]]
 hmul := by decide  
 g := ![![![![33, 8, -1], ![59, 0, 0]], ![![-4, 9, -1], ![59, 0, 0]]], ![![![-13, 9, -1], ![59, 0, 0]], ![![0, 2, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![26, -8, 1]] ![![59, 0, 0], ![23, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1357, 59, 0]], ![![1534, -472, 59], ![708, -118, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![23, 1, 0]]], ![![![26, -8, 1]], ![![12, -2, -1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![11, 17, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![11, 17, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![11, 17, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![11, 17, 1], ![110, -74, 193], ![1980, 10, 119]]]
  hmulB := by decide  
  f := ![![![-10, -17, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -17, 61]], ![![0, 0, 1], ![-33, -55, 193], ![11, -33, 119]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [31, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 60], [0, 1]]
 g := ![![[34, 56], [16], [48, 15], [17, 13], [44, 1]], ![[58, 5], [16], [37, 46], [40, 48], [27, 60]]]
 h' := ![![[44, 60], [19, 42], [37, 57], [22, 36], [39, 14], [0, 1]], ![[0, 1], [37, 19], [44, 4], [20, 25], [45, 47], [44, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [45, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [31, 17, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4431, 3748, 791]
  a := ![0, 9, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-70, -159, 791]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-10, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-10, 1, 0]] 
 ![![61, 0, 0], ![51, 1, 0], ![3, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-10, 1, 0], ![0, -15, 11], ![110, 0, -4]]]
  hmulB := by decide  
  f := ![![![591, -59, 0], ![3599, 0, 0]], ![![501, -50, 0], ![3051, 0, 0]], ![![33, 9, -9], ![201, 50, 0]]]
  g := ![![![1, 0, 0], ![-51, 61, 0], ![-3, 0, 61]], ![![-1, 1, 0], ![12, -15, 11], ![2, 0, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![11, 17, 1]] ![![61, 0, 0], ![-10, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-610, 61, 0]], ![![671, 1037, 61], ![0, -244, 183]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-10, 1, 0]]], ![![![11, 17, 1]], ![![0, -4, 3]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-11, 29, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-11, 29, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![56, 29, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-11, 29, 1], ![110, -156, 325], ![3300, 10, 169]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -29, 67]], ![![-1, 0, 1], ![-270, -143, 325], ![-92, -73, 169]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [52, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 66], [0, 1]]
 g := ![![[40, 60], [11, 9], [21], [21], [9], [1]], ![[61, 7], [51, 58], [21], [21], [9], [1]]]
 h' := ![![[64, 66], [31, 23], [51, 3], [2, 50], [25, 17], [15, 64], [0, 1]], ![[0, 1], [29, 44], [42, 64], [53, 17], [41, 50], [24, 3], [64, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [32, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [52, 3, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![400456, 298030, 94921]
  a := ![1, -81, 182]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-73360, -36637, 94921]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![10, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![10, 1, 0]] 
 ![![67, 0, 0], ![10, 1, 0], ![32, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![10, 1, 0], ![0, 5, 11], ![110, 0, 16]]]
  hmulB := by decide  
  f := ![![![431, 43, 0], ![-2881, 0, 0]], ![![50, 5, 0], ![-334, 0, 0]], ![![196, 15, -10], ![-1310, 61, 0]]]
  g := ![![![1, 0, 0], ![-10, 67, 0], ![-32, 0, 67]], ![![0, 1, 0], ![-6, 5, 11], ![-6, 0, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-11, 29, 1]] ![![67, 0, 0], ![10, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![670, 67, 0]], ![![-737, 1943, 67], ![0, 134, 335]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![10, 1, 0]]], ![![![-11, 29, 1]], ![![0, 2, 5]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-34, -24, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-34, -24, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![37, 47, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-34, -24, 1], ![110, 86, -258], ![-2530, 10, -172]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -47, 71]], ![![-1, -1, 1], ![136, 172, -258], ![54, 114, -172]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [67, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 70], [0, 1]]
 g := ![![[63, 50], [40, 32], [49, 1], [10], [30], [1]], ![[25, 21], [10, 39], [17, 70], [10], [30], [1]]]
 h' := ![![[39, 70], [18, 60], [54, 23], [5, 1], [65, 62], [4, 39], [0, 1]], ![[0, 1], [15, 11], [28, 48], [44, 70], [69, 9], [34, 32], [39, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [24, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [67, 32, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3556, 2105, 1211]
  a := ![-1, -7, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-581, -772, 1211]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-26, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-26, 1, 0]] 
 ![![71, 0, 0], ![45, 1, 0], ![30, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-26, 1, 0], ![0, -31, 11], ![110, 0, -20]]]
  hmulB := by decide  
  f := ![![![1535, -59, 0], ![4189, 0, 0]], ![![989, -38, 0], ![2699, 0, 0]], ![![694, -21, -2], ![1894, 13, 0]]]
  g := ![![![1, 0, 0], ![-45, 71, 0], ![-30, 0, 71]], ![![-1, 1, 0], ![15, -31, 11], ![10, 0, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-34, -24, 1]] ![![71, 0, 0], ![-26, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1846, 71, 0]], ![![-2414, -1704, 71], ![994, 710, -284]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-26, 1, 0]]], ![![![-34, -24, 1]], ![![14, 10, -4]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-1, 16, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-1, 16, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![72, 16, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-1, 16, 1], ![110, -81, 182], ![1870, 10, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -16, 73]], ![![-1, 0, 1], ![-178, -41, 182], ![-74, -22, 101]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [11, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 72], [0, 1]]
 g := ![![[44, 41], [46], [23], [39, 55], [72], [1]], ![[56, 32], [46], [23], [64, 18], [72], [1]]]
 h' := ![![[27, 72], [24, 25], [47, 22], [9, 60], [59, 36], [62, 27], [0, 1]], ![[0, 1], [42, 48], [57, 51], [23, 13], [9, 37], [61, 46], [27, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [14, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [11, 46, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10241, 7986, 4140]
  a := ![0, -14, 31]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3943, -798, 4140]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-36, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-36, 1, 0]] 
 ![![73, 0, 0], ![37, 1, 0], ![45, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-36, 1, 0], ![0, -41, 11], ![110, 0, -30]]]
  hmulB := by decide  
  f := ![![![2629, -73, 0], ![5329, 0, 0]], ![![1369, -38, 0], ![2775, 0, 0]], ![![1665, -35, -3], ![3375, 20, 0]]]
  g := ![![![1, 0, 0], ![-37, 73, 0], ![-45, 0, 73]], ![![-1, 1, 0], ![14, -41, 11], ![20, 0, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-1, 16, 1]] ![![73, 0, 0], ![-36, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-2628, 73, 0]], ![![-73, 1168, 73], ![146, -657, 146]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-36, 1, 0]]], ![![![-1, 16, 1]], ![![2, -9, 2]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-13, 2, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-13, 2, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![66, 2, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-13, 2, 1], ![110, -23, 28], ![330, 10, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -2, 79]], ![![-1, 0, 1], ![-22, -1, 28], ![0, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [66, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 78], [0, 1]]
 g := ![![[30, 4], [4, 16], [63, 22], [30, 8], [25], [1]], ![[10, 75], [3, 63], [32, 57], [69, 71], [25], [1]]]
 h' := ![![[74, 78], [52, 2], [29, 75], [74, 38], [20, 61], [13, 74], [0, 1]], ![[0, 1], [42, 77], [49, 4], [42, 41], [31, 18], [38, 5], [74, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [42, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [66, 5, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![59920, 42010, 12552]
  a := ![2, 30, -68]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9728, 214, 12552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-28, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-28, 1, 0]] 
 ![![79, 0, 0], ![51, 1, 0], ![74, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-28, 1, 0], ![0, -33, 11], ![110, 0, -22]]]
  hmulB := by decide  
  f := ![![![1457, -52, 0], ![4108, 0, 0]], ![![981, -35, 0], ![2766, 0, 0]], ![![1374, -34, -5], ![3874, 36, 0]]]
  g := ![![![1, 0, 0], ![-51, 79, 0], ![-74, 0, 79]], ![![-1, 1, 0], ![11, -33, 11], ![22, 0, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-13, 2, 1]] ![![79, 0, 0], ![-28, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-2212, 79, 0]], ![![-1027, 158, 79], ![474, -79, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-28, 1, 0]]], ![![![-13, 2, 1]], ![![6, -1, 0]]]]
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


lemma PB163I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB163I1 : PrimesBelowBoundCertificateInterval O 31 79 163 where
  m := 11
  g := ![1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB163I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
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
    · exact ![103823]
    · exact ![53, 53, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
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
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
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
  β := ![I43N1, I53N0, I53N1, I53N2, I59N0, I59N1, I59N2, I61N1, I67N1, I71N1, I73N1, I79N1]
  Il := ![[], [], [I43N1], [], [I53N0, I53N1, I53N2], [I59N0, I59N1, I59N2], [I61N1], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
