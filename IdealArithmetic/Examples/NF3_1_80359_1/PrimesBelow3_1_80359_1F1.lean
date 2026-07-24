
import IdealArithmetic.Examples.NF3_1_80359_1.RI3_1_80359_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1009, 83, 124]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![1009, 83, 124]] 
 ![![37, 0, 0], ![0, 37, 0], ![15, 32, 1]] where
  M :=![![![1009, 83, 124], ![6737, 554, 829], ![7541, 619, 927]]]
  hmulB := by decide  
  f := ![![![11, -5, 3]], ![![170, 7, -29]], ![![146, 5, -24]]]
  g := ![![![-23, -105, 124], ![-154, -702, 829], ![-172, -785, 927]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [35, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 36], [0, 1]]
 g := ![![[29, 4], [28], [1, 34], [34], [1]], ![[2, 33], [28], [12, 3], [34], [1]]]
 h' := ![![[21, 36], [23, 35], [2, 19], [35, 21], [2, 21], [0, 1]], ![[0, 1], [18, 2], [31, 18], [32, 16], [36, 16], [21, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [19, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [35, 16, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1228, 343, -224]
  a := ![1, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![124, 203, -224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -5, 3]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![11, -5, 3]] 
 ![![37, 0, 0], ![33, 1, 0], ![34, 0, 1]] where
  M :=![![![11, -5, 3], ![170, 7, -29], ![-203, 36, -5]]]
  hmulB := by decide  
  f := ![![![1009, 83, 124]], ![![1082, 89, 133]], ![![1131, 93, 139]]]
  g := ![![![2, -5, 3], ![25, 7, -29], ![-33, 36, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![1009, 83, 124]] ![![11, -5, 3]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [21, 39, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 1, 26], [35, 39, 15], [0, 1]]
 g := ![![[11, 17, 39], [30, 4], [7, 36], [1, 9, 1], []], ![[25, 7, 26, 29], [24, 4], [7, 25], [15, 16, 9, 22], [27, 20]], ![[29, 36, 27, 17], [], [5, 39], [30, 22, 4, 15], [38, 20]]]
 h' := ![![[15, 1, 26], [34, 37, 11], [7, 19, 2], [20, 18, 6], [0, 0, 1], [0, 1]], ![[35, 39, 15], [25, 31, 38], [18, 3, 39], [1, 11, 5], [27, 33, 39], [15, 1, 26]], ![[0, 1], [40, 14, 33], [9, 19], [14, 12, 30], [17, 8, 1], [35, 39, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 39], []]
 b := ![[], [20, 16, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [21, 39, 32, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3486640, -259120, 13530]
  a := ![-3, -5, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![85040, -6320, 330]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, -2, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![6, -2, 1]] 
 ![![43, 0, 0], ![0, 1, 0], ![6, 0, 1]] where
  M :=![![![6, -2, 1], ![57, 5, -12], ![-86, 13, 0]]]
  hmulB := by decide  
  f := ![![![156, 13, 19]], ![![24, 2, 3]], ![![49, 4, 6]]]
  g := ![![![0, -2, 1], ![3, 5, -12], ![-2, 13, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![156, 13, 19]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![156, 13, 19]] 
 ![![43, 0, 0], ![0, 43, 0], ![15, 12, 1]] where
  M :=![![![156, 13, 19], ![1032, 86, 129], ![1171, 94, 144]]]
  hmulB := by decide  
  f := ![![![6, -2, 1]], ![![57, 5, -12]], ![![16, 1, -3]]]
  g := ![![![-3, -5, 19], ![-21, -34, 129], ![-23, -38, 144]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [38, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 42], [0, 1]]
 g := ![![[21, 17], [12, 38], [14], [40, 17], [1]], ![[0, 26], [3, 5], [14], [19, 26], [1]]]
 h' := ![![[19, 42], [17, 24], [37, 9], [28, 10], [5, 19], [0, 1]], ![[0, 1], [0, 19], [36, 34], [3, 33], [22, 24], [19, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [4, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [38, 24, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![105423, 36187, -12468]
  a := ![1, 2, -71]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6801, 4321, -12468]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![6, -2, 1]] ![![156, 13, 19]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 5, 7]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![61, 5, 7]] 
 ![![47, 0, 0], ![0, 47, 0], ![2, 41, 1]] where
  M :=![![![61, 5, 7], ![380, 35, 49], ![443, 34, 57]]]
  hmulB := by decide  
  f := ![![![7, -1, 0]], ![![1, 8, -7]], ![![0, 7, -6]]]
  g := ![![![1, -6, 7], ![6, -42, 49], ![7, -49, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [27, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 46], [0, 1]]
 g := ![![[25, 7], [2, 25], [31, 12], [0, 7], [1]], ![[0, 40], [0, 22], [15, 35], [22, 40], [1]]]
 h' := ![![[30, 46], [40, 30], [9, 42], [0, 23], [20, 30], [0, 1]], ![[0, 1], [0, 17], [0, 5], [32, 24], [27, 17], [30, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [36, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [27, 17, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![871, 3356, -1468]
  a := ![3, 4, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![81, 1352, -1468]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-7, 1, 0]] 
 ![![47, 0, 0], ![40, 1, 0], ![12, 0, 1]] where
  M :=![![![-7, 1, 0], ![-1, -8, 7], ![55, -3, -5]]]
  hmulB := by decide  
  f := ![![![-61, -5, -7]], ![![-60, -5, -7]], ![![-25, -2, -3]]]
  g := ![![![-1, 1, 0], ![5, -8, 7], ![5, -3, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![61, 5, 7]] ![![-7, 1, 0]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [25, 42, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 9, 29], [36, 43, 24], [0, 1]]
 g := ![![[19, 37, 9], [5, 7], [21, 25, 13], [5, 13], [1]], ![[6, 42, 9, 9], [46, 13], [12, 7, 45, 1], [9, 11], [17, 39, 47, 9]], ![[16, 10, 38, 6], [32, 49], [2, 49, 21, 10], [49, 52], [39, 4, 27, 44]]]
 h' := ![![[2, 9, 29], [6, 11, 3], [5, 29, 22], [23, 28, 38], [28, 11, 38], [0, 1]], ![[36, 43, 24], [26, 11, 24], [13, 22, 38], [36, 3, 8], [7, 9, 45], [2, 9, 29]], ![[0, 1], [32, 31, 26], [14, 2, 46], [19, 22, 7], [48, 33, 23], [36, 43, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 5], []]
 b := ![[], [49, 0, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [25, 42, 15, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-94340, 18179, -16695]
  a := ![1, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1780, 343, -315]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17423, 1432, 2142]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![17423, 1432, 2142]] 
 ![![59, 0, 0], ![0, 59, 0], ![1, 14, 1]] where
  M :=![![![17423, 1432, 2142], ![116378, 9565, 14308], ![130168, 10698, 16003]]]
  hmulB := by decide  
  f := ![![![29, -20, 14]], ![![790, 7, -112]], ![![175, 4, -27]]]
  g := ![![![259, -484, 2142], ![1730, -3233, 14308], ![1935, -3616, 16003]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [54, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 58], [0, 1]]
 g := ![![[5, 46], [40, 15], [5], [27, 7], [25, 1]], ![[34, 13], [2, 44], [5], [25, 52], [50, 58]]]
 h' := ![![[25, 58], [23, 20], [19, 30], [17, 51], [7, 40], [0, 1]], ![[0, 1], [51, 39], [2, 29], [53, 8], [4, 19], [25, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [38, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [54, 34, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17073, -164, 2972]
  a := ![-1, 18, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![239, -708, 2972]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, -20, 14]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![29, -20, 14]] 
 ![![59, 0, 0], ![18, 1, 0], ![32, 0, 1]] where
  M :=![![![29, -20, 14], ![790, 7, -112], ![-764, 158, -39]]]
  hmulB := by decide  
  f := ![![![17423, 1432, 2142]], ![![7288, 599, 896]], ![![11656, 958, 1433]]]
  g := ![![![-1, -20, 14], ![72, 7, -112], ![-40, 158, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![17423, 1432, 2142]] ![![29, -20, 14]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [37, 32, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 53, 25], [30, 7, 36], [0, 1]]
 g := ![![[49, 54, 15], [36, 4], [3, 41, 13], [5, 43, 13], [1]], ![[5, 3, 51, 39], [18, 14], [57, 19, 27, 42], [21, 10, 55, 27], [60, 3, 2, 9]], ![[22, 41, 54, 14], [49, 56], [8, 19, 30, 34], [42, 60, 22, 19], [51, 24, 14, 52]]]
 h' := ![![[17, 53, 25], [9, 24, 36], [11, 38, 59], [59, 45, 14], [24, 29, 47], [0, 1]], ![[30, 7, 36], [24, 48, 59], [18, 8, 21], [51, 18, 3], [9, 0, 17], [17, 53, 25]], ![[0, 1], [18, 50, 27], [1, 15, 42], [4, 59, 44], [42, 32, 58], [30, 7, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 50], []]
 b := ![[], [37, 17, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [37, 32, 14, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-315004, 25132, 17080]
  a := ![1, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5164, 412, 280]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![407, -392, 296]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![407, -392, 296]] 
 ![![67, 0, 0], ![0, 67, 0], ![60, 53, 1]] where
  M :=![![![407, -392, 296], ![16672, -89, -2152], ![-14456, 3248, -969]]]
  hmulB := by decide  
  f := ![![![-105611, -8680, -12984]], ![![-705440, -57979, -86728]], ![![-664388, -54605, -81681]]]
  g := ![![![-259, -240, 296], ![2176, 1701, -2152], ![652, 815, -969]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [57, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 66], [0, 1]]
 g := ![![[28, 4], [33, 4], [35], [22], [10], [1]], ![[9, 63], [14, 63], [35], [22], [10], [1]]]
 h' := ![![[12, 66], [62, 2], [13, 2], [20, 13], [66, 25], [10, 12], [0, 1]], ![[0, 1], [19, 65], [37, 65], [42, 54], [31, 42], [20, 55], [12, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [19, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [57, 55, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3114, 1404, 273]
  a := ![-2, -1, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-198, -195, 273]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![105611, 8680, 12984]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![105611, 8680, 12984]] 
 ![![67, 0, 0], ![29, 1, 0], ![37, 0, 1]] where
  M :=![![![105611, 8680, 12984], ![705440, 57979, 86728], ![789016, 64848, 97003]]]
  hmulB := by decide  
  f := ![![![-407, 392, -296]], ![![-425, 171, -96]], ![![-9, 168, -149]]]
  g := ![![![-9351, 8680, 12984], ![-62461, 57979, 86728], ![-69861, 64848, 97003]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![407, -392, 296]] ![![105611, 8680, 12984]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6108, -502, -751]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-6108, -502, -751]] 
 ![![71, 0, 0], ![0, 71, 0], ![52, 59, 1]] where
  M :=![![![-6108, -502, -751], ![-40803, -3353, -5016], ![-45634, -3751, -5610]]]
  hmulB := by decide  
  f := ![![![66, -11, 1]], ![![66, 74, -75]], ![![95, 54, -61]]]
  g := ![![![464, 617, -751], ![3099, 4121, -5016], ![3466, 4609, -5610]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [38, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 70], [0, 1]]
 g := ![![[9, 43], [69, 60], [47, 45], [4], [27], [1]], ![[0, 28], [68, 11], [64, 26], [4], [27], [1]]]
 h' := ![![[13, 70], [5, 16], [60, 42], [54, 20], [63, 2], [33, 13], [0, 1]], ![[0, 1], [0, 55], [38, 29], [30, 51], [18, 69], [60, 58], [13, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [30, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [38, 58, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![638, 175, -340]
  a := ![0, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![258, 285, -340]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-66, 11, -1]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-66, 11, -1]] 
 ![![71, 0, 0], ![11, 1, 0], ![45, 0, 1]] where
  M :=![![![-66, 11, -1], ![-66, -74, 75], ![581, -40, -42]]]
  hmulB := by decide  
  f := ![![![6108, 502, 751]], ![![1521, 125, 187]], ![![4514, 371, 555]]]
  g := ![![![-2, 11, -1], ![-37, -74, 75], ![41, -40, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-6108, -502, -751]] ![![-66, 11, -1]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1455, -26, 218]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-1455, -26, 218]] 
 ![![73, 0, 0], ![0, 73, 0], ![68, 26, 1]] where
  M :=![![![-1455, -26, 218], ![12016, -2083, 254], ![3802, 1604, -1943]]]
  hmulB := by decide  
  f := ![![![49861, 4098, 6130]], ![![333052, 27373, 40946]], ![![170170, 13986, 20921]]]
  g := ![![![-223, -78, 218], ![-72, -119, 254], ![1862, 714, -1943]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [31, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 72], [0, 1]]
 g := ![![[54, 16], [69], [6], [32, 61], [25], [1]], ![[61, 57], [69], [6], [45, 12], [25], [1]]]
 h' := ![![[5, 72], [15, 4], [57, 54], [30, 15], [40, 34], [42, 5], [0, 1]], ![[0, 1], [35, 69], [35, 19], [32, 58], [64, 39], [67, 68], [5, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [70, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [31, 68, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15221, 2032, 752]
  a := ![-2, -12, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-909, -240, 752]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49861, -4098, -6130]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-49861, -4098, -6130]] 
 ![![73, 0, 0], ![35, 1, 0], ![28, 0, 1]] where
  M :=![![![-49861, -4098, -6130], ![-333052, -27373, -40946], ![-372510, -30616, -45797]]]
  hmulB := by decide  
  f := ![![![1455, 26, -218]], ![![533, 41, -108]], ![![506, -12, -57]]]
  g := ![![![3633, -4098, -6130], ![24267, -27373, -40946], ![27142, -30616, -45797]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-1455, -26, 218]] ![![-49861, -4098, -6130]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18895, -1553, -2323]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-18895, -1553, -2323]] 
 ![![79, 0, 0], ![0, 79, 0], ![35, 51, 1]] where
  M :=![![![-18895, -1553, -2323], ![-126212, -10373, -15517], ![-141167, -11602, -17355]]]
  hmulB := by decide  
  f := ![![![61, 11, -18]], ![![-1001, 104, 41]], ![![-617, 70, 20]]]
  g := ![![![790, 1480, -2323], ![5277, 9886, -15517], ![5902, 11057, -17355]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [42, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 78], [0, 1]]
 g := ![![[76, 32], [29, 38], [46, 38], [70, 45], [76], [1]], ![[0, 47], [77, 41], [15, 41], [52, 34], [76], [1]]]
 h' := ![![[47, 78], [46, 36], [43, 65], [62, 14], [73, 19], [37, 47], [0, 1]], ![[0, 1], [0, 43], [17, 14], [9, 65], [18, 60], [34, 32], [47, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [45, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [42, 32, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5207, 2976, -332]
  a := ![-1, -2, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![213, 252, -332]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61, -11, 18]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-61, -11, 18]] 
 ![![79, 0, 0], ![36, 1, 0], ![23, 0, 1]] where
  M :=![![![-61, -11, 18], ![1001, -104, -41], ![-173, 159, -119]]]
  hmulB := by decide  
  f := ![![![18895, 1553, 2323]], ![![10208, 839, 1255]], ![![7288, 599, 896]]]
  g := ![![![-1, -11, 18], ![72, -104, -41], ![-40, 159, -119]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-18895, -1553, -2323]] ![![-61, -11, 18]]
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


lemma PB81I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 80 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 80 (by omega)

def PB81I1 : PrimesBelowBoundCertificateInterval O 31 80 81 where
  m := 11
  g := ![2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB81I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
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
    · exact ![1369, 37]
    · exact ![68921]
    · exact ![43, 1849]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![226981]
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
      exact NI47N1
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
  β := ![I37N1, I43N0, I47N1, I59N1, I67N1, I71N1, I73N1, I79N1]
  Il := ![[I37N1], [], [I43N0], [I47N1], [], [I59N1], [], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
