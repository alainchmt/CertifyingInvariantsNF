
import IdealArithmetic.Examples.NF3_1_551980_3.RI3_1_551980_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-15, -3, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-15, -3, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![22, 34, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-15, -3, 1], ![-155, 6, -2], ![310, -197, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -34, 37]], ![![-1, -1, 1], ![-3, 2, -2], ![6, -9, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [17, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 36], [0, 1]]
 g := ![![[9, 11], [27], [20, 27], [25], [1]], ![[28, 26], [27], [33, 10], [25], [1]]]
 h' := ![![[32, 36], [34, 14], [30, 29], [12, 8], [20, 32], [0, 1]], ![[0, 1], [1, 23], [33, 8], [9, 29], [8, 5], [32, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [7, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [17, 5, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-448, -97, 20]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24, -21, 20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![2, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![2, 1, 0]] 
 ![![37, 0, 0], ![2, 1, 0], ![33, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![2, 1, 0], ![0, 2, 1], ![-155, 21, 3]]]
  hmulB := by decide  
  f := ![![![35, 17, 0], ![-629, 0, 0]], ![![-2, -1, 0], ![38, 0, 0]], ![![31, 15, 0], ![-557, 1, 0]]]
  g := ![![![1, 0, 0], ![-2, 37, 0], ![-33, 0, 37]], ![![0, 1, 0], ![-1, 2, 1], ![-8, 21, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-15, -3, 1]] ![![37, 0, 0], ![2, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![74, 37, 0]], ![![-555, -111, 37], ![-185, 0, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![2, 1, 0]]], ![![![-15, -3, 1]], ![![-5, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-12, -12, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-12, -12, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![29, 29, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-12, -12, 1], ![-155, 9, -11], ![1705, -386, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -29, 41]], ![![-1, -1, 1], ![4, 8, -11], ![43, -8, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [34, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 40], [0, 1]]
 g := ![![[39, 5], [10], [37], [12, 32], [1]], ![[10, 36], [10], [37], [15, 9], [1]]]
 h' := ![![[27, 40], [31, 13], [17, 25], [2, 23], [7, 27], [0, 1]], ![[0, 1], [13, 28], [36, 16], [8, 18], [39, 14], [27, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [23, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [34, 14, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![486, -1482, 226]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-148, -196, 226]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![11, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![11, 1, 0]] 
 ![![41, 0, 0], ![11, 1, 0], ![2, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![11, 1, 0], ![0, 11, 1], ![-155, 21, 12]]]
  hmulB := by decide  
  f := ![![![122, 11, 0], ![-451, 0, 0]], ![![22, 2, 0], ![-81, 0, 0]], ![![-8, -1, 0], ![30, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 41, 0], ![-2, 0, 41]], ![![0, 1, 0], ![-3, 11, 1], ![-10, 21, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-12, -12, 1]] ![![41, 0, 0], ![11, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![451, 41, 0]], ![![-492, -492, 41], ![-287, -123, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![11, 1, 0]]], ![![![-12, -12, 1]], ![![-7, -3, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [35, 19, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 25, 13], [39, 17, 30], [0, 1]]
 g := ![![[25, 33, 36], [1, 41, 41], [9, 13], [41, 24, 1], []], ![[10, 28, 33, 15], [15, 4, 29, 4], [18, 17], [41, 29, 9, 16], [19, 40]], ![[8, 11, 10, 32], [16, 41, 26, 12], [27, 16], [2, 22, 10, 2], [2, 40]]]
 h' := ![![[28, 25, 13], [8, 6, 6], [27, 12, 27], [27, 15, 20], [0, 0, 1], [0, 1]], ![[39, 17, 30], [30, 5, 8], [7, 13, 13], [32, 35, 19], [33, 26, 17], [28, 25, 13]], ![[0, 1], [4, 32, 29], [26, 18, 3], [5, 36, 4], [32, 17, 25], [39, 17, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 32], []]
 b := ![[], [17, 4, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [35, 19, 19, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-239596, 47429, -14104]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5572, 1103, -328]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![175936, 14251, -2194]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![175936, 14251, -2194]] 
 ![![47, 0, 0], ![0, 47, 0], ![1, 32, 1]] where
  M :=![![![175936, 14251, -2194], ![340070, 129862, 12057], ![-1868835, 593267, 141919]]]
  hmulB := by decide  
  f := ![![![239933297, -70725861, 9717905]], ![![-1506275275, 444009302, -61007956]], ![![-819247709, 241492116, -33181603]]]
  g := ![![![3790, 1797, -2194], ![6979, -5446, 12057], ![-42782, -84003, 141919]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [17, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 46], [0, 1]]
 g := ![![[19, 36], [27, 8], [27, 21], [12, 36], [1]], ![[0, 11], [28, 39], [12, 26], [40, 11], [1]]]
 h' := ![![[6, 46], [11, 6], [11, 14], [31, 31], [30, 6], [0, 1]], ![[0, 1], [0, 41], [1, 33], [29, 16], [19, 41], [6, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [38, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [17, 41, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-406, -1289, 64]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, -71, 64]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239933297, -70725861, 9717905]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![239933297, -70725861, 9717905]] 
 ![![47, 0, 0], ![14, 1, 0], ![39, 0, 1]] where
  M :=![![![239933297, -70725861, 9717905], ![-1506275275, 444009302, -61007956], ![9456233180, -2787442351, 383001346]]]
  hmulB := by decide  
  f := ![![![175936, 14251, -2194]], ![![59642, 7008, -397]], ![![106227, 24448, 1199]]]
  g := ![![![18108448, -70725861, 9717905], ![-113682877, 444009302, -61007956], ![713688800, -2787442351, 383001346]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![175936, 14251, -2194]] ![![239933297, -70725861, 9717905]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![4, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![4, 1, 0]] 
 ![![53, 0, 0], ![4, 1, 0], ![37, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![4, 1, 0], ![0, 4, 1], ![-155, 21, 5]]]
  hmulB := by decide  
  f := ![![![137, 34, 0], ![-1802, 0, 0]], ![![4, 1, 0], ![-52, 0, 0]], ![![97, 24, 0], ![-1276, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 53, 0], ![-37, 0, 53]], ![![0, 1, 0], ![-1, 4, 1], ![-8, 21, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59642, 7008, -397]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![59642, 7008, -397]] 
 ![![53, 0, 0], ![14, 1, 0], ![16, 0, 1]] where
  M :=![![![59642, 7008, -397], ![61535, 51305, 6611], ![-1024705, 200366, 57916]]]
  hmulB := by decide  
  f := ![![![1646760754, -485420630, 66697973]], ![![239933297, -70725861, 9717905]], ![![1721701583, -507511164, 69733266]]]
  g := ![![![-606, 7008, -397], ![-14387, 51305, 6611], ![-89745, 200366, 57916]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-19, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-19, 1, 0]] 
 ![![53, 0, 0], ![34, 1, 0], ![10, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-19, 1, 0], ![0, -19, 1], ![-155, 21, -18]]]
  hmulB := by decide  
  f := ![![![419, -22, 0], ![1166, 0, 0]], ![![286, -15, 0], ![796, 0, 0]], ![![102, -5, 0], ![284, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 53, 0], ![-10, 0, 53]], ![![-1, 1, 0], ![12, -19, 1], ![-13, 21, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![4, 1, 0]] ![![59642, 7008, -397]]
  ![![53, 0, 0], ![3, 18, 1]] where
 M := ![![![3161026, 371424, -21041]], ![![300103, 79337, 5023]]]
 hmul := by decide  
 g := ![![![![59351, 5262, -494], ![5141, 0, 0]]], ![![![5618, 1231, 80], ![783, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![3, 18, 1]] ![![53, 0, 0], ![-19, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1007, 53, 0]], ![![159, 954, 53], ![-212, -318, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-19, 1, 0]]], ![![![3, 18, 1]], ![![-4, -6, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-33, 18, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-33, 18, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![26, 18, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-33, 18, 1], ![-155, -12, 19], ![-2945, 244, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -18, 59]], ![![-1, 0, 1], ![-11, -6, 19], ![-53, 2, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [57, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 58], [0, 1]]
 g := ![![[50, 29], [15, 36], [22], [58, 17], [41, 1]], ![[0, 30], [16, 23], [22], [47, 42], [23, 58]]]
 h' := ![![[41, 58], [30, 41], [48, 53], [57, 50], [23, 31], [0, 1]], ![[0, 1], [0, 18], [38, 6], [42, 9], [55, 28], [41, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [33, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [57, 18, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-408, -110, 7]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, -4, 7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-19, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-19, 1, 0]] 
 ![![59, 0, 0], ![40, 1, 0], ![52, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-19, 1, 0], ![0, -19, 1], ![-155, 21, -18]]]
  hmulB := by decide  
  f := ![![![723, -38, 0], ![2242, 0, 0]], ![![476, -25, 0], ![1476, 0, 0]], ![![634, -33, 0], ![1966, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 59, 0], ![-52, 0, 59]], ![![-1, 1, 0], ![12, -19, 1], ![-1, 21, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-33, 18, 1]] ![![59, 0, 0], ![-19, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1121, 59, 0]], ![![-1947, 1062, 59], ![472, -354, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-19, 1, 0]]], ![![![-33, 18, 1]], ![![8, -6, 0]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [51, 25, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 34, 38], [24, 26, 23], [0, 1]]
 g := ![![[59, 27, 47], [22, 49], [32, 44, 46], [5, 47, 16], [1]], ![[49, 42, 40, 50], [20, 36], [11, 59], [33, 9, 27, 53], [47, 26, 44, 33]], ![[39, 40, 32, 38], [29, 47], [3, 28, 43, 21], [46, 11, 54, 18], [20, 38, 16, 28]]]
 h' := ![![[41, 34, 38], [18, 29, 13], [15, 5, 7], [50, 18, 30], [10, 36, 4], [0, 1]], ![[24, 26, 23], [26, 44, 37], [58, 10, 6], [24, 57], [34, 52, 8], [41, 34, 38]], ![[0, 1], [50, 49, 11], [59, 46, 48], [43, 47, 31], [55, 34, 49], [24, 26, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 27], []]
 b := ![[], [36, 0, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [51, 25, 57, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1770586, 53192, 49898]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29026, 872, 818]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11236572, -14572248, -2036095]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-11236572, -14572248, -2036095]] 
 ![![67, 0, 0], ![17, 1, 0], ![46, 0, 1]] where
  M :=![![![-11236572, -14572248, -2036095], ![315594725, -53994567, -16608343], ![2574293165, -33180478, -70602910]]]
  hmulB := by decide  
  f := ![![![-3261100794862016, 961284508688270, -132082825169199]], ![![-521878740469081, 153835769019185, -21137408124736]], ![![-4157267127001623, 1225450159026668, -168379826831034]]]
  g := ![![![4927642, -14572248, -2036095], ![29813226, -53994567, -16608343], ![95314853, -33180478, -70602910]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1558, 72, 51]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-1558, 72, 51]] 
 ![![67, 0, 0], ![50, 1, 0], ![46, 0, 1]] where
  M :=![![![-1558, 72, 51], ![-7905, -487, 123], ![-19065, -5322, -364]]]
  hmulB := by decide  
  f := ![![![-831874, 245214, -33693]], ![![-542855, 160019, -21987]], ![![-1060477, 312600, -42952]]]
  g := ![![![-112, 72, 51], ![161, -487, 123], ![3937, -5322, -364]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![308277, 17835, -4981]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![308277, 17835, -4981]] 
 ![![67, 0, 0], ![66, 1, 0], ![66, 0, 1]] where
  M :=![![![308277, 17835, -4981], ![772055, 203676, 12854], ![-1992370, 1041989, 216530]]]
  hmulB := by decide  
  f := ![![![-30708237674, 9051959759, -1243761246]], ![![-27372547662, 8068688362, -1108657369]], ![![-48313648597, 14241559791, -1956824889]]]
  g := ![![![-8061, 17835, -4981], ![-201775, 203676, 12854], ![-1269472, 1041989, 216530]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-11236572, -14572248, -2036095]] ![![-1558, 72, 51]]
  ![![171518350791, 17123749182, -1624313096]] where
 M := ![![![171518350791, 17123749182, -1624313096]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![171518350791, 17123749182, -1624313096]] ![![308277, 17835, -4981]]
  ![![67, 0, 0]] where
 M := ![![![69331871484583637, 4854210146162573, -985936747981423]]]
 hmul := by decide  
 g := ![![![![1034804052008711, 72450897703919, -14715473850469]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [62, 23, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 66, 45], [37, 4, 26], [0, 1]]
 g := ![![[70, 2, 5], [40, 56, 3], [69, 43, 20], [35, 45], [28, 1], []], ![[42, 33, 8, 57], [14, 54, 6, 12], [6, 68, 67, 27], [20, 60], [23, 16], [18, 37]], ![[35, 38, 60, 42], [22, 70, 57, 22], [60, 23, 12, 68], [18, 10], [9, 25], [37, 37]]]
 h' := ![![[62, 66, 45], [5, 50, 54], [53, 36, 43], [61, 54, 34], [39, 4, 51], [0, 0, 1], [0, 1]], ![[37, 4, 26], [39, 23, 52], [25, 65, 17], [27, 36, 10], [42, 13, 29], [30, 9, 4], [62, 66, 45]], ![[0, 1], [43, 69, 36], [21, 41, 11], [3, 52, 27], [14, 54, 62], [69, 62, 66], [37, 4, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 6], []]
 b := ![[], [35, 58, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [62, 23, 43, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16969, 2130, -710]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-239, 30, -10]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-33, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-33, 1, 0]] 
 ![![73, 0, 0], ![40, 1, 0], ![6, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-33, 1, 0], ![0, -33, 1], ![-155, 21, -32]]]
  hmulB := by decide  
  f := ![![![1486, -45, 0], ![3285, 0, 0]], ![![826, -25, 0], ![1826, 0, 0]], ![![180, -5, 0], ![398, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 73, 0], ![-6, 0, 73]], ![![-1, 1, 0], ![18, -33, 1], ![-11, 21, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-27, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-27, 1, 0]] 
 ![![73, 0, 0], ![46, 1, 0], ![1, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-27, 1, 0], ![0, -27, 1], ![-155, 21, -26]]]
  hmulB := by decide  
  f := ![![![1567, -58, 0], ![4234, 0, 0]], ![![1000, -37, 0], ![2702, 0, 0]], ![![37, -1, 0], ![100, 1, 0]]]
  g := ![![![1, 0, 0], ![-46, 73, 0], ![-1, 0, 73]], ![![-1, 1, 0], ![17, -27, 1], ![-15, 21, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-113, -18, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-113, -18, 0]] 
 ![![73, 0, 0], ![59, 1, 0], ![23, 0, 1]] where
  M :=![![![-113, -18, 0], ![0, -113, -18], ![2790, -378, -131]]]
  hmulB := by decide  
  f := ![![![7999, -2358, 324]], ![![5777, -1703, 234]], ![![6839, -2016, 277]]]
  g := ![![![13, -18, 0], ![97, -113, -18], ![385, -378, -131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-33, 1, 0]] ![![73, 0, 0], ![-27, 1, 0]]
  ![![7999, -2358, 324]] where
 M := ![![![5329, 0, 0], ![-1971, 73, 0]], ![![-2409, 73, 0], ![891, -60, 1]]]
 hmul := by decide  
 g := ![![![![-8249, -1314, 0]], ![![3051, 373, -18]]], ![![![3729, 481, -18]], ![![-1341, -132, 13]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![7999, -2358, 324]] ![![-113, -18, 0]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [13, 0, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 77, 30], [8, 1, 49], [0, 1]]
 g := ![![[0, 10, 55], [42, 47, 21], [67, 21, 40], [32, 57, 67], [8, 1], []], ![[48, 65, 73, 59], [63, 16, 59, 56], [51, 71, 3, 74], [9, 8, 32, 77], [71, 1], [49, 31]], ![[46, 25, 39, 26], [17, 60, 9, 67], [17, 66, 38, 65], [31, 78, 39, 52], [0, 4], [30, 31]]]
 h' := ![![[0, 77, 30], [7, 25, 23], [77, 10, 69], [58, 42, 35], [54, 66, 64], [0, 0, 1], [0, 1]], ![[8, 1, 49], [50, 3, 62], [48, 60, 53], [41, 31, 31], [50, 67, 69], [74, 71, 1], [0, 77, 30]], ![[0, 1], [56, 51, 73], [20, 9, 36], [44, 6, 13], [21, 25, 25], [69, 8, 77], [8, 1, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73], []]
 b := ![[], [0, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [13, 0, 71, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8848, -75287, 6952]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![112, -953, 88]
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



lemma PB211I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB211I1 : PrimesBelowBoundCertificateInterval O 31 79 211 where
  m := 11
  g := ![2, 2, 1, 2, 3, 2, 1, 3, 1, 3, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB211I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![67, 67, 67]
    · exact ![357911]
    · exact ![73, 73, 73]
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
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
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
      exact NI67N2
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
  β := ![I37N1, I41N1, I47N1, I53N0, I53N1, I53N2, I59N1, I67N0, I67N1, I67N2, I73N0, I73N1, I73N2]
  Il := ![[I37N1], [I41N1], [], [I47N1], [I53N0, I53N1, I53N2], [I59N1], [], [I67N0, I67N1, I67N2], [], [I73N0, I73N1, I73N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
