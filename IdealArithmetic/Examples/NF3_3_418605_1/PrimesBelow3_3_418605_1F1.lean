
import IdealArithmetic.Examples.NF3_3_418605_1.RI3_3_418605_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-33, -9, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-33, -9, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![4, 28, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-33, -9, 1], ![81, 12, -26], ![-612, -288, -5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -28, 37]], ![![-1, -1, 1], ![5, 20, -26], ![-16, -4, -5]]]
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
  c := ![337, 324, 297]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23, -216, 297]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-11, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-11, 1, 0]] 
 ![![37, 0, 0], ![26, 1, 0], ![5, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-11, 1, 0], ![-1, -12, 3], ![72, 36, -10]]]
  hmulB := by decide  
  f := ![![![202, 2279, -570], ![37, 7030, 0]], ![![145, 1595, -399], ![38, 4921, 0]], ![![27, 308, -77], ![4, 950, 0]]]
  g := ![![![1, 0, 0], ![-26, 37, 0], ![-5, 0, 37]], ![![-1, 1, 0], ![8, -12, 3], ![-22, 36, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-33, -9, 1]] ![![37, 0, 0], ![-11, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-407, 37, 0]], ![![-1221, -333, 37], ![444, 111, -37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-11, 1, 0]]], ![![![-33, -9, 1]], ![![12, 3, -1]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [20, 5, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 13, 4], [34, 27, 37], [0, 1]]
 g := ![![[16, 2, 40], [19, 40], [21, 21], [37, 1, 1], []], ![[11, 1, 21, 40], [38, 36], [21, 16], [4, 11, 10, 5], [38, 16]], ![[0, 2, 39, 9], [31, 20], [13, 23], [8, 24, 31, 21], [5, 16]]]
 h' := ![![[8, 13, 4], [25, 34, 32], [35, 8, 32], [39, 0, 12], [0, 0, 1], [0, 1]], ![[34, 27, 37], [1, 3, 16], [8, 34, 35], [10, 25, 37], [1, 26, 27], [8, 13, 4]], ![[0, 1], [0, 4, 34], [28, 40, 15], [1, 16, 33], [31, 15, 13], [34, 27, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 40], []]
 b := ![[], [32, 15, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [20, 5, 40, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-626890, 78925, 735581]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15290, 1925, 17941]
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


def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![6, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![6, 1, 0]] 
 ![![43, 0, 0], ![6, 1, 0], ![4, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![6, 1, 0], ![-1, 5, 3], ![72, 36, 7]]]
  hmulB := by decide  
  f := ![![![-755, 3780, 2268], ![0, -32508, 0]], ![![-105, 525, 315], ![1, -4515, 0]], ![![-74, 351, 211], ![27, -3024, 0]]]
  g := ![![![1, 0, 0], ![-6, 43, 0], ![-4, 0, 43]], ![![0, 1, 0], ![-1, 5, 3], ![-4, 36, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 5, -5]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![173, 5, -5]] 
 ![![43, 0, 0], ![31, 1, 0], ![5, 0, 1]] where
  M :=![![![173, 5, -5], ![-365, -12, 10], ![180, 0, -7]]]
  hmulB := by decide  
  f := ![![![-84, -35, 10]], ![![-43, -18, 5]], ![![-60, -25, 7]]]
  g := ![![![1, 5, -5], ![-1, -12, 10], ![5, 0, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![6, 1, 0]] ![![43, 0, 0], ![6, 1, 0]]
  ![![-84, -35, 10]] where
 M := ![![![1849, 0, 0], ![258, 43, 0]], ![![258, 43, 0], ![35, 11, 3]]]
 hmul := by decide  
 g := ![![![![7439, 215, -215]], ![![673, 18, -20]]], ![![![673, 18, -20]], ![![60, 1, -2]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-84, -35, 10]] ![![173, 5, -5]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1068, 29, -30]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![1068, 29, -30]] 
 ![![47, 0, 0], ![0, 47, 0], ![2, 10, 1]] where
  M :=![![![1068, 29, -30], ![-2189, -41, 57], ![1008, -36, -13]]]
  hmulB := by decide  
  f := ![![![-55, -31, -9]], ![![-617, -348, -102]], ![![-188, -106, -31]]]
  g := ![![![24, 7, -30], ![-49, -13, 57], ![22, 2, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [17, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 46], [0, 1]]
 g := ![![[29, 36], [14, 6], [46, 34], [36, 12], [1]], ![[0, 11], [17, 41], [16, 13], [42, 35], [1]]]
 h' := ![![[24, 46], [44, 6], [17, 10], [46, 9], [30, 24], [0, 1]], ![[0, 1], [0, 41], [22, 37], [27, 38], [42, 23], [24, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [13, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [17, 23, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![142345, 152002, 164162]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3957, -31694, 164162]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, -31, -9]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-55, -31, -9]] 
 ![![47, 0, 0], ![16, 1, 0], ![45, 0, 1]] where
  M :=![![![-55, -31, -9], ![-617, -348, -102], ![-2556, -1440, -419]]]
  hmulB := by decide  
  f := ![![![1068, 29, -30]], ![![317, 9, -9]], ![![1044, 27, -29]]]
  g := ![![![18, -31, -9], ![203, -348, -102], ![837, -1440, -419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![1068, 29, -30]] ![![-55, -31, -9]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [8, 42, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 17, 17], [8, 35, 36], [0, 1]]
 g := ![![[0, 28, 11], [47, 16], [47], [52, 11], [1]], ![[52, 12, 27, 52], [22, 1], [41, 36, 49, 43], [18, 47], [13, 11, 36, 37]], ![[17, 33, 6, 36], [23, 25], [24, 13, 12, 10], [33, 4], [9, 6, 51, 16]]]
 h' := ![![[0, 17, 17], [20, 36, 8], [48, 30, 49], [19, 43], [45, 11, 8], [0, 1]], ![[8, 35, 36], [30, 3, 44], [43, 46, 52], [19, 42, 42], [2, 2, 43], [0, 17, 17]], ![[0, 1], [32, 14, 1], [2, 30, 5], [45, 21, 11], [16, 40, 2], [8, 35, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 22], []]
 b := ![[], [16, 28, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [8, 42, 45, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-115434, -342804, -543992]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2178, -6468, -10264]
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


def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1412, 15, -34]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![1412, 15, -34]] 
 ![![59, 0, 0], ![12, 1, 0], ![54, 0, 1]] where
  M :=![![![1412, 15, -34], ![-2463, 173, 11], ![-144, -684, 169]]]
  hmulB := by decide  
  f := ![![![-36761, -20721, -6047]], ![![-14505, -8176, -2386]], ![![-62622, -35298, -10301]]]
  g := ![![![52, 15, -34], ![-87, 173, 11], ![-18, -684, 169]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-6, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-6, 1, 0]] 
 ![![59, 0, 0], ![53, 1, 0], ![25, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-6, 1, 0], ![-1, -7, 3], ![72, 36, -5]]]
  hmulB := by decide  
  f := ![![![-2547, -17836, 7644], ![0, -150332, 0]], ![![-2287, -16016, 6864], ![1, -134992, 0]], ![![-1077, -7558, 3239], ![22, -63700, 0]]]
  g := ![![![1, 0, 0], ![-53, 59, 0], ![-25, 0, 59]], ![![-1, 1, 0], ![5, -7, 3], ![-29, 36, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![1412, 15, -34]] ![![59, 0, 0], ![-6, 1, 0]]
  ![![59, 0, 0], ![-44, -18, 1]] where
 M := ![![![83308, 885, -2006], ![-10935, 83, 215]]]
 hmul := by decide  
 g := ![![![![972, -165, -24], ![-590, 0, 0]], ![![-113, 31, 2], ![97, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-44, -18, 1]] ![![59, 0, 0], ![-6, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-354, 59, 0]], ![![-2596, -1062, 59], ![354, 118, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-6, 1, 0]]], ![![![-44, -18, 1]], ![![6, 2, -1]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-1, -6, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-1, -6, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![60, 55, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-1, -6, 1], ![78, 41, -17], ![-396, -180, 30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-60, -55, 61]], ![![-1, -1, 1], ![18, 16, -17], ![-36, -30, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [29, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 60], [0, 1]]
 g := ![![[17, 48], [1], [9, 19], [41, 16], [56, 1]], ![[21, 13], [1], [36, 42], [22, 45], [51, 60]]]
 h' := ![![[56, 60], [16, 29], [44, 60], [31, 43], [23, 57], [0, 1]], ![[0, 1], [54, 32], [49, 1], [60, 18], [43, 4], [56, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [51, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [29, 5, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![359, 324, 312]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-301, -276, 312]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![17, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![17, 1, 0]] 
 ![![61, 0, 0], ![17, 1, 0], ![31, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![17, 1, 0], ![-1, 16, 3], ![72, 36, 18]]]
  hmulB := by decide  
  f := ![![![-161, 2592, 486], ![0, -9882, 0]], ![![-45, 720, 135], ![1, -2745, 0]], ![![-86, 1317, 247], ![15, -5022, 0]]]
  g := ![![![1, 0, 0], ![-17, 61, 0], ![-31, 0, 61]], ![![0, 1, 0], ![-6, 16, 3], ![-18, 36, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-1, -6, 1]] ![![61, 0, 0], ![17, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1037, 61, 0]], ![![-61, -366, 61], ![61, -61, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![17, 1, 0]]], ![![![-1, -6, 1]], ![![1, -1, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [25, 26, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 50, 40], [12, 16, 27], [0, 1]]
 g := ![![[5, 56, 55], [33, 15, 9], [53, 64], [26, 35], [21, 1], []], ![[48, 46, 38, 6], [17, 66, 25, 15], [60, 55], [61, 62], [12, 55], [13, 59]], ![[58, 60, 4, 7], [12, 13, 59, 46], [48, 40], [52, 59], [18, 21], [26, 59]]]
 h' := ![![[9, 50, 40], [46, 49, 51], [64, 38, 3], [7, 24, 8], [11, 32, 13], [0, 0, 1], [0, 1]], ![[12, 16, 27], [36, 40, 29], [9, 32, 27], [13, 60, 16], [8, 49, 14], [24, 25, 16], [9, 50, 40]], ![[0, 1], [20, 45, 54], [7, 64, 37], [66, 50, 43], [48, 53, 40], [30, 42, 50], [12, 16, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 61], []]
 b := ![[], [47, 43, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [25, 26, 46, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4383944, 2461446, 714488]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![65432, 36738, 10664]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [3, 39, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 61, 66], [7, 9, 5], [0, 1]]
 g := ![![[4, 32, 49], [44, 44, 25], [15, 28, 5], [34, 54], [66, 1], []], ![[8, 40, 50, 44], [28, 51, 31, 62], [26, 31, 27, 65], [60, 15], [22, 10], [46, 25]], ![[53, 44, 61, 29], [51, 51, 12, 5], [48, 38, 37, 8], [43, 18], [6, 29], [36, 25]]]
 h' := ![![[59, 61, 66], [10, 35, 7], [26, 47, 66], [52, 12, 17], [15, 50, 57], [0, 0, 1], [0, 1]], ![[7, 9, 5], [58, 33, 30], [0, 7, 4], [10, 19, 22], [41, 12, 50], [6, 4, 9], [59, 61, 66]], ![[0, 1], [55, 3, 34], [11, 17, 1], [56, 40, 32], [55, 9, 35], [12, 67, 61], [7, 9, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 10], []]
 b := ![[], [50, 22, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [3, 39, 5, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![246512, 76112, -80656]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3472, 1072, -1136]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [55, 59, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 46, 35], [18, 26, 38], [0, 1]]
 g := ![![[23, 70, 32], [60, 36], [44, 27], [38, 8, 18], [67, 1], []], ![[7, 46, 66, 2], [36, 71], [], [16, 36, 39, 3], [45, 19], [31, 57]], ![[38, 21, 46, 18], [15, 32], [7, 27], [64, 11, 22, 72], [56, 72], [28, 57]]]
 h' := ![![[49, 46, 35], [56, 60, 18], [61, 23, 6], [27, 3, 10], [38, 7, 50], [0, 0, 1], [0, 1]], ![[18, 26, 38], [48, 27, 13], [35, 1, 12], [53, 31], [68, 6, 12], [39, 55, 26], [49, 46, 35]], ![[0, 1], [53, 59, 42], [41, 49, 55], [39, 39, 63], [27, 60, 11], [25, 18, 46], [18, 26, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 41], []]
 b := ![[], [32, 66, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [55, 59, 6, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![564144, 424933, 297840]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7728, 5821, 4080]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-28, -25, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-28, -25, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![51, 54, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-28, -25, 1], ![97, 33, -74], ![-1764, -864, -16]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -54, 79]], ![![-1, -1, 1], ![49, 51, -74], ![-12, 0, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [29, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 78], [0, 1]]
 g := ![![[78, 19], [75, 5], [13, 13], [15, 50], [51], [1]], ![[76, 60], [62, 74], [74, 66], [43, 29], [51], [1]]]
 h' := ![![[29, 78], [37, 63], [18, 20], [39, 48], [73, 34], [50, 29], [0, 1]], ![[0, 1], [47, 16], [45, 59], [9, 31], [32, 45], [22, 50], [29, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [19, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [29, 50, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![929, 900, 675]
  a := ![0, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-424, -450, 675]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-5, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-5, 1, 0]] 
 ![![79, 0, 0], ![74, 1, 0], ![16, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-5, 1, 0], ![-1, -6, 3], ![72, 36, -4]]]
  hmulB := by decide  
  f := ![![![-3842, -23058, 11529], ![0, -303597, 0]], ![![-3598, -21594, 10797], ![1, -284321, 0]], ![![-778, -4670, 2335], ![2, -61488, 0]]]
  g := ![![![1, 0, 0], ![-74, 79, 0], ![-16, 0, 79]], ![![-1, 1, 0], ![5, -6, 3], ![-32, 36, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-28, -25, 1]] ![![79, 0, 0], ![-5, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-395, 79, 0]], ![![-2212, -1975, 79], ![237, 158, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-5, 1, 0]]], ![![![-28, -25, 1]], ![![3, 2, -1]]]]
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


lemma PB144I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB144I1 : PrimesBelowBoundCertificateInterval O 31 79 144 where
  m := 11
  g := ![2, 1, 3, 2, 1, 3, 2, 1, 1, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB144I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0]
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
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![357911]
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I43N0, I43N1, I47N1, I59N0, I59N1, I61N1, I79N1]
  Il := ![[I37N1], [], [I43N0, I43N0, I43N1], [I47N1], [], [I59N0, I59N1, I59N1], [I61N1], [], [], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
