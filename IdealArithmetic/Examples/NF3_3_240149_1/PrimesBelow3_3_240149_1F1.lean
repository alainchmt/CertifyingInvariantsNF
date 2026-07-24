
import IdealArithmetic.Examples.NF3_3_240149_1.RI3_3_240149_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-20, -14, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-20, -14, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![17, 23, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-20, -14, 1], ![-63, 4, -69], ![681, -341, -10]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -23, 37]], ![![-1, -1, 1], ![30, 43, -69], ![23, -3, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [33, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 36], [0, 1]]
 g := ![![[2, 9], [16], [4, 34], [27], [1]], ![[0, 28], [16], [17, 3], [27], [1]]]
 h' := ![![[8, 36], [24, 34], [16, 4], [13, 21], [4, 8], [0, 1]], ![[0, 1], [0, 3], [11, 33], [33, 16], [31, 29], [8, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [26, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [33, 29, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-609, 88, 480]
  a := ![-1, -1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-237, -296, 480]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-5, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-5, 1, 0]] 
 ![![37, 0, 0], ![32, 1, 0], ![10, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-5, 1, 0], ![1, -5, 5], ![-49, 24, -4]]]
  hmulB := by decide  
  f := ![![![-231, 1208, -1210], ![74, 8954, 0]], ![![-198, 1043, -1045], ![75, 7733, 0]], ![![-60, 326, -327], ![38, 2420, 0]]]
  g := ![![![1, 0, 0], ![-32, 37, 0], ![-10, 0, 37]], ![![-1, 1, 0], ![3, -5, 5], ![-21, 24, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-20, -14, 1]] ![![37, 0, 0], ![-5, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-185, 37, 0]], ![![-740, -518, 37], ![37, 74, -74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-5, 1, 0]]], ![![![-20, -14, 1]], ![![1, 2, -2]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![0, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![0, 1, 0]] 
 ![![41, 0, 0], ![0, 1, 0], ![33, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![0, 1, 0], ![1, 0, 5], ![-49, 24, 1]]]
  hmulB := by decide  
  f := ![![![0, 0, -5], ![0, 41, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -4], ![0, 33, 0]]]
  g := ![![![1, 0, 0], ![0, 41, 0], ![-33, 0, 41]], ![![0, 1, 0], ![-4, 0, 5], ![-2, 24, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-24, 8, 1]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-24, 8, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![17, 8, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-24, 8, 1], ![-41, 0, 41], ![-397, 187, 8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -8, 41]], ![![-1, 0, 1], ![-18, -8, 41], ![-13, 3, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [40, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 40], [0, 1]]
 g := ![![[32, 40], [40], [1], [32, 40], [1]], ![[0, 1], [40], [1], [0, 1], [1]]]
 h' := ![![[32, 40], [40, 9], [0, 9], [32, 40], [1, 32], [0, 1]], ![[0, 1], [0, 32], [1, 32], [0, 1], [0, 9], [32, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [38, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [40, 9, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1617, -1687, 3023]
  a := ![2, -2, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1214, -631, 3023]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![0, 1, 0]] ![![41, 0, 0], ![-24, 8, 1]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-984, 328, 41]], ![![0, 41, 0], ![-41, 0, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-24, 8, 1]]], ![![![0, 1, 0]], ![![-1, 0, 1]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-19, 3, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-19, 3, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![24, 3, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-19, 3, 1], ![-46, 5, 16], ![-152, 67, 8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -3, 43]], ![![-1, 0, 1], ![-10, -1, 16], ![-8, 1, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [20, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 42], [0, 1]]
 g := ![![[24, 14], [16, 24], [14], [23, 6], [1]], ![[12, 29], [20, 19], [14], [24, 37], [1]]]
 h' := ![![[36, 42], [24, 33], [18, 29], [13, 33], [23, 36], [0, 1]], ![[0, 1], [8, 10], [30, 14], [40, 10], [29, 7], [36, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [3, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [20, 7, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-311236, -353256, 1666490]
  a := ![-65, 1, -261]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-937372, -124482, 1666490]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-16, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-16, 1, 0]] 
 ![![43, 0, 0], ![27, 1, 0], ![35, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-16, 1, 0], ![1, -16, 5], ![-49, 24, -15]]]
  hmulB := by decide  
  f := ![![![-39, 1150, -360], ![86, 3096, 0]], ![![-28, 719, -225], ![44, 1935, 0]], ![![-31, 936, -293], ![72, 2520, 0]]]
  g := ![![![1, 0, 0], ![-27, 43, 0], ![-35, 0, 43]], ![![-1, 1, 0], ![6, -16, 5], ![-4, 24, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-19, 3, 1]] ![![43, 0, 0], ![-16, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-688, 43, 0]], ![![-817, 129, 43], ![258, -43, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-16, 1, 0]]], ![![![-19, 3, 1]], ![![6, -1, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-34, -23, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-34, -23, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![13, 24, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-34, -23, 1], ![-72, -10, -114], ![1122, -557, -33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -24, 47]], ![![-1, -1, 1], ![30, 58, -114], ![33, 5, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [25, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 46], [0, 1]]
 g := ![![[3, 32], [37, 3], [11, 1], [34, 32], [1]], ![[0, 15], [0, 44], [30, 46], [31, 15], [1]]]
 h' := ![![[19, 46], [15, 19], [7, 12], [43, 1], [22, 19], [0, 1]], ![[0, 1], [0, 28], [0, 35], [15, 46], [7, 28], [19, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [17, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [25, 28, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![447, -1109, 2623]
  a := ![-2, 1, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-716, -1363, 2623]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![20, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![20, 1, 0]] 
 ![![47, 0, 0], ![20, 1, 0], ![33, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![20, 1, 0], ![1, 20, 5], ![-49, 24, 21]]]
  hmulB := by decide  
  f := ![![![-1119, -31976, -8000], ![-1128, 75200, 0]], ![![-480, -13590, -3400], ![-469, 31960, 0]], ![![-781, -22451, -5617], ![-803, 52800, 0]]]
  g := ![![![1, 0, 0], ![-20, 47, 0], ![-33, 0, 47]], ![![0, 1, 0], ![-12, 20, 5], ![-26, 24, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-34, -23, 1]] ![![47, 0, 0], ![20, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![940, 47, 0]], ![![-1598, -1081, 47], ![-752, -470, -94]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![20, 1, 0]]], ![![![-34, -23, 1]], ![![-16, -10, -2]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [8, 47, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 51, 49], [32, 1, 4], [0, 1]]
 g := ![![[8, 43, 7], [7, 1], [39, 30, 52], [26, 17], [1]], ![[44, 27, 7, 10], [46, 46], [40, 42, 9, 36], [34, 9], [14, 17, 44, 42]], ![[44, 43, 6, 42], [20, 52], [6, 29, 27, 37], [0, 6], [23, 0, 14, 11]]]
 h' := ![![[42, 51, 49], [33, 12, 31], [6, 7, 52], [15, 30, 30], [45, 6, 21], [0, 1]], ![[32, 1, 4], [43, 39, 36], [27, 25, 24], [31, 42, 16], [41, 17, 50], [42, 51, 49]], ![[0, 1], [8, 2, 39], [50, 21, 30], [15, 34, 7], [42, 30, 35], [32, 1, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 31], []]
 b := ![[], [21, 1, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [8, 47, 32, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![55756, -9222, -54590]
  a := ![-1, -1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1052, -174, -1030]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [30, 25, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 53, 55], [3, 5, 4], [0, 1]]
 g := ![![[36, 19, 3], [29, 45, 15], [18, 25], [52, 30, 48], [1]], ![[18, 31, 45, 6], [34, 9, 17, 42], [24, 27], [24, 21, 37, 37], [37, 18, 23, 54]], ![[8, 12, 0, 46], [9, 40, 8, 15], [40, 28], [8, 31, 38, 46], [53, 27, 47, 5]]]
 h' := ![![[41, 53, 55], [15, 19, 11], [18, 25, 29], [33, 57, 5], [29, 34, 44], [0, 1]], ![[3, 5, 4], [45, 45, 38], [7, 1, 45], [45, 36, 33], [20, 19, 25], [41, 53, 55]], ![[0, 1], [32, 54, 10], [9, 33, 44], [41, 25, 21], [30, 6, 49], [3, 5, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 51], []]
 b := ![[], [11, 14, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [30, 25, 15, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7638376, 3213317, 1708463]
  a := ![2, 19, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-129464, 54463, 28957]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-1, 8, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-1, 8, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![60, 8, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-1, 8, 1], ![-41, 23, 41], ![-397, 187, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-60, -8, 61]], ![![-1, 0, 1], ![-41, -5, 41], ![-37, -1, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [42, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 60], [0, 1]]
 g := ![![[40, 16], [42], [11, 16], [20, 39], [28, 1]], ![[0, 45], [42], [32, 45], [14, 22], [56, 60]]]
 h' := ![![[28, 60], [10, 4], [26, 15], [14, 4], [44, 10], [0, 1]], ![[0, 1], [0, 57], [19, 46], [4, 57], [19, 51], [28, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [25, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [42, 33, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2230, -1614, 1674]
  a := ![-2, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1610, -246, 1674]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![20, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![20, 1, 0]] 
 ![![61, 0, 0], ![20, 1, 0], ![30, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![20, 1, 0], ![1, 20, 5], ![-49, 24, 21]]]
  hmulB := by decide  
  f := ![![![-2493, -61451, -15370], ![-1769, 187514, 0]], ![![-827, -20131, -5035], ![-548, 61427, 0]], ![![-1230, -30222, -7559], ![-858, 92220, 0]]]
  g := ![![![1, 0, 0], ![-20, 61, 0], ![-30, 0, 61]], ![![0, 1, 0], ![-9, 20, 5], ![-19, 24, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-1, 8, 1]] ![![61, 0, 0], ![20, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1220, 61, 0]], ![![-61, 488, 61], ![-61, 183, 61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![20, 1, 0]]], ![![![-1, 8, 1]], ![![-1, 3, 1]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [10, 5, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 18, 36], [2, 48, 31], [0, 1]]
 g := ![![[52, 24, 55], [61, 16, 47], [64, 62], [36, 55], [18, 1], []], ![[6, 9, 24, 9], [9, 2, 60, 37], [57, 1], [43, 35], [0, 26], [35, 23]], ![[11, 28, 10, 61], [30, 54, 29, 51], [65, 35], [13, 37], [11, 56], [40, 23]]]
 h' := ![![[16, 18, 36], [60, 26, 51], [25, 45, 28], [14, 28, 53], [21, 34, 51], [0, 0, 1], [0, 1]], ![[2, 48, 31], [37, 10, 34], [56, 37, 16], [36, 53, 1], [59, 20, 54], [40, 37, 48], [16, 18, 36]], ![[0, 1], [16, 31, 49], [15, 52, 23], [53, 53, 13], [60, 13, 29], [6, 30, 18], [2, 48, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 53], []]
 b := ![[], [61, 10, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [10, 5, 49, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-311416, -70216, 704840]
  a := ![2, 1, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4648, -1048, 10520]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [42, 48, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 53, 1], [58, 17, 70], [0, 1]]
 g := ![![[6, 14, 40], [63, 18, 10], [54], [52, 60], [19, 1], []], ![[63, 65, 68, 15], [26, 23, 57, 24], [14, 48, 27, 54], [20, 18], [23, 5], [54, 1]], ![[31, 37, 21, 41], [59, 62, 49, 11], [4, 38, 24, 17], [21, 36], [3, 40], [56, 1]]]
 h' := ![![[32, 53, 1], [52, 70, 18], [4, 22, 9], [22, 14], [54, 40, 29], [0, 0, 1], [0, 1]], ![[58, 17, 70], [64, 30, 21], [20, 36, 33], [44, 32, 14], [48, 33, 36], [34, 48, 17], [32, 53, 1]], ![[0, 1], [34, 42, 32], [22, 13, 29], [53, 25, 57], [56, 69, 6], [18, 23, 53], [58, 17, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 67], []]
 b := ![[], [64, 20, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [42, 48, 52, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1073023, 1846000, -4164860]
  a := ![-5, 0, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15113, 26000, -58660]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-9, -15, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-9, -15, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![64, 58, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-9, -15, 1], ![-64, 15, -74], ![730, -365, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -58, 73]], ![![-1, -1, 1], ![64, 59, -74], ![10, -5, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [50, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 72], [0, 1]]
 g := ![![[18, 19], [37], [19], [47, 55], [65], [1]], ![[0, 54], [37], [19], [41, 18], [65], [1]]]
 h' := ![![[49, 72], [40, 26], [49, 57], [59, 26], [53, 37], [23, 49], [0, 1]], ![[0, 1], [0, 47], [68, 16], [19, 47], [41, 36], [15, 24], [49, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [31, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [50, 24, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16282, -10580, 8492]
  a := ![4, -10, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7222, -6892, 8492]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![1, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![1, 1, 0]] 
 ![![73, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![1, 1, 0], ![1, 1, 5], ![-49, 24, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![73, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-1, -1, -3], ![29, 44, 0]]]
  g := ![![![1, 0, 0], ![-1, 73, 0], ![0, 0, 73]], ![![0, 1, 0], ![0, 1, 5], ![-1, 24, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-9, -15, 1]] ![![73, 0, 0], ![1, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![73, 73, 0]], ![![-657, -1095, 73], ![-73, 0, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![1, 1, 0]]], ![![![-9, -15, 1]], ![![-1, 0, -1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-12, -24, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-12, -24, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![67, 55, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-12, -24, 1], ![-73, 12, -119], ![1171, -581, -12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-67, -55, 79]], ![![-1, -1, 1], ![100, 83, -119], ![25, 1, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [36, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 78], [0, 1]]
 g := ![![[48, 11], [8, 9], [45, 32], [71, 32], [21], [1]], ![[0, 68], [19, 70], [49, 47], [75, 47], [21], [1]]]
 h' := ![![[10, 78], [28, 13], [39, 3], [51, 43], [66, 43], [43, 10], [0, 1]], ![[0, 1], [0, 66], [69, 76], [7, 36], [22, 36], [64, 69], [10, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [68, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [36, 69, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9460, -19078, 83396]
  a := ![14, -1, 57]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-70848, -58302, 83396]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-39, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-39, 1, 0]] 
 ![![79, 0, 0], ![40, 1, 0], ![12, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-39, 1, 0], ![1, -39, 5], ![-49, 24, -38]]]
  hmulB := by decide  
  f := ![![![-14, 2105, -270], ![79, 4266, 0]], ![![13, 1052, -135], ![80, 2133, 0]], ![![27, 319, -41], ![71, 648, 0]]]
  g := ![![![1, 0, 0], ![-40, 79, 0], ![-12, 0, 79]], ![![-1, 1, 0], ![19, -39, 5], ![-7, 24, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-12, -24, 1]] ![![79, 0, 0], ![-39, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-3081, 79, 0]], ![![-948, -1896, 79], ![395, 948, -158]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-39, 1, 0]]], ![![![-12, -24, 1]], ![![5, 12, -2]]]]
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


lemma PB109I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB109I1 : PrimesBelowBoundCertificateInterval O 31 79 109 where
  m := 11
  g := ![2, 2, 2, 2, 1, 1, 2, 1, 1, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB109I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0]
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
    · exact ![41, 1681]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![357911]
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
      exact NI41N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N0, I43N1, I47N1, I61N1, I73N1, I79N1]
  Il := ![[I37N1], [I41N0], [I43N1], [I47N1], [], [], [I61N1], [], [], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
