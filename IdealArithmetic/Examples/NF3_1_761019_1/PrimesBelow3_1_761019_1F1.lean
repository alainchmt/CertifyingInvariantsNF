
import IdealArithmetic.Examples.NF3_1_761019_1.RI3_1_761019_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![7, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![7, 1, 0]] 
 ![![37, 0, 0], ![7, 1, 0], ![27, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![7, 1, 0], ![2, 6, 4], ![-92, -32, 9]]]
  hmulB := by decide  
  f := ![![![-305, -958, -640], ![-74, 5920, 0]], ![![-60, -180, -120], ![1, 1110, 0]], ![![-222, -699, -467], ![-57, 4320, 0]]]
  g := ![![![1, 0, 0], ![-7, 37, 0], ![-27, 0, 37]], ![![0, 1, 0], ![-4, 6, 4], ![-3, -32, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![9, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![9, 1, 0]] 
 ![![37, 0, 0], ![9, 1, 0], ![1, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![9, 1, 0], ![2, 8, 4], ![-92, -32, 11]]]
  hmulB := by decide  
  f := ![![![418, 1843, 924], ![185, -8547, 0]], ![![103, 447, 224], ![38, -2072, 0]], ![![4, 49, 25], ![35, -231, 0]]]
  g := ![![![1, 0, 0], ![-9, 37, 0], ![-1, 0, 37]], ![![0, 1, 0], ![-2, 8, 4], ![5, -32, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-17, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-17, 1, 0]] 
 ![![37, 0, 0], ![20, 1, 0], ![35, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-17, 1, 0], ![2, -18, 4], ![-92, -32, -15]]]
  hmulB := by decide  
  f := ![![![411, -4906, 1092], ![-296, -10101, 0]], ![![227, -2642, 588], ![-147, -5439, 0]], ![![392, -4641, 1033], ![-273, -9555, 0]]]
  g := ![![![1, 0, 0], ![-20, 37, 0], ![-35, 0, 37]], ![![-1, 1, 0], ![6, -18, 4], ![29, -32, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![7, 1, 0]] ![![37, 0, 0], ![9, 1, 0]]
  ![![37, 0, 0], ![7, 13, 1]] where
 M := ![![![1369, 0, 0], ![333, 37, 0]], ![![259, 37, 0], ![65, 15, 4]]]
 hmul := by decide  
 g := ![![![![30, -13, -1], ![37, 0, 0]], ![![2, -12, -1], ![37, 0, 0]]], ![![![0, -12, -1], ![37, 0, 0]], ![![1, -1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![7, 13, 1]] ![![37, 0, 0], ![-17, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-629, 37, 0]], ![![259, 481, 37], ![-185, -259, 37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-17, 1, 0]]], ![![![7, 13, 1]], ![![-5, -7, 1]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![1, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![1, 1, 0]] 
 ![![41, 0, 0], ![1, 1, 0], ![21, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![1, 1, 0], ![2, 0, 4], ![-92, -32, 3]]]
  hmulB := by decide  
  f := ![![![-41, 0, -84], ![0, 861, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-21, 0, -43], ![0, 441, 0]]]
  g := ![![![1, 0, 0], ![-1, 41, 0], ![-21, 0, 41]], ![![0, 1, 0], ![-2, 0, 4], ![-3, -32, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![10, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![10, 1, 0]] 
 ![![41, 0, 0], ![10, 1, 0], ![19, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![10, 1, 0], ![2, 9, 4], ![-92, -32, 12]]]
  hmulB := by decide  
  f := ![![![1967, 9639, 4292], ![738, -43993, 0]], ![![472, 2344, 1044], ![206, -10701, 0]], ![![913, 4467, 1989], ![336, -20387, 0]]]
  g := ![![![1, 0, 0], ![-10, 41, 0], ![-19, 0, 41]], ![![0, 1, 0], ![-4, 9, 4], ![0, -32, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-12, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-12, 1, 0]] 
 ![![41, 0, 0], ![29, 1, 0], ![23, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-12, 1, 0], ![2, -13, 4], ![-92, -32, -10]]]
  hmulB := by decide  
  f := ![![![1025, -7503, 2312], ![-451, -23698, 0]], ![![721, -5296, 1632], ![-327, -16728, 0]], ![![575, -4209, 1297], ![-253, -13294, 0]]]
  g := ![![![1, 0, 0], ![-29, 41, 0], ![-23, 0, 41]], ![![-1, 1, 0], ![7, -13, 4], ![26, -32, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![1, 1, 0]] ![![41, 0, 0], ![10, 1, 0]]
  ![![41, 0, 0], ![3, -18, 1]] where
 M := ![![![1681, 0, 0], ![410, 41, 0]], ![![41, 41, 0], ![12, 10, 4]]]
 hmul := by decide  
 g := ![![![![38, 18, -1], ![41, 0, 0]], ![![7, 19, -1], ![41, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![0, 2, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![3, -18, 1]] ![![41, 0, 0], ![-12, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-492, 41, 0]], ![![123, -738, 41], ![-164, 205, -82]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-12, 1, 0]]], ![![![3, -18, 1]], ![![-4, 5, -2]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [16, 36, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 40, 17], [17, 2, 26], [0, 1]]
 g := ![![[29, 38, 41], [33, 12, 15], [20, 6], [38, 26, 1], []], ![[24, 27, 9, 4], [27, 31, 28, 4], [15, 41], [24, 23, 8, 25], [16, 31]], ![[13, 18, 0, 42], [27, 38, 27, 33], [0, 38], [38, 41, 38, 19], [7, 31]]]
 h' := ![![[9, 40, 17], [31, 27, 16], [17, 38, 12], [37, 22, 36], [0, 0, 1], [0, 1]], ![[17, 2, 26], [11, 6, 18], [22, 5, 25], [41, 33, 16], [40, 35, 2], [9, 40, 17]], ![[0, 1], [11, 10, 9], [35, 0, 6], [32, 31, 34], [5, 8, 40], [17, 2, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 23], []]
 b := ![[], [35, 3, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [16, 36, 17, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1056080, -434644, -202530]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24560, -10108, -4710]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![41, -15, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![41, -15, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![41, 32, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![41, -15, 1], ![-122, 24, -58], ![1295, 441, -20]]]
  hmulB := by decide  
  f := ![![![-40, 15, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -32, 47]], ![![0, -1, 1], ![48, 40, -58], ![45, 23, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [28, 2, 1] where
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
 g := ![![[37, 42], [39, 28], [45, 36], [10, 4], [1]], ![[0, 5], [30, 19], [20, 11], [2, 43], [1]]]
 h' := ![![[45, 46], [36, 18], [9, 34], [2, 41], [19, 45], [0, 1]], ![[0, 1], [0, 29], [35, 13], [14, 6], [23, 2], [45, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [27, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [28, 2, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-240, -600, -1511]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1313, 1016, -1511]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![11, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![11, 1, 0]] 
 ![![47, 0, 0], ![11, 1, 0], ![20, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![11, 1, 0], ![2, 10, 4], ![-92, -32, 13]]]
  hmulB := by decide  
  f := ![![![1718, 9287, 3720], ![611, -43710, 0]], ![![401, 2167, 868], ![142, -10199, 0]], ![![732, 3952, 1583], ![256, -18600, 0]]]
  g := ![![![1, 0, 0], ![-11, 47, 0], ![-20, 0, 47]], ![![0, 1, 0], ![-4, 10, 4], ![0, -32, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![41, -15, 1]] ![![47, 0, 0], ![11, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![517, 47, 0]], ![![1927, -705, 47], ![329, -141, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![11, 1, 0]]], ![![![41, -15, 1]], ![![7, -3, -1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![12, 9, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![12, 9, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![12, 9, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![12, 9, 1], ![-74, -29, 38], ![-913, -327, -1]]]
  hmulB := by decide  
  f := ![![![-11, -9, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -9, 53]], ![![0, 0, 1], ![-10, -7, 38], ![-17, -6, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [47, 50, 1] where
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
 g := ![![[27, 44], [29], [12, 16], [13], [3, 1]], ![[0, 9], [29], [7, 37], [13], [6, 52]]]
 h' := ![![[3, 52], [5, 16], [19, 33], [31, 49], [18, 15], [0, 1]], ![[0, 1], [0, 37], [12, 20], [19, 4], [10, 38], [3, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [29, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [47, 50, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-357092, -165741, -130016]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22700, 18951, -130016]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![15, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![15, 1, 0]] 
 ![![53, 0, 0], ![15, 1, 0], ![1, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![15, 1, 0], ![2, 14, 4], ![-92, -32, 17]]]
  hmulB := by decide  
  f := ![![![2938, 23159, 6624], ![1325, -87768, 0]], ![![831, 6545, 1872], ![372, -24804, 0]], ![![41, 436, 125], ![76, -1656, 0]]]
  g := ![![![1, 0, 0], ![-15, 53, 0], ![-1, 0, 53]], ![![0, 1, 0], ![-4, 14, 4], ![7, -32, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![12, 9, 1]] ![![53, 0, 0], ![15, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![795, 53, 0]], ![![636, 477, 53], ![106, 106, 53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![15, 1, 0]]], ![![![12, 9, 1]], ![![2, 2, 1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![19, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![19, 1, 0]] 
 ![![59, 0, 0], ![19, 1, 0], ![33, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![19, 1, 0], ![2, 18, 4], ![-92, -32, 21]]]
  hmulB := by decide  
  f := ![![![-688, -7051, -1568], ![-295, 23128, 0]], ![![-233, -2267, -504], ![-58, 7434, 0]], ![![-389, -3944, -877], ![-152, 12936, 0]]]
  g := ![![![1, 0, 0], ![-19, 59, 0], ![-33, 0, 59]], ![![0, 1, 0], ![-8, 18, 4], ![-3, -32, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-13, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-13, 1, 0]] 
 ![![59, 0, 0], ![46, 1, 0], ![14, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-13, 1, 0], ![2, -14, 4], ![-92, -32, -11]]]
  hmulB := by decide  
  f := ![![![-392, 3021, -864], ![177, 12744, 0]], ![![-309, 2350, -672], ![119, 9912, 0]], ![![-82, 716, -205], ![92, 3024, 0]]]
  g := ![![![1, 0, 0], ![-46, 59, 0], ![-14, 0, 59]], ![![-1, 1, 0], ![10, -14, 4], ![26, -32, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-7, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-7, 1, 0]] 
 ![![59, 0, 0], ![52, 1, 0], ![16, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-7, 1, 0], ![2, -8, 4], ![-92, -32, -5]]]
  hmulB := by decide  
  f := ![![![2059, -8394, 4200], ![-354, -61950, 0]], ![![1816, -7395, 3700], ![-294, -54575, 0]], ![![563, -2277, 1139], ![-57, -16800, 0]]]
  g := ![![![1, 0, 0], ![-52, 59, 0], ![-16, 0, 59]], ![![-1, 1, 0], ![6, -8, 4], ![28, -32, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![19, 1, 0]] ![![59, 0, 0], ![-13, 1, 0]]
  ![![59, 0, 0], ![42, 16, 1]] where
 M := ![![![3481, 0, 0], ![-767, 59, 0]], ![![1121, 59, 0], ![-245, 5, 4]]]
 hmul := by decide  
 g := ![![![![17, -16, -1], ![59, 0, 0]], ![![-13, 1, 0], ![0, 0, 0]]], ![![![-23, -15, -1], ![59, 0, 0]], ![![-7, -1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![42, 16, 1]] ![![59, 0, 0], ![-7, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-413, 59, 0]], ![![2478, 944, 59], ![-354, -118, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-7, 1, 0]]], ![![![42, 16, 1]], ![![-6, -2, 1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![11, 6, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![11, 6, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![11, 6, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![11, 6, 1], ![-80, -27, 26], ![-637, -231, -8]]]
  hmulB := by decide  
  f := ![![![-10, -6, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -6, 61]], ![![0, 0, 1], ![-6, -3, 26], ![-9, -3, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [43, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 60], [0, 1]]
 g := ![![[50, 13], [48], [9, 45], [37, 1], [46, 1]], ![[38, 48], [48], [5, 16], [22, 60], [31, 60]]]
 h' := ![![[46, 60], [24, 14], [40, 29], [56, 17], [35, 60], [0, 1]], ![[0, 1], [58, 47], [32, 32], [45, 44], [50, 1], [46, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [40, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [43, 15, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1900, -1419, -2646]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![446, 237, -2646]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-26, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-26, 1, 0]] 
 ![![61, 0, 0], ![35, 1, 0], ![8, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-26, 1, 0], ![2, -27, 4], ![-92, -32, -24]]]
  hmulB := by decide  
  f := ![![![-15, 566, -84], ![61, 1281, 0]], ![![3, 323, -48], ![62, 732, 0]], ![![4, 74, -11], ![22, 168, 0]]]
  g := ![![![1, 0, 0], ![-35, 61, 0], ![-8, 0, 61]], ![![-1, 1, 0], ![15, -27, 4], ![20, -32, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![11, 6, 1]] ![![61, 0, 0], ![-26, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1586, 61, 0]], ![![671, 366, 61], ![-366, -183, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-26, 1, 0]]], ![![![11, 6, 1]], ![![-6, -3, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![26, -29, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![26, -29, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![26, 38, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![26, -29, 1], ![-150, 23, -114], ![2583, 889, -63]]]
  hmulB := by decide  
  f := ![![![-25, 29, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -38, 67]], ![![0, -1, 1], ![42, 65, -114], ![63, 49, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [5, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 66], [0, 1]]
 g := ![![[5, 29], [40, 37], [49], [19], [22], [1]], ![[17, 38], [53, 30], [49], [19], [22], [1]]]
 h' := ![![[42, 66], [1, 30], [3, 38], [28, 7], [49, 35], [62, 42], [0, 1]], ![[0, 1], [55, 37], [58, 29], [54, 60], [45, 32], [17, 25], [42, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [21, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [5, 25, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2015, -1002, -1250]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![455, 694, -1250]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-20, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-20, 1, 0]] 
 ![![67, 0, 0], ![47, 1, 0], ![63, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-20, 1, 0], ![2, -21, 4], ![-92, -32, -18]]]
  hmulB := by decide  
  f := ![![![-299, 3777, -720], ![201, 12060, 0]], ![![-211, 2644, -504], ![135, 8442, 0]], ![![-291, 3552, -677], ![156, 11340, 0]]]
  g := ![![![1, 0, 0], ![-47, 67, 0], ![-63, 0, 67]], ![![-1, 1, 0], ![11, -21, 4], ![38, -32, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![26, -29, 1]] ![![67, 0, 0], ![-20, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1340, 67, 0]], ![![1742, -1943, 67], ![-670, 603, -134]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-20, 1, 0]]], ![![![26, -29, 1]], ![![-10, 9, -2]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![16, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![16, 1, 0]] 
 ![![71, 0, 0], ![16, 1, 0], ![47, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![16, 1, 0], ![2, 15, 4], ![-92, -32, 18]]]
  hmulB := by decide  
  f := ![![![-4399, -35380, -9440], ![-1420, 167560, 0]], ![![-998, -7961, -2124], ![-283, 37701, 0]], ![![-2903, -23420, -6249], ![-980, 110920, 0]]]
  g := ![![![1, 0, 0], ![-16, 71, 0], ![-47, 0, 71]], ![![0, 1, 0], ![-6, 15, 4], ![-6, -32, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![20, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![20, 1, 0]] 
 ![![71, 0, 0], ![20, 1, 0], ![12, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![20, 1, 0], ![2, 19, 4], ![-92, -32, 22]]]
  hmulB := by decide  
  f := ![![![-1719, -18230, -3840], ![-710, 68160, 0]], ![![-500, -5128, -1080], ![-141, 19170, 0]], ![![-308, -3082, -649], ![-58, 11520, 0]]]
  g := ![![![1, 0, 0], ![-20, 71, 0], ![-12, 0, 71]], ![![0, 1, 0], ![-6, 19, 4], ![4, -32, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![171, -6, 5]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![171, -6, 5]] 
 ![![71, 0, 0], ![34, 1, 0], ![4, 0, 1]] where
  M :=![![![171, -6, 5], ![-472, 17, -14], ![127, -3, 4]]]
  hmulB := by decide  
  f := ![![![26, 9, -1]], ![![14, 5, 0]], ![![-9, -3, 1]]]
  g := ![![![5, -6, 5], ![-14, 17, -14], ![3, -3, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![16, 1, 0]] ![![71, 0, 0], ![20, 1, 0]]
  ![![26, 9, -1]] where
 M := ![![![5041, 0, 0], ![1420, 71, 0]], ![![1136, 71, 0], ![322, 35, 4]]]
 hmul := by decide  
 g := ![![![![12141, -426, 355]], ![![2948, -103, 86]]], ![![![2264, -79, 66]], ![![550, -19, 16]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![26, 9, -1]] ![![171, -6, 5]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [54, 26, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 34, 55], [44, 38, 18], [0, 1]]
 g := ![![[66, 43, 69], [25, 37], [55, 70], [15, 42, 48], [57, 1], []], ![[61, 43, 2, 65], [11, 27], [27, 69], [70, 47, 47, 70], [53, 57], [16, 32]], ![[33, 69, 24, 27], [9, 19], [14, 4], [7, 38, 62, 23], [24, 61], [53, 32]]]
 h' := ![![[13, 34, 55], [38, 14, 54], [72, 56, 57], [66, 41, 17], [61, 70, 11], [0, 0, 1], [0, 1]], ![[44, 38, 18], [66, 34, 48], [21, 18, 63], [26, 49, 54], [42, 54, 34], [35, 54, 38], [13, 34, 55]], ![[0, 1], [71, 25, 44], [51, 72, 26], [71, 56, 2], [36, 22, 28], [23, 19, 34], [44, 38, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 21], []]
 b := ![[], [47, 18, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [54, 26, 16, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![467133497, 184395664, 60019724]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6399089, 2525968, 822188]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [42, 70, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 23], [10, 55], [0, 1]]
 g := ![![[13, 50, 5], [12, 1, 44], [48, 2, 64], [48, 11, 8], [17, 1], []], ![[55, 74, 38], [42, 50, 50], [38, 35, 44], [43, 64, 45], [24, 23], []], ![[65, 34, 36], [77, 28, 64], [69, 42, 50], [10, 4, 26], [27, 55], []]]
 h' := ![![[7, 23], [49, 9, 20], [38, 54, 26], [38, 58, 71], [76, 32, 61], [0, 0, 1], [0, 1]], ![[10, 55], [65, 11, 73], [31, 55, 8], [52, 22, 34], [50, 75, 37], [49, 6, 55], [7, 23]], ![[0, 1], [6, 59, 65], [18, 49, 45], [55, 78, 53], [18, 51, 60], [21, 73, 23], [10, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19], []]
 b := ![[], [78, 5, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [42, 70, 62, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3081, -1580, -1580]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39, -20, -20]
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



lemma PB247I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB247I1 : PrimesBelowBoundCertificateInterval O 31 79 247 where
  m := 11
  g := ![3, 3, 1, 2, 2, 3, 2, 2, 3, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB247I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0]
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
    · exact ![37, 37, 37]
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![71, 71, 71]
    · exact ![389017]
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
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
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
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N0, I37N1, I37N2, I41N0, I41N1, I41N2, I47N1, I53N1, I59N0, I59N1, I59N2, I61N1, I67N1, I71N0, I71N1, I71N2]
  Il := ![[I37N0, I37N1, I37N2], [I41N0, I41N1, I41N2], [], [I47N1], [I53N1], [I59N0, I59N1, I59N2], [I61N1], [I67N1], [I71N0, I71N1, I71N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
