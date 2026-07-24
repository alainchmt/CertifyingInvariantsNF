
import IdealArithmetic.Examples.NF3_1_314847_3.RI3_1_314847_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-1, 6, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-1, 6, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![36, 6, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-1, 6, 1], ![123, 2, 25], ![726, 84, 14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -6, 37]], ![![-1, 0, 1], ![-21, -4, 25], ![6, 0, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [14, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 36], [0, 1]]
 g := ![![[16, 25], [30], [26, 10], [4], [1]], ![[3, 12], [30], [6, 27], [4], [1]]]
 h' := ![![[35, 36], [23, 32], [6, 20], [29, 11], [23, 35], [0, 1]], ![[0, 1], [33, 5], [3, 17], [7, 26], [27, 2], [35, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [10, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [14, 2, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1675, 1059, 491]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-523, -51, 491]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![12, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![12, 1, 0]] 
 ![![37, 0, 0], ![12, 1, 0], ![23, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![12, 1, 0], ![2, 11, 4], ![111, 9, 13]]]
  hmulB := by decide  
  f := ![![![1405, 8957, 3264], ![703, -30192, 0]], ![![444, 2897, 1056], ![260, -9768, 0]], ![![863, 5567, 2029], ![469, -18768, 0]]]
  g := ![![![1, 0, 0], ![-12, 37, 0], ![-23, 0, 37]], ![![0, 1, 0], ![-6, 11, 4], ![-8, 9, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-1, 6, 1]] ![![37, 0, 0], ![12, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![444, 37, 0]], ![![-37, 222, 37], ![111, 74, 37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![12, 1, 0]]], ![![![-1, 6, 1]], ![![3, 2, 1]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![9, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![9, 1, 0]] 
 ![![41, 0, 0], ![9, 1, 0], ![3, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![9, 1, 0], ![2, 8, 4], ![111, 9, 10]]]
  hmulB := by decide  
  f := ![![![1786, 7665, 3840], ![615, -39360, 0]], ![![384, 1676, 840], ![165, -8610, 0]], ![![123, 560, 281], ![80, -2880, 0]]]
  g := ![![![1, 0, 0], ![-9, 41, 0], ![-3, 0, 41]], ![![0, 1, 0], ![-2, 8, 4], ![0, 9, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![13, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![13, 1, 0]] 
 ![![41, 0, 0], ![13, 1, 0], ![23, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![13, 1, 0], ![2, 12, 4], ![111, 9, 14]]]
  hmulB := by decide  
  f := ![![![-996, -6829, -2280], ![-451, 23370, 0]], ![![-321, -2157, -720], ![-122, 7380, 0]], ![![-560, -3831, -1279], ![-249, 13110, 0]]]
  g := ![![![1, 0, 0], ![-13, 41, 0], ![-23, 0, 41]], ![![0, 1, 0], ![-6, 12, 4], ![-8, 9, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![19, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![19, 1, 0]] 
 ![![41, 0, 0], ![19, 1, 0], ![38, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![19, 1, 0], ![2, 18, 4], ![111, 9, 20]]]
  hmulB := by decide  
  f := ![![![-707, -8412, -1872], ![-492, 19188, 0]], ![![-337, -3883, -864], ![-204, 8856, 0]], ![![-646, -7796, -1735], ![-476, 17784, 0]]]
  g := ![![![1, 0, 0], ![-19, 41, 0], ![-38, 0, 41]], ![![0, 1, 0], ![-12, 18, 4], ![-20, 9, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![9, 1, 0]] ![![41, 0, 0], ![13, 1, 0]]
  ![![41, 0, 0], ![-1, -5, 1]] where
 M := ![![![1681, 0, 0], ![533, 41, 0]], ![![369, 41, 0], ![119, 21, 4]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![13, 1, 0], ![0, 0, 0]]], ![![![9, 1, 0], ![0, 0, 0]], ![![3, 1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-1, -5, 1]] ![![41, 0, 0], ![19, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![779, 41, 0]], ![![-41, -205, 41], ![82, -82, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![19, 1, 0]]], ![![![-1, -5, 1]], ![![2, -2, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-5, -17, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-5, -17, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![38, 26, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-5, -17, 1], ![77, 21, -67], ![-1827, -123, -13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -26, 43]], ![![-1, -1, 1], ![61, 41, -67], ![-31, 5, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [12, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 42], [0, 1]]
 g := ![![[36, 14], [37, 25], [41], [40, 4], [1]], ![[8, 29], [30, 18], [41], [32, 39], [1]]]
 h' := ![![[41, 42], [29, 10], [30, 38], [36, 16], [31, 41], [0, 1]], ![[0, 1], [9, 33], [40, 5], [4, 27], [35, 2], [41, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [12, 2, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![250817, 129363, 47524]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36165, -25727, 47524]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-19, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-19, 1, 0]] 
 ![![43, 0, 0], ![24, 1, 0], ![13, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-19, 1, 0], ![2, -20, 4], ![111, 9, -18]]]
  hmulB := by decide  
  f := ![![![-210, 3055, -612], ![215, 6579, 0]], ![![-112, 1697, -340], ![130, 3655, 0]], ![![-52, 923, -185], ![91, 1989, 0]]]
  g := ![![![1, 0, 0], ![-24, 43, 0], ![-13, 0, 43]], ![![-1, 1, 0], ![10, -20, 4], ![3, 9, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-5, -17, 1]] ![![43, 0, 0], ![-19, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-817, 43, 0]], ![![-215, -731, 43], ![172, 344, -86]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-19, 1, 0]]], ![![![-5, -17, 1]], ![![4, 8, -2]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [11, 12, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 5, 4], [27, 41, 43], [0, 1]]
 g := ![![[14, 11, 6], [32, 8, 24], [3], [43, 14, 1], []], ![[34, 2, 38, 24], [16, 12, 3, 8], [1, 45, 24, 4], [10, 31, 30, 3], [29, 16]], ![[10, 7, 34, 45], [26, 30, 9, 45], [32, 30, 20, 43], [9, 26, 20, 41], [37, 16]]]
 h' := ![![[34, 5, 4], [24, 6, 37], [14, 20, 20], [44, 35], [0, 0, 1], [0, 1]], ![[27, 41, 43], [36, 37, 37], [44, 39, 7], [12, 34, 46], [38, 4, 41], [34, 5, 4]], ![[0, 1], [21, 4, 20], [38, 35, 20], [2, 25, 1], [40, 43, 5], [27, 41, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 8], []]
 b := ![[], [25, 29, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [11, 12, 33, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2091641, -298638, -22842]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-44503, -6354, -486]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22733, -346, -832]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![22733, -346, -832]] 
 ![![53, 0, 0], ![0, 53, 0], ![13, 38, 1]] where
  M :=![![![22733, -346, -832], ![-93044, 15591, -2216], ![-88326, -28074, 14899]]]
  hmulB := by decide  
  f := ![![![3209025, 537974, 259216]], ![![29848924, 5003995, 2411112]], ![![23608387, 3957806, 1907019]]]
  g := ![![![633, 590, -832], ![-1212, 1883, -2216], ![-5321, -11212, 14899]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [6, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 52], [0, 1]]
 g := ![![[11, 9], [16], [32, 11], [16], [40, 1]], ![[0, 44], [16], [48, 42], [16], [27, 52]]]
 h' := ![![[40, 52], [39, 3], [20, 49], [52, 45], [25, 4], [0, 1]], ![[0, 1], [0, 50], [19, 4], [50, 8], [26, 49], [40, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [35, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [6, 13, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![806, 978, 274]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-52, -178, 274]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3209025, -537974, -259216]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-3209025, -537974, -259216]] 
 ![![53, 0, 0], ![6, 1, 0], ![46, 0, 1]] where
  M :=![![![-3209025, -537974, -259216], ![-29848924, -5003995, -2411112], ![-75268074, -12618246, -6079943]]]
  hmulB := by decide  
  f := ![![![-22733, 346, 832]], ![![-818, -255, 136]], ![![-18064, 830, 441]]]
  g := ![![![225335, -537974, -259216], ![2095966, -5003995, -2411112], ![5285260, -12618246, -6079943]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![22733, -346, -832]] ![![-3209025, -537974, -259216]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [7, 55, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 54, 40], [51, 4, 19], [0, 1]]
 g := ![![[39, 50, 22], [39, 44, 26], [53, 17], [55, 24, 19], [1]], ![[18, 35, 20, 18], [12, 43, 49, 18], [28, 12], [1, 58, 24, 11], [39, 54, 39, 44]], ![[4, 17, 32, 4], [13, 44, 23, 1], [33, 22], [56, 29, 46, 35], [51, 23, 58, 15]]]
 h' := ![![[22, 54, 40], [22, 25, 9], [0, 26, 12], [28, 42, 28], [52, 4, 14], [0, 1]], ![[51, 4, 19], [0, 34, 33], [6, 23, 26], [5, 29, 22], [50, 11, 39], [22, 54, 40]], ![[0, 1], [47, 0, 17], [33, 10, 21], [38, 47, 9], [16, 44, 6], [51, 4, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 4], []]
 b := ![[], [0, 34, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [7, 55, 45, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![313122617, 48400001, 14872897]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5307163, 820339, 252083]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![1, -6, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![1, -6, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![1, 55, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![1, -6, 1], ![99, 16, -23], ![-606, -24, 4]]]
  hmulB := by decide  
  f := ![![![0, -4, 1], ![-38, 1, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -55, 61]], ![![0, -1, 1], ![2, 21, -23], ![-10, -4, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [60, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 60], [0, 1]]
 g := ![![[37, 60], [25], [57, 36], [31, 52], [37, 1]], ![[0, 1], [25], [47, 25], [3, 9], [13, 60]]]
 h' := ![![[37, 60], [41, 50], [57, 56], [31, 6], [37, 28], [0, 1]], ![[0, 1], [0, 11], [55, 5], [9, 55], [36, 33], [37, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [13, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [60, 24, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![344, 71, 39]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, -34, 39]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![23, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![23, 1, 0]] 
 ![![61, 0, 0], ![23, 1, 0], ![57, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![23, 1, 0], ![2, 22, 4], ![111, 9, 24]]]
  hmulB := by decide  
  f := ![![![656, 8969, 1632], ![427, -24888, 0]], ![![237, 3363, 612], ![184, -9333, 0]], ![![616, 8381, 1525], ![391, -23256, 0]]]
  g := ![![![1, 0, 0], ![-23, 61, 0], ![-57, 0, 61]], ![![0, 1, 0], ![-12, 22, 4], ![-24, 9, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![1, -6, 1]] ![![61, 0, 0], ![23, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1403, 61, 0]], ![![61, -366, 61], ![122, -122, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![23, 1, 0]]], ![![![1, -6, 1]], ![![2, -2, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-37, -26, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-37, -26, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![30, 41, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-37, -26, 1], ![59, -2, -103], ![-2826, -204, -54]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -41, 67]], ![![-1, -1, 1], ![47, 63, -103], ![-18, 30, -54]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [5, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 66], [0, 1]]
 g := ![![[56, 40], [], [], [], [10], [1]], ![[45, 27], [], [], [], [10], [1]]]
 h' := ![![[55, 66], [0, 24], [15], [22], [42], [62, 55], [0, 1]], ![[0, 1], [47, 43], [15], [22], [42], [5, 12], [55, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [28, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [5, 12, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1658, 2592, 1096]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-466, -632, 1096]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-31, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-31, 1, 0]] 
 ![![67, 0, 0], ![36, 1, 0], ![54, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-31, 1, 0], ![2, -32, 4], ![111, 9, -30]]]
  hmulB := by decide  
  f := ![![![879, -18998, 2376], ![-670, -39798, 0]], ![![484, -10203, 1276], ![-334, -21373, 0]], ![![714, -15312, 1915], ![-528, -32076, 0]]]
  g := ![![![1, 0, 0], ![-36, 67, 0], ![-54, 0, 67]], ![![-1, 1, 0], ![14, -32, 4], ![21, 9, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-37, -26, 1]] ![![67, 0, 0], ![-31, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-2077, 67, 0]], ![![-2479, -1742, 67], ![1206, 804, -134]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-31, 1, 0]]], ![![![-37, -26, 1]], ![![18, 12, -2]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [41, 40, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 67, 63], [17, 3, 8], [0, 1]]
 g := ![![[48, 49, 36], [32, 55, 57], [49], [25, 45], [37, 1], []], ![[39, 5, 63, 59], [47, 30, 60, 26], [4, 29, 67, 46], [12, 24], [41, 9], [18, 64]], ![[50, 56, 66, 5], [44, 47, 59, 6], [51, 15, 39, 25], [0, 40], [37, 16], [2, 64]]]
 h' := ![![[20, 67, 63], [37, 30, 65], [50, 64, 25], [6, 64], [45, 41, 51], [0, 0, 1], [0, 1]], ![[17, 3, 8], [38, 30, 26], [51, 42, 60], [8, 28, 56], [28, 52, 38], [17, 46, 3], [20, 67, 63]], ![[0, 1], [15, 11, 51], [65, 36, 57], [29, 50, 15], [10, 49, 53], [65, 25, 67], [17, 3, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 6], []]
 b := ![[], [8, 43, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [41, 40, 34, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-454684, -53250, -15975]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6404, -750, -225]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [67, 55, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 60, 55], [56, 12, 18], [0, 1]]
 g := ![![[56, 13, 38], [55, 36], [62, 8], [56, 3, 70], [27, 1], []], ![[11, 39, 20, 41], [48, 65], [20, 24], [38, 14, 56, 69], [58, 71], [18, 32]], ![[7, 70, 56, 54], [43, 24], [64, 3], [26, 37, 49, 54], [61, 23], [55, 32]]]
 h' := ![![[44, 60, 55], [19, 59, 44], [45, 27, 6], [44, 41, 64], [16, 54, 17], [0, 0, 1], [0, 1]], ![[56, 12, 18], [60, 71, 50], [65, 42, 24], [23, 9, 30], [56, 10, 35], [0, 29, 12], [44, 60, 55]], ![[0, 1], [45, 16, 52], [15, 4, 43], [54, 23, 52], [58, 9, 21], [35, 44, 60], [56, 12, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 70], []]
 b := ![[], [8, 41, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [67, 55, 46, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4168665, -505598, -217686]
  a := ![-4, -2, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-57105, -6926, -2982]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-36, 32, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-36, 32, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![43, 32, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-36, 32, 1], ![175, -59, 129], ![3612, 318, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -32, 79]], ![![-1, 0, 1], ![-68, -53, 129], ![43, 2, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [70, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 78], [0, 1]]
 g := ![![[4, 49], [24, 32], [48, 31], [70, 52], [32], [1]], ![[30, 30], [70, 47], [58, 48], [46, 27], [32], [1]]]
 h' := ![![[36, 78], [58, 72], [37, 36], [77, 30], [53, 62], [9, 36], [0, 1]], ![[0, 1], [43, 7], [69, 43], [51, 49], [73, 17], [41, 43], [36, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [47, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [70, 43, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11040, 6408, 3064]
  a := ![14, -1, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1528, -1160, 3064]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![29, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![29, 1, 0]] 
 ![![79, 0, 0], ![29, 1, 0], ![74, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![29, 1, 0], ![2, 28, 4], ![111, 9, 30]]]
  hmulB := by decide  
  f := ![![![-2084, -35265, -5040], ![-1185, 99540, 0]], ![![-779, -12931, -1848], ![-394, 36498, 0]], ![![-1951, -33033, -4721], ![-1113, 93240, 0]]]
  g := ![![![1, 0, 0], ![-29, 79, 0], ![-74, 0, 79]], ![![0, 1, 0], ![-14, 28, 4], ![-30, 9, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-36, 32, 1]] ![![79, 0, 0], ![29, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![2291, 79, 0]], ![![-2844, 2528, 79], ![-869, 869, 158]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![29, 1, 0]]], ![![![-36, 32, 1]], ![![-11, 11, 2]]]]
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


lemma PB159I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB159I1 : PrimesBelowBoundCertificateInterval O 31 79 159 where
  m := 11
  g := ![2, 3, 2, 1, 2, 1, 2, 2, 1, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB159I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
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
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![4489, 67]
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
      exact NI41N1
      exact NI41N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N0, I41N1, I41N2, I43N1, I53N1, I61N1, I67N1, I79N1]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [I43N1], [], [I53N1], [], [I61N1], [I67N1], [], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
