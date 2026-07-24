
import IdealArithmetic.Examples.NF3_1_455455_1.RI3_1_455455_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [66, 18, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 30, 31], [41, 52, 52], [0, 1]]
 g := ![![[74, 52, 9], [37, 21, 21], [22, 44], [40, 25], [76, 54, 1], []], ![[22, 37, 54, 7], [70, 77, 39, 38], [12, 70], [7, 40], [29, 13, 74, 77], [53, 48]], ![[72, 60, 54, 79], [40, 14, 17, 54], [64, 25], [63, 69], [38, 75, 3, 71], [32, 48]]]
 h' := ![![[13, 30, 31], [48, 17, 80], [49, 34, 41], [67, 67, 58], [47, 48, 78], [0, 0, 1], [0, 1]], ![[41, 52, 52], [47, 78, 39], [39, 35, 32], [1, 70, 30], [52, 56, 66], [74, 61, 52], [13, 30, 31]], ![[0, 1], [46, 71, 47], [40, 14, 10], [60, 29, 78], [20, 62, 22], [67, 22, 30], [41, 52, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 42], []]
 b := ![[], [81, 6, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [66, 18, 29, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3617306, 220448, 47310]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43582, 2656, 570]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![23, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![23, 1, 0]] 
 ![![89, 0, 0], ![23, 1, 0], ![86, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![23, 1, 0], ![0, 24, 6], ![-132, 5, 23]]]
  hmulB := by decide  
  f := ![![![576, 25, 0], ![-2225, 0, 0]], ![![138, 6, 0], ![-533, 0, 0]], ![![554, 20, -1], ![-2140, 15, 0]]]
  g := ![![![1, 0, 0], ![-23, 89, 0], ![-86, 0, 89]], ![![0, 1, 0], ![-12, 24, 6], ![-25, 5, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![32, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![32, 1, 0]] 
 ![![89, 0, 0], ![32, 1, 0], ![2, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![32, 1, 0], ![0, 33, 6], ![-132, 5, 32]]]
  hmulB := by decide  
  f := ![![![1601, 50, 0], ![-4450, 0, 0]], ![![544, 17, 0], ![-1512, 0, 0]], ![![18, -5, -1], ![-50, 15, 0]]]
  g := ![![![1, 0, 0], ![-32, 89, 0], ![-2, 0, 89]], ![![0, 1, 0], ![-12, 33, 6], ![-4, 5, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![33, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![33, 1, 0]] 
 ![![89, 0, 0], ![33, 1, 0], ![80, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![33, 1, 0], ![0, 34, 6], ![-132, 5, 33]]]
  hmulB := by decide  
  f := ![![![496, 15, 0], ![-1335, 0, 0]], ![![132, 4, 0], ![-355, 0, 0]], ![![454, 8, -1], ![-1222, 15, 0]]]
  g := ![![![1, 0, 0], ![-33, 89, 0], ![-80, 0, 89]], ![![0, 1, 0], ![-18, 34, 6], ![-33, 5, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![23, 1, 0]] ![![89, 0, 0], ![32, 1, 0]]
  ![![89, 0, 0], ![4, 39, 1]] where
 M := ![![![7921, 0, 0], ![2848, 89, 0]], ![![2047, 89, 0], ![736, 56, 6]]]
 hmul := by decide  
 g := ![![![![85, -39, -1], ![89, 0, 0]], ![![28, -38, -1], ![89, 0, 0]]], ![![![19, -38, -1], ![89, 0, 0]], ![![8, -2, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![4, 39, 1]] ![![89, 0, 0], ![33, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![2937, 89, 0]], ![![356, 3471, 89], ![0, 1335, 267]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![33, 1, 0]]], ![![![4, 39, 1]], ![![0, 15, 3]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![30, -46, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![30, -46, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![30, 51, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![30, -46, 1], ![-132, -11, -276], ![6094, -252, 35]]]
  hmulB := by decide  
  f := ![![![-29, 46, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -51, 97]], ![![0, -1, 1], ![84, 145, -276], ![52, -21, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [76, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 96], [0, 1]]
 g := ![![[59, 32], [85], [89], [44], [12], [75, 1]], ![[34, 65], [85], [89], [44], [12], [53, 96]]]
 h' := ![![[75, 96], [72, 41], [79, 52], [76, 63], [5, 74], [23, 20], [0, 1]], ![[0, 1], [43, 56], [2, 45], [48, 34], [26, 23], [68, 77], [75, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [57, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [76, 22, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-649, -1307, 486]
  a := ![-1, 1, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-157, -269, 486]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-15, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-15, 1, 0]] 
 ![![97, 0, 0], ![82, 1, 0], ![62, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-15, 1, 0], ![0, -14, 6], ![-132, 5, -15]]]
  hmulB := by decide  
  f := ![![![226, -15, 0], ![1455, 0, 0]], ![![196, -13, 0], ![1262, 0, 0]], ![![146, 2, -5], ![940, 81, 0]]]
  g := ![![![1, 0, 0], ![-82, 97, 0], ![-62, 0, 97]], ![![-1, 1, 0], ![8, -14, 6], ![4, 5, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![30, -46, 1]] ![![97, 0, 0], ![-15, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-1455, 97, 0]], ![![2910, -4462, 97], ![-582, 679, -291]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-15, 1, 0]]], ![![![30, -46, 1]], ![![-6, 7, -3]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-9, -20, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-9, -20, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![92, 81, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-9, -20, 1], ![-132, -24, -120], ![2662, -122, -4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-92, -81, 101]], ![![-1, -1, 1], ![108, 96, -120], ![30, 2, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [1, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 100], [0, 1]]
 g := ![![[41, 1], [47], [54, 84], [24], [56], [60, 1]], ![[0, 100], [47], [44, 17], [24], [56], [19, 100]]]
 h' := ![![[60, 100], [41, 1], [47, 42], [57, 36], [9, 23], [41, 64], [0, 1]], ![[0, 1], [0, 100], [42, 59], [96, 65], [76, 78], [43, 37], [60, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [49, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [1, 41, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1495, -22, 92]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-69, -74, 92]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![19, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![19, 1, 0]] 
 ![![101, 0, 0], ![19, 1, 0], ![4, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![19, 1, 0], ![0, 20, 6], ![-132, 5, 19]]]
  hmulB := by decide  
  f := ![![![191, 10, 0], ![-1010, 0, 0]], ![![19, 1, 0], ![-100, 0, 0]], ![![-12, -4, -1], ![64, 17, 0]]]
  g := ![![![1, 0, 0], ![-19, 101, 0], ![-4, 0, 101]], ![![0, 1, 0], ![-4, 20, 6], ![-3, 5, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-9, -20, 1]] ![![101, 0, 0], ![19, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![1919, 101, 0]], ![![-909, -2020, 101], ![-303, -404, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![19, 1, 0]]], ![![![-9, -20, 1]], ![![-3, -4, -1]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![36, 28, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![36, 28, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![36, 28, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![36, 28, 1], ![-132, 69, 168], ![-3674, 118, 41]]]
  hmulB := by decide  
  f := ![![![-35, -28, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -28, 103]], ![![0, 0, 1], ![-60, -45, 168], ![-50, -10, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [14, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 102], [0, 1]]
 g := ![![[87, 81], [62, 8], [20, 79], [17], [1], [18, 1]], ![[0, 22], [0, 95], [0, 24], [17], [1], [36, 102]]]
 h' := ![![[18, 102], [59, 94], [29, 27], [84, 64], [42, 29], [57, 1], [0, 1]], ![[0, 1], [0, 9], [0, 76], [0, 39], [49, 74], [75, 102], [18, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [90, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [14, 85, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3046, -3628, -262]
  a := ![1, -2, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![62, 36, -262]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![38, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![38, 1, 0]] 
 ![![103, 0, 0], ![38, 1, 0], ![62, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![38, 1, 0], ![0, 39, 6], ![-132, 5, 38]]]
  hmulB := by decide  
  f := ![![![495, 13, 0], ![-1339, 0, 0]], ![![190, 5, 0], ![-514, 0, 0]], ![![326, -24, -5], ![-882, 86, 0]]]
  g := ![![![1, 0, 0], ![-38, 103, 0], ![-62, 0, 103]], ![![0, 1, 0], ![-18, 39, 6], ![-26, 5, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![36, 28, 1]] ![![103, 0, 0], ![38, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![3914, 103, 0]], ![![3708, 2884, 103], ![1236, 1133, 206]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![38, 1, 0]]], ![![![36, 28, 1]], ![![12, 11, 2]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [61, 77, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 67, 36], [49, 39, 71], [0, 1]]
 g := ![![[50, 5, 79], [58, 102, 9], [31, 85], [18, 30, 4], [3, 25], [1]], ![[103, 52, 55, 64], [9, 62, 36, 4], [74, 4], [105, 91, 94, 52], [51, 92], [103, 14, 38, 4]], ![[85, 49, 88, 82], [68, 99, 3, 28], [76, 23], [45, 75, 22, 63], [16, 41], [17, 65, 33, 103]]]
 h' := ![![[53, 67, 36], [100, 97, 87], [70, 78, 3], [79, 43, 70], [7, 41, 105], [46, 30, 102], [0, 1]], ![[49, 39, 71], [47, 7, 37], [29, 58, 36], [100, 30, 105], [77, 22, 7], [70, 66, 29], [53, 67, 36]], ![[0, 1], [1, 3, 90], [83, 78, 68], [15, 34, 39], [97, 44, 102], [89, 11, 83], [49, 39, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 29], []]
 b := ![[], [37, 27, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [61, 77, 5, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3541807, 278842, 31565]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33101, 2606, 295]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-14, -14, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-14, -14, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![95, 95, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-14, -14, 1], ![-132, -23, -84], ![1870, -92, -9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-95, -95, 109]], ![![-1, -1, 1], ![72, 73, -84], ![25, 7, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [88, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 108], [0, 1]]
 g := ![![[79, 83], [31], [9, 4], [75, 21], [88], [24, 1]], ![[0, 26], [31], [105, 105], [34, 88], [88], [48, 108]]]
 h' := ![![[24, 108], [75, 65], [80, 85], [49, 107], [41, 28], [68, 52], [0, 1]], ![[0, 1], [0, 44], [49, 24], [1, 2], [59, 81], [8, 57], [24, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [4, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [88, 85, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-308684, -202082, 62192]
  a := ![1, 20, 101]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-57036, -56058, 62192]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-25, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-25, 1, 0]] 
 ![![109, 0, 0], ![84, 1, 0], ![9, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-25, 1, 0], ![0, -24, 6], ![-132, 5, -25]]]
  hmulB := by decide  
  f := ![![![1501, -60, 0], ![6540, 0, 0]], ![![1176, -47, 0], ![5124, 0, 0]], ![![151, 14, -5], ![658, 91, 0]]]
  g := ![![![1, 0, 0], ![-84, 109, 0], ![-9, 0, 109]], ![![-1, 1, 0], ![18, -24, 6], ![-3, 5, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-14, -14, 1]] ![![109, 0, 0], ![-25, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-2725, 109, 0]], ![![-1526, -1526, 109], ![218, 327, -109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-25, 1, 0]]], ![![![-14, -14, 1]], ![![2, 3, -1]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-38, -47, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-38, -47, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![75, 66, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-38, -47, 1], ![-132, -80, -282], ![6226, -257, -33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-75, -66, 113]], ![![-1, -1, 1], ![186, 164, -282], ![77, 17, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [101, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 112], [0, 1]]
 g := ![![[51, 8], [9], [61], [85], [36, 52], [47, 1]], ![[88, 105], [9], [61], [85], [107, 61], [94, 112]]]
 h' := ![![[47, 112], [52, 11], [82, 3], [64, 20], [93, 57], [112, 74], [0, 1]], ![[0, 1], [4, 102], [110, 110], [100, 93], [60, 56], [87, 39], [47, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [22, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [101, 66, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2934, -1470, 1005]
  a := ![-1, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-693, -600, 1005]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![56, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![56, 1, 0]] 
 ![![113, 0, 0], ![56, 1, 0], ![33, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![56, 1, 0], ![0, 57, 6], ![-132, 5, 56]]]
  hmulB := by decide  
  f := ![![![6105, 109, 0], ![-12317, 0, 0]], ![![2968, 53, 0], ![-5988, 0, 0]], ![![1769, 22, -1], ![-3569, 19, 0]]]
  g := ![![![1, 0, 0], ![-56, 113, 0], ![-33, 0, 113]], ![![0, 1, 0], ![-30, 57, 6], ![-20, 5, 56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-38, -47, 1]] ![![113, 0, 0], ![56, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![6328, 113, 0]], ![![-4294, -5311, 113], ![-2260, -2712, -226]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![56, 1, 0]]], ![![![-38, -47, 1]], ![![-20, -24, -2]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![41, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![41, 1, 0]] 
 ![![127, 0, 0], ![41, 1, 0], ![94, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![41, 1, 0], ![0, 42, 6], ![-132, 5, 41]]]
  hmulB := by decide  
  f := ![![![452, 11, 0], ![-1397, 0, 0]], ![![164, 4, 0], ![-507, 0, 0]], ![![372, -26, -5], ![-1150, 106, 0]]]
  g := ![![![1, 0, 0], ![-41, 127, 0], ![-94, 0, 127]], ![![0, 1, 0], ![-18, 42, 6], ![-33, 5, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-41, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-41, 1, 0]] 
 ![![127, 0, 0], ![86, 1, 0], ![23, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-41, 1, 0], ![0, -40, 6], ![-132, 5, -41]]]
  hmulB := by decide  
  f := ![![![2256, -55, 0], ![6985, 0, 0]], ![![1518, -37, 0], ![4700, 0, 0]], ![![426, 23, -5], ![1319, 106, 0]]]
  g := ![![![1, 0, 0], ![-86, 127, 0], ![-23, 0, 127]], ![![-1, 1, 0], ![26, -40, 6], ![3, 5, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-1, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-1, 1, 0]] 
 ![![127, 0, 0], ![126, 1, 0], ![0, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-1, 1, 0], ![0, 0, 6], ![-132, 5, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -5], ![0, 106, 0]]]
  g := ![![![1, 0, 0], ![-126, 127, 0], ![0, 0, 127]], ![![-1, 1, 0], ![0, 0, 6], ![-6, 5, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![41, 1, 0]] ![![127, 0, 0], ![-41, 1, 0]]
  ![![127, 0, 0], ![-5, -21, 1]] where
 M := ![![![16129, 0, 0], ![-5207, 127, 0]], ![![5207, 127, 0], ![-1681, 1, 6]]]
 hmul := by decide  
 g := ![![![![127, 0, 0], ![0, 0, 0]], ![![-36, 22, -1], ![127, 0, 0]]], ![![![41, 1, 0], ![0, 0, 0]], ![![-13, 1, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-5, -21, 1]] ![![127, 0, 0], ![-1, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-127, 127, 0]], ![![-635, -2667, 127], ![-127, 0, -127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-1, 1, 0]]], ![![![-5, -21, 1]], ![![-1, 0, -1]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![35, 63, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![35, 63, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![35, 63, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![35, 63, 1], ![-132, 103, 378], ![-8294, 293, 40]]]
  hmulB := by decide  
  f := ![![![-34, -63, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -63, 131]], ![![0, 0, 1], ![-102, -181, 378], ![-74, -17, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [18, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 130], [0, 1]]
 g := ![![[113, 46], [126, 81], [9], [48], [108], [45], [1]], ![[83, 85], [39, 50], [9], [48], [108], [45], [1]]]
 h' := ![![[62, 130], [90, 35], [121, 9], [105, 3], [24, 110], [38, 34], [113, 62], [0, 1]], ![[0, 1], [33, 96], [24, 122], [29, 128], [32, 21], [50, 97], [27, 69], [62, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [119, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [18, 69, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7088, -5632, 2672]
  a := ![0, 3, 17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-768, -1328, 2672]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![15, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![15, 1, 0]] 
 ![![131, 0, 0], ![15, 1, 0], ![91, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![15, 1, 0], ![0, 16, 6], ![-132, 5, 15]]]
  hmulB := by decide  
  f := ![![![466, 31, 0], ![-4061, 0, 0]], ![![30, 2, 0], ![-261, 0, 0]], ![![326, 19, -1], ![-2841, 22, 0]]]
  g := ![![![1, 0, 0], ![-15, 131, 0], ![-91, 0, 131]], ![![0, 1, 0], ![-6, 16, 6], ![-12, 5, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![35, 63, 1]] ![![131, 0, 0], ![15, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![1965, 131, 0]], ![![4585, 8253, 131], ![393, 1048, 393]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![15, 1, 0]]], ![![![35, 63, 1]], ![![3, 8, 3]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![57, -10, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![57, -10, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![57, 127, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![57, -10, 1], ![-132, 52, -60], ![1342, -72, 62]]]
  hmulB := by decide  
  f := ![![![-56, 10, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -127, 137]], ![![0, -1, 1], ![24, 56, -60], ![-16, -58, 62]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [136, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 136], [0, 1]]
 g := ![![[122, 136], [76], [76], [44, 128], [126], [88], [1]], ![[0, 1], [76], [76], [42, 9], [126], [88], [1]]]
 h' := ![![[122, 136], [7, 37], [94, 58], [44, 79], [101, 26], [89, 20], [1, 122], [0, 1]], ![[0, 1], [0, 100], [46, 79], [92, 58], [122, 111], [63, 117], [89, 15], [122, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131]]
 b := ![[], [46, 134]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [136, 15, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-48318, -28816, 6882]
  a := ![2, -8, -38]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3216, -6590, 6882]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![60, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![60, 1, 0]] 
 ![![137, 0, 0], ![60, 1, 0], ![75, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![60, 1, 0], ![0, 61, 6], ![-132, 5, 60]]]
  hmulB := by decide  
  f := ![![![841, 14, 0], ![-1918, 0, 0]], ![![300, 5, 0], ![-684, 0, 0]], ![![435, -3, -1], ![-992, 23, 0]]]
  g := ![![![1, 0, 0], ![-60, 137, 0], ![-75, 0, 137]], ![![0, 1, 0], ![-30, 61, 6], ![-36, 5, 60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![57, -10, 1]] ![![137, 0, 0], ![60, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![8220, 137, 0]], ![![7809, -1370, 137], ![3288, -548, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![60, 1, 0]]], ![![![57, -10, 1]], ![![24, -4, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB191I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB191I2 : PrimesBelowBoundCertificateInterval O 79 137 191 where
  m := 11
  g := ![1, 3, 2, 2, 2, 1, 2, 2, 3, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB191I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![89, 89, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![127, 127, 127]
    · exact ![17161, 131]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I89N0, I89N1, I89N2, I97N1, I101N1, I103N1, I109N1, I113N1, I127N0, I127N1, I127N2, I131N1, I137N1]
  Il := ![[], [I89N0, I89N1, I89N2], [I97N1], [I101N1], [I103N1], [], [I109N1], [I113N1], [I127N0, I127N1, I127N2], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
