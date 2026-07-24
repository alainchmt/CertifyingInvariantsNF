
import IdealArithmetic.Examples.NF3_1_888300_3.RI3_1_888300_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![1, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![1, 1, 0]] 
 ![![83, 0, 0], ![1, 1, 0], ![82, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![1, 1, 0], ![0, 1, 1], ![730, 150, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![83, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![82, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 83, 0], ![-82, 0, 83]], ![![0, 1, 0], ![-1, 1, 1], ![6, 150, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-553, -32, 5]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-553, -32, 5]] 
 ![![83, 0, 0], ![39, 1, 0], ![56, 0, 1]] where
  M :=![![![-553, -32, 5], ![3650, 197, -32], ![-23360, -1150, 197]]]
  hmulB := by decide  
  f := ![![![2009, 554, 39]], ![![1287, 355, 25]], ![![6228, 1718, 121]]]
  g := ![![![5, -32, 5], ![-27, 197, -32], ![126, -1150, 197]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-40, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-40, 1, 0]] 
 ![![83, 0, 0], ![43, 1, 0], ![60, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-40, 1, 0], ![0, -40, 1], ![730, 150, -40]]]
  hmulB := by decide  
  f := ![![![1721, -43, 0], ![3569, 0, 0]], ![![881, -22, 0], ![1827, 0, 0]], ![![1220, -30, 0], ![2530, 1, 0]]]
  g := ![![![1, 0, 0], ![-43, 83, 0], ![-60, 0, 83]], ![![-1, 1, 0], ![20, -40, 1], ![-40, 150, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![1, 1, 0]] ![![-553, -32, 5]]
  ![![83, 0, 0], ![-127, -43, 1]] where
 M := ![![![-45899, -2656, 415]], ![![3097, 165, -27]]]
 hmul := by decide  
 g := ![![![![-172, 97, 2], ![249, 0, 0]]], ![![![123, 31, -1], ![56, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-127, -43, 1]] ![![83, 0, 0], ![-40, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-3320, 83, 0]], ![![-10541, -3569, 83], ![5810, 1743, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-40, 1, 0]]], ![![![-127, -43, 1]], ![![70, 21, -1]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [45, 46, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 76, 45], [35, 12, 44], [0, 1]]
 g := ![![[47, 72, 44], [43, 22], [64, 45], [7, 59, 78], [64, 56, 1], []], ![[63, 21, 72, 84], [66, 50], [49, 5], [77, 79, 70, 40], [60, 5, 83, 72], [1, 67]], ![[19, 37, 79, 53], [0, 50], [44, 80], [26, 16, 79, 40], [1, 27, 43, 49], [2, 67]]]
 h' := ![![[21, 76, 45], [7, 47, 20], [47, 69, 72], [41, 5, 57], [57, 54, 73], [0, 0, 1], [0, 1]], ![[35, 12, 44], [14, 51, 41], [15, 80, 53], [23, 15, 19], [17, 50, 13], [40, 42, 12], [21, 76, 45]], ![[0, 1], [55, 80, 28], [77, 29, 53], [30, 69, 13], [74, 74, 3], [67, 47, 76], [35, 12, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 7], []]
 b := ![[], [25, 85, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [45, 46, 33, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-813905, -254896, -20203]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9145, -2864, -227]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-134, -4, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-134, -4, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![60, 93, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-134, -4, 1], ![730, 16, -4], ![-2920, 130, 16]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-60, -93, 97]], ![![-2, -1, 1], ![10, 4, -4], ![-40, -14, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [93, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 96], [0, 1]]
 g := ![![[65, 24], [48], [27], [12], [25], [66, 1]], ![[0, 73], [48], [27], [12], [25], [35, 96]]]
 h' := ![![[66, 96], [47, 86], [7, 57], [44, 30], [53, 77], [70, 92], [0, 1]], ![[0, 1], [0, 11], [83, 40], [84, 67], [91, 20], [31, 5], [66, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [51, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [93, 31, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8697, 4712, 1441]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-981, -1333, 1441]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![4, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![4, 1, 0]] 
 ![![97, 0, 0], ![4, 1, 0], ![81, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![4, 1, 0], ![0, 4, 1], ![730, 150, 4]]]
  hmulB := by decide  
  f := ![![![269, 67, 0], ![-6499, 0, 0]], ![![4, 1, 0], ![-96, 0, 0]], ![![229, 57, 0], ![-5533, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 97, 0], ![-81, 0, 97]], ![![0, 1, 0], ![-1, 4, 1], ![-2, 150, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-134, -4, 1]] ![![97, 0, 0], ![4, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![388, 97, 0]], ![![-12998, -388, 97], ![194, 0, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![4, 1, 0]]], ![![![-134, -4, 1]], ![![2, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![30, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![30, 1, 0]] 
 ![![101, 0, 0], ![30, 1, 0], ![9, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![30, 1, 0], ![0, 30, 1], ![730, 150, 30]]]
  hmulB := by decide  
  f := ![![![1201, 40, 0], ![-4040, 0, 0]], ![![330, 11, 0], ![-1110, 0, 0]], ![![69, 2, 0], ![-232, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 101, 0], ![-9, 0, 101]], ![![0, 1, 0], ![-9, 30, 1], ![-40, 150, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-24, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-24, 1, 0]] 
 ![![101, 0, 0], ![77, 1, 0], ![30, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-24, 1, 0], ![0, -24, 1], ![730, 150, -24]]]
  hmulB := by decide  
  f := ![![![2113, -88, 0], ![8888, 0, 0]], ![![1609, -67, 0], ![6768, 0, 0]], ![![630, -26, 0], ![2650, 1, 0]]]
  g := ![![![1, 0, 0], ![-77, 101, 0], ![-30, 0, 101]], ![![-1, 1, 0], ![18, -24, 1], ![-100, 150, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-6, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-6, 1, 0]] 
 ![![101, 0, 0], ![95, 1, 0], ![65, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-6, 1, 0], ![0, -6, 1], ![730, 150, -6]]]
  hmulB := by decide  
  f := ![![![115, -19, 0], ![1919, 0, 0]], ![![109, -18, 0], ![1819, 0, 0]], ![![79, -13, 0], ![1319, 1, 0]]]
  g := ![![![1, 0, 0], ![-95, 101, 0], ![-65, 0, 101]], ![![-1, 1, 0], ![5, -6, 1], ![-130, 150, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![30, 1, 0]] ![![101, 0, 0], ![-24, 1, 0]]
  ![![101, 0, 0], ![-114, 6, 1]] where
 M := ![![![10201, 0, 0], ![-2424, 101, 0]], ![![3030, 101, 0], ![-720, 6, 1]]]
 hmul := by decide  
 g := ![![![![101, 0, 0], ![0, 0, 0]], ![![90, -5, -1], ![101, 0, 0]]], ![![![30, 1, 0], ![0, 0, 0]], ![![108, -6, -1], ![102, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-114, 6, 1]] ![![101, 0, 0], ![-6, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-606, 101, 0]], ![![-11514, 606, 101], ![1414, 0, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-6, 1, 0]]], ![![![-114, 6, 1]], ![![14, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-116, 31, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-116, 31, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![90, 31, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-116, 31, 1], ![730, 34, 31], ![22630, 5380, 34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-90, -31, 103]], ![![-2, 0, 1], ![-20, -9, 31], ![190, 42, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [94, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 102], [0, 1]]
 g := ![![[10, 76], [26, 66], [42, 50], [92], [63], [90, 1]], ![[52, 27], [95, 37], [10, 53], [92], [63], [77, 102]]]
 h' := ![![[90, 102], [28, 73], [69, 90], [17, 87], [42, 68], [89, 75], [0, 1]], ![[0, 1], [6, 30], [32, 13], [19, 16], [85, 35], [41, 28], [90, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [13, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [94, 13, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1898, 315, 266]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-214, -77, 266]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-31, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-31, 1, 0]] 
 ![![103, 0, 0], ![72, 1, 0], ![69, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-31, 1, 0], ![0, -31, 1], ![730, 150, -31]]]
  hmulB := by decide  
  f := ![![![497, -16, 0], ![1648, 0, 0]], ![![342, -11, 0], ![1134, 0, 0]], ![![351, -11, 0], ![1164, 1, 0]]]
  g := ![![![1, 0, 0], ![-72, 103, 0], ![-69, 0, 103]], ![![-1, 1, 0], ![21, -31, 1], ![-77, 150, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-116, 31, 1]] ![![103, 0, 0], ![-31, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-3193, 103, 0]], ![![-11948, 3193, 103], ![4326, -927, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-31, 1, 0]]], ![![![-116, 31, 1]], ![![42, -9, 0]]]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [46, 78, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 2, 101], [34, 104, 6], [0, 1]]
 g := ![![[97, 98, 34], [11, 93, 9], [77, 33], [86, 8, 37], [70, 76], [1]], ![[78, 54, 48, 64], [20, 15, 7, 34], [44, 52], [100, 30, 54, 69], [71, 33], [41, 96, 84, 105]], ![[38, 42, 89, 95], [74, 39, 72, 77], [68, 81], [88, 19, 104, 96], [82, 11], [89, 101, 22, 2]]]
 h' := ![![[32, 2, 101], [29, 4, 26], [105, 77, 3], [3, 72, 56], [73, 39, 95], [61, 29, 66], [0, 1]], ![[34, 104, 6], [69, 74, 5], [32, 104, 64], [68, 31, 42], [20, 64, 16], [66, 28, 56], [32, 2, 101]], ![[0, 1], [99, 29, 76], [98, 33, 40], [103, 4, 9], [22, 4, 103], [7, 50, 92], [34, 104, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 45], []]
 b := ![[], [22, 86, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [46, 78, 41, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11623624, -5062277, -530185]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-108632, -47311, -4955]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-69, -9, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-69, -9, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![40, 100, 1]] where
  M :=![![![-69, -9, 1], ![730, 81, -9], ![-6570, -620, 81]]]
  hmulB := by decide  
  f := ![![![9, 1, 0]], ![![0, 9, 1]], ![![10, 10, 1]]]
  g := ![![![-1, -1, 1], ![10, 9, -9], ![-90, -80, 81]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [38, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 108], [0, 1]]
 g := ![![[6, 66], [48], [101, 100], [40, 74], [29], [99, 1]], ![[0, 43], [48], [82, 9], [63, 35], [29], [89, 108]]]
 h' := ![![[99, 108], [13, 34], [86, 22], [6, 10], [72, 69], [53, 62], [0, 1]], ![[0, 1], [0, 75], [84, 87], [15, 99], [36, 40], [87, 47], [99, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [105, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [38, 10, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1498, 1020, 141]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-38, -120, 141]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![9, 1, 0]] 
 ![![109, 0, 0], ![9, 1, 0], ![28, 0, 1]] where
  M :=![![![9, 1, 0], ![0, 9, 1], ![730, 150, 9]]]
  hmulB := by decide  
  f := ![![![-69, -9, 1]], ![![1, 0, 0]], ![![-78, -8, 1]]]
  g := ![![![0, 1, 0], ![-1, 9, 1], ![-8, 150, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-69, -9, 1]] ![![9, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [99, 2, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 78, 94], [48, 34, 19], [0, 1]]
 g := ![![[107, 89, 61], [81, 99], [59, 44], [92, 14], [18, 44, 53], [1]], ![[62, 14, 97, 17], [102, 52], [96, 44], [58, 91], [61, 57, 96, 80], [91, 33, 82, 34]], ![[107, 42, 20, 78], [99, 4], [], [49, 16], [46, 110, 31, 17], [20, 102, 78, 79]]]
 h' := ![![[29, 78, 94], [17, 43, 20], [76, 103, 72], [43, 23, 48], [26, 98, 63], [14, 111, 77], [0, 1]], ![[48, 34, 19], [15, 52, 89], [13, 34, 39], [108, 39, 65], [58, 79, 54], [12, 2, 57], [29, 78, 94]], ![[0, 1], [16, 18, 4], [72, 89, 2], [33, 51], [5, 49, 109], [19, 0, 92], [48, 34, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 31], []]
 b := ![[], [88, 12, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [99, 2, 36, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12863468, 3573173, 246566]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![113836, 31621, 2182]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-79, -43, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-79, -43, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![48, 84, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-79, -43, 1], ![730, 71, -43], ![-31390, -5720, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-48, -84, 127]], ![![-1, -1, 1], ![22, 29, -43], ![-274, -92, 71]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [74, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 126], [0, 1]]
 g := ![![[46, 115], [95, 47], [30, 117], [9, 25], [28, 71], [25, 1]], ![[0, 12], [0, 80], [34, 10], [126, 102], [25, 56], [50, 126]]]
 h' := ![![[25, 126], [82, 78], [66, 38], [96, 102], [87, 122], [55, 43], [0, 1]], ![[0, 1], [0, 49], [0, 89], [106, 25], [89, 5], [114, 84], [25, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88]]
 b := ![[], [85, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [74, 102, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4407, 130, 59]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-57, -38, 59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![43, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![43, 1, 0]] 
 ![![127, 0, 0], ![43, 1, 0], ![56, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![43, 1, 0], ![0, 43, 1], ![730, 150, 43]]]
  hmulB := by decide  
  f := ![![![1850, 43, 0], ![-5461, 0, 0]], ![![602, 14, 0], ![-1777, 0, 0]], ![![832, 19, 0], ![-2456, 1, 0]]]
  g := ![![![1, 0, 0], ![-43, 127, 0], ![-56, 0, 127]], ![![0, 1, 0], ![-15, 43, 1], ![-64, 150, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-79, -43, 1]] ![![127, 0, 0], ![43, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![5461, 127, 0]], ![![-10033, -5461, 127], ![-2667, -1778, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![43, 1, 0]]], ![![![-79, -43, 1]], ![![-21, -14, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [56, 58, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 67, 13], [31, 63, 118], [0, 1]]
 g := ![![[53, 83, 13], [78, 26, 15], [70, 100], [125, 123], [82, 20], [76, 1], []], ![[5, 26, 126, 7], [65, 5, 15, 38], [68, 49], [41, 48], [46, 94], [41, 39], [45, 38]], ![[61, 105, 68, 82], [14, 67, 120, 106], [48, 9], [48, 46], [120, 53], [94, 35], [71, 38]]]
 h' := ![![[45, 67, 13], [86, 66, 12], [85, 16, 88], [72, 49, 121], [28, 120, 56], [67, 121, 85], [0, 0, 1], [0, 1]], ![[31, 63, 118], [129, 14, 42], [82, 12, 119], [22, 57, 7], [109, 89, 110], [117, 27, 116], [29, 113, 63], [45, 67, 13]], ![[0, 1], [12, 51, 77], [12, 103, 55], [39, 25, 3], [99, 53, 96], [111, 114, 61], [129, 18, 67], [31, 63, 118]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84, 112], []]
 b := ![[], [108, 51, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [56, 58, 55, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5738586, 2220188, 222831]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![43806, 16948, 1701]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![11, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![11, 1, 0]] 
 ![![137, 0, 0], ![11, 1, 0], ![16, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![11, 1, 0], ![0, 11, 1], ![730, 150, 11]]]
  hmulB := by decide  
  f := ![![![254, 23, 0], ![-3151, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![12, 1, 0], ![-148, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 137, 0], ![-16, 0, 137]], ![![0, 1, 0], ![-1, 11, 1], ![-8, 150, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![58, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![58, 1, 0]] 
 ![![137, 0, 0], ![58, 1, 0], ![61, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![58, 1, 0], ![0, 58, 1], ![730, 150, 58]]]
  hmulB := by decide  
  f := ![![![1277, 22, 0], ![-3014, 0, 0]], ![![522, 9, 0], ![-1232, 0, 0]], ![![489, 8, 0], ![-1154, 1, 0]]]
  g := ![![![1, 0, 0], ![-58, 137, 0], ![-61, 0, 137]], ![![0, 1, 0], ![-25, 58, 1], ![-84, 150, 58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![68, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![68, 1, 0]] 
 ![![137, 0, 0], ![68, 1, 0], ![34, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![68, 1, 0], ![0, 68, 1], ![730, 150, 68]]]
  hmulB := by decide  
  f := ![![![1973, 29, 0], ![-3973, 0, 0]], ![![884, 13, 0], ![-1780, 0, 0]], ![![442, 6, 0], ![-890, 1, 0]]]
  g := ![![![1, 0, 0], ![-68, 137, 0], ![-34, 0, 137]], ![![0, 1, 0], ![-34, 68, 1], ![-86, 150, 68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![11, 1, 0]] ![![137, 0, 0], ![58, 1, 0]]
  ![![137, 0, 0], ![-47, -68, 1]] where
 M := ![![![18769, 0, 0], ![7946, 137, 0]], ![![1507, 137, 0], ![638, 69, 1]]]
 hmul := by decide  
 g := ![![![![137, 0, 0], ![0, 0, 0]], ![![58, 1, 0], ![0, 0, 0]]], ![![![11, 1, 0], ![0, 0, 0]], ![![5, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-47, -68, 1]] ![![137, 0, 0], ![68, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![9316, 137, 0]], ![![-6439, -9316, 137], ![-2466, -4521, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![68, 1, 0]]], ![![![-47, -68, 1]], ![![-18, -33, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB267I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB267I2 : PrimesBelowBoundCertificateInterval O 79 137 267 where
  m := 11
  g := ![3, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB267I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
    · exact ![I137N0, I137N1, I137N2]
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
    · exact ![83, 83, 83]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![2248091]
    · exact ![137, 137, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I83N0, I83N1, I83N2, I97N1, I101N0, I101N1, I101N2, I103N1, I109N1, I127N1, I137N0, I137N1, I137N2]
  Il := ![[I83N0, I83N1, I83N2], [], [I97N1], [I101N0, I101N1, I101N2], [I103N1], [], [I109N1], [], [I127N1], [], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
