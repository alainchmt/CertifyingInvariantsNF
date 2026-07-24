
import IdealArithmetic.Examples.NF3_1_933107_3.RI3_1_933107_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![55, -5, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![55, -5, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![55, 78, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![55, -5, 1], ![13, 29, -39], ![-117, 154, 19]]]
  hmulB := by decide  
  f := ![![![-54, 5, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -78, 83]], ![![0, -1, 1], ![26, 37, -39], ![-14, -16, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [22, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 82], [0, 1]]
 g := ![![[26, 69], [42, 3], [26], [27], [1, 81], [1]], ![[66, 14], [69, 80], [26], [27], [66, 2], [1]]]
 h' := ![![[9, 82], [72, 61], [74, 13], [56, 21], [61, 39], [61, 9], [0, 1]], ![[0, 1], [40, 22], [25, 70], [79, 62], [80, 44], [59, 74], [9, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [58, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [22, 74, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1029, 667, -5296]
  a := ![-3, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3497, 4985, -5296]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![39, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![39, 1, 0]] 
 ![![83, 0, 0], ![39, 1, 0], ![64, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![39, 1, 0], ![2, 38, 8], ![23, -31, 40]]]
  hmulB := by decide  
  f := ![![![1435, 37606, 7920], ![1162, -82170, 0]], ![![657, 17663, 3720], ![582, -38595, 0]], ![![1091, 28997, 6107], ![929, -63360, 0]]]
  g := ![![![1, 0, 0], ![-39, 83, 0], ![-64, 0, 83]], ![![0, 1, 0], ![-24, 38, 8], ![-16, -31, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![55, -5, 1]] ![![83, 0, 0], ![39, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![3237, 83, 0]], ![![4565, -415, 83], ![2158, -166, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![39, 1, 0]]], ![![![55, -5, 1]], ![![26, -2, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![21, -15, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![21, -15, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![21, 74, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![21, -15, 1], ![-7, 5, -119], ![-347, 464, -25]]]
  hmulB := by decide  
  f := ![![![-20, 15, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -74, 89]], ![![0, -1, 1], ![28, 99, -119], ![2, 26, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [46, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 88], [0, 1]]
 g := ![![[80, 45], [53], [87], [62, 40], [28, 71], [1]], ![[20, 44], [53], [87], [68, 49], [52, 18], [1]]]
 h' := ![![[58, 88], [59, 57], [19, 26], [85, 49], [47, 29], [43, 58], [0, 1]], ![[0, 1], [72, 32], [14, 63], [79, 40], [38, 60], [25, 31], [58, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [5, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [46, 31, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1966, 2129, -4764]
  a := ![3, -3, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1102, 3985, -4764]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![30, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![30, 1, 0]] 
 ![![89, 0, 0], ![30, 1, 0], ![25, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![30, 1, 0], ![2, 29, 8], ![23, -31, 31]]]
  hmulB := by decide  
  f := ![![![157, 2696, 744], ![89, -8277, 0]], ![![32, 898, 248], ![90, -2759, 0]], ![![35, 757, 209], ![52, -2325, 0]]]
  g := ![![![1, 0, 0], ![-30, 89, 0], ![-25, 0, 89]], ![![0, 1, 0], ![-12, 29, 8], ![2, -31, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![21, -15, 1]] ![![89, 0, 0], ![30, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![2670, 89, 0]], ![![1869, -1335, 89], ![623, -445, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![30, 1, 0]]], ![![![21, -15, 1]], ![![7, -5, -1]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![12, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![12, 1, 0]] 
 ![![97, 0, 0], ![12, 1, 0], ![8, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![12, 1, 0], ![2, 11, 8], ![23, -31, 13]]]
  hmulB := by decide  
  f := ![![![3133, 17616, 12816], ![582, -155394, 0]], ![![384, 2177, 1584], ![98, -19206, 0]], ![![248, 1452, 1057], ![132, -12816, 0]]]
  g := ![![![1, 0, 0], ![-12, 97, 0], ![-8, 0, 97]], ![![0, 1, 0], ![-2, 11, 8], ![3, -31, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![30, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![30, 1, 0]] 
 ![![97, 0, 0], ![30, 1, 0], ![37, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![30, 1, 0], ![2, 29, 8], ![23, -31, 31]]]
  hmulB := by decide  
  f := ![![![-599, -9568, -2640], ![-194, 32010, 0]], ![![-204, -2958, -816], ![1, 9894, 0]], ![![-239, -3650, -1007], ![-40, 12210, 0]]]
  g := ![![![1, 0, 0], ![-30, 97, 0], ![-37, 0, 97]], ![![0, 1, 0], ![-12, 29, 8], ![-2, -31, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-42, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-42, 1, 0]] 
 ![![97, 0, 0], ![55, 1, 0], ![17, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-42, 1, 0], ![2, -43, 8], ![23, -31, -41]]]
  hmulB := by decide  
  f := ![![![751, -20635, 3840], ![-485, -46560, 0]], ![![419, -11693, 2176], ![-290, -26384, 0]], ![![155, -3617, 673], ![-31, -8160, 0]]]
  g := ![![![1, 0, 0], ![-55, 97, 0], ![-17, 0, 97]], ![![-1, 1, 0], ![23, -43, 8], ![25, -31, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![12, 1, 0]] ![![97, 0, 0], ![30, 1, 0]]
  ![![97, 0, 0], ![21, -7, 1]] where
 M := ![![![9409, 0, 0], ![2910, 97, 0]], ![![1164, 97, 0], ![362, 41, 8]]]
 hmul := by decide  
 g := ![![![![76, 7, -1], ![97, 0, 0]], ![![9, 8, -1], ![97, 0, 0]]], ![![![-9, 8, -1], ![97, 0, 0]], ![![2, 1, 0], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![21, -7, 1]] ![![97, 0, 0], ![-42, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-4074, 97, 0]], ![![2037, -679, 97], ![-873, 291, -97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-42, 1, 0]]], ![![![21, -7, 1]], ![![-9, 3, -1]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![59, 27, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![59, 27, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![59, 27, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![59, 27, 1], ![77, 1, 217], ![619, -838, 55]]]
  hmulB := by decide  
  f := ![![![-58, -27, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -27, 101]], ![![0, 0, 1], ![-126, -58, 217], ![-26, -23, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [4, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 100], [0, 1]]
 g := ![![[35, 76], [13], [46, 71], [56], [4], [62, 1]], ![[0, 25], [13], [4, 30], [56], [4], [23, 100]]]
 h' := ![![[62, 100], [70, 51], [18, 66], [15, 77], [80, 64], [55, 2], [0, 1]], ![[0, 1], [0, 50], [70, 35], [42, 24], [8, 37], [78, 99], [62, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [14, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [4, 39, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-84152, -26356, -1173444]
  a := ![-65, 1, -196]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![684644, 313432, -1173444]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-15, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-15, 1, 0]] 
 ![![101, 0, 0], ![86, 1, 0], ![46, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-15, 1, 0], ![2, -16, 8], ![23, -31, -14]]]
  hmulB := by decide  
  f := ![![![1155, -9470, 4736], ![-202, -59792, 0]], ![![979, -8062, 4032], ![-201, -50904, 0]], ![![525, -4313, 2157], ![-99, -27232, 0]]]
  g := ![![![1, 0, 0], ![-86, 101, 0], ![-46, 0, 101]], ![![-1, 1, 0], ![10, -16, 8], ![33, -31, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![59, 27, 1]] ![![101, 0, 0], ![-15, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-1515, 101, 0]], ![![5959, 2727, 101], ![-808, -404, 202]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-15, 1, 0]]], ![![![59, 27, 1]], ![![-8, -4, 2]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![33, -48, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![33, -48, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![33, 55, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![33, -48, 1], ![-73, 50, -383], ![-1106, 1487, -46]]]
  hmulB := by decide  
  f := ![![![-32, 48, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -55, 103]], ![![0, -1, 1], ![122, 205, -383], ![4, 39, -46]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [86, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 102], [0, 1]]
 g := ![![[71, 63], [93, 50], [39, 81], [25], [23], [74, 1]], ![[98, 40], [85, 53], [59, 22], [25], [23], [45, 102]]]
 h' := ![![[74, 102], [36, 75], [45, 16], [39, 94], [51, 5], [22, 34], [0, 1]], ![[0, 1], [24, 28], [96, 87], [94, 9], [9, 98], [66, 69], [74, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [76, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [86, 29, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2920, 2927, -9346]
  a := ![-4, 3, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2966, 5019, -9346]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-29, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-29, 1, 0]] 
 ![![103, 0, 0], ![74, 1, 0], ![46, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-29, 1, 0], ![2, -30, 8], ![23, -31, -28]]]
  hmulB := by decide  
  f := ![![![12635, -212946, 56800], ![-5562, -731300, 0]], ![![9070, -152961, 40800], ![-4016, -525300, 0]], ![![5640, -95102, 25367], ![-2494, -326600, 0]]]
  g := ![![![1, 0, 0], ![-74, 103, 0], ![-46, 0, 103]], ![![-1, 1, 0], ![18, -30, 8], ![35, -31, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![33, -48, 1]] ![![103, 0, 0], ![-29, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-2987, 103, 0]], ![![3399, -4944, 103], ![-1030, 1442, -412]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-29, 1, 0]]], ![![![33, -48, 1]], ![![-10, 14, -4]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![1, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![1, 1, 0]] 
 ![![107, 0, 0], ![1, 1, 0], ![27, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![1, 1, 0], ![2, 0, 8], ![23, -31, 2]]]
  hmulB := by decide  
  f := ![![![-107, 0, -432], ![0, 5778, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-27, 0, -109], ![0, 1458, 0]]]
  g := ![![![1, 0, 0], ![-1, 107, 0], ![-27, 0, 107]], ![![0, 1, 0], ![-2, 0, 8], ![0, -31, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![13, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![13, 1, 0]] 
 ![![107, 0, 0], ![13, 1, 0], ![61, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![13, 1, 0], ![2, 12, 8], ![23, -31, 14]]]
  hmulB := by decide  
  f := ![![![-131, -792, -528], ![0, 7062, 0]], ![![-16, -96, -64], ![1, 856, 0]], ![![-81, -452, -301], ![52, 4026, 0]]]
  g := ![![![1, 0, 0], ![-13, 107, 0], ![-61, 0, 107]], ![![0, 1, 0], ![-6, 12, 8], ![-4, -31, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-14, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-14, 1, 0]] 
 ![![107, 0, 0], ![93, 1, 0], ![81, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-14, 1, 0], ![2, -15, 8], ![23, -31, -13]]]
  hmulB := by decide  
  f := ![![![6231, -47869, 25536], ![-1177, -341544, 0]], ![![5409, -41600, 22192], ![-1069, -296818, 0]], ![![4713, -36237, 19331], ![-921, -258552, 0]]]
  g := ![![![1, 0, 0], ![-93, 107, 0], ![-81, 0, 107]], ![![-1, 1, 0], ![7, -15, 8], ![37, -31, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![1, 1, 0]] ![![107, 0, 0], ![13, 1, 0]]
  ![![107, 0, 0], ![42, 15, 1]] where
 M := ![![![11449, 0, 0], ![1391, 107, 0]], ![![107, 107, 0], ![15, 13, 8]]]
 hmul := by decide  
 g := ![![![![65, -15, -1], ![107, 0, 0]], ![![-29, -14, -1], ![107, 0, 0]]], ![![![-41, -14, -1], ![107, 0, 0]], ![![-3, -1, 0], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![42, 15, 1]] ![![107, 0, 0], ![-14, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-1498, 107, 0]], ![![4494, 1605, 107], ![-535, -214, 107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-14, 1, 0]]], ![![![42, 15, 1]], ![![-5, -2, 1]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-21, 10, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-21, 10, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![88, 10, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-21, 10, 1], ![43, -62, 81], ![228, -311, -42]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-88, -10, 109]], ![![-1, 0, 1], ![-65, -8, 81], ![36, 1, -42]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [100, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 108], [0, 1]]
 g := ![![[17, 12], [5], [43, 61], [7, 7], [71], [44, 1]], ![[0, 97], [5], [2, 48], [97, 102], [71], [88, 108]]]
 h' := ![![[44, 108], [48, 98], [60, 88], [63, 37], [59, 15], [69, 92], [0, 1]], ![[0, 1], [0, 11], [8, 21], [56, 72], [65, 94], [84, 17], [44, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [48, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [100, 65, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-924, 658, -5188]
  a := ![-3, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4180, 482, -5188]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![28, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![28, 1, 0]] 
 ![![109, 0, 0], ![28, 1, 0], ![42, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![28, 1, 0], ![2, 27, 8], ![23, -31, 29]]]
  hmulB := by decide  
  f := ![![![1193, 17977, 5328], ![545, -72594, 0]], ![![286, 4615, 1368], ![219, -18639, 0]], ![![462, 6927, 2053], ![201, -27972, 0]]]
  g := ![![![1, 0, 0], ![-28, 109, 0], ![-42, 0, 109]], ![![0, 1, 0], ![-10, 27, 8], ![-3, -31, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-21, 10, 1]] ![![109, 0, 0], ![28, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![3052, 109, 0]], ![![-2289, 1090, 109], ![-545, 218, 109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![28, 1, 0]]], ![![![-21, 10, 1]], ![![-5, 2, 1]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 4, -2]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-5, 4, -2]] 
 ![![113, 0, 0], ![0, 113, 0], ![59, 111, 1]] where
  M :=![![![-5, 4, -2], ![-38, 53, 30], ![96, -122, 61]]]
  hmulB := by decide  
  f := ![![![-61, 0, -2]], ![![-46, 1, -2]], ![![-77, 1, -3]]]
  g := ![![![1, 2, -2], ![-16, -29, 30], ![-31, -61, 61]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [40, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 112], [0, 1]]
 g := ![![[24, 77], [69], [4], [1], [60, 104], [57, 1]], ![[6, 36], [69], [4], [1], [112, 9], [1, 112]]]
 h' := ![![[57, 112], [4, 90], [74, 71], [11, 111], [86, 112], [93, 45], [0, 1]], ![[0, 1], [49, 23], [53, 42], [10, 2], [29, 1], [59, 68], [57, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101]]
 b := ![[], [58, 107]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [40, 56, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17382, -2276, -226105]
  a := ![22, -1, 87]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![117901, 222083, -226105]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 2]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![61, 0, 2]] 
 ![![113, 0, 0], ![15, 1, 0], ![87, 0, 1]] where
  M :=![![![61, 0, 2], ![46, -1, 2], ![-4, -2, -1]]]
  hmulB := by decide  
  f := ![![![5, -4, 2]], ![![1, -1, 0]], ![![3, -2, 1]]]
  g := ![![![-1, 0, 2], ![-1, -1, 2], ![1, -2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-5, 4, -2]] ![![61, 0, 2]]
  ![![113, 0, 0]] where
 M := ![![![-113, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-41, -61, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-41, -61, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![86, 66, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-41, -61, 1], ![-99, -11, -487], ![-1405, 1890, -133]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-86, -66, 127]], ![![-1, -1, 1], ![329, 253, -487], ![79, 84, -133]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [71, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 126], [0, 1]]
 g := ![![[78, 34], [117, 11], [21, 13], [124, 2], [38, 2], [50, 1]], ![[0, 93], [32, 116], [36, 114], [97, 125], [11, 125], [100, 126]]]
 h' := ![![[50, 126], [75, 62], [33, 30], [86, 34], [96, 16], [6, 16], [0, 1]], ![[0, 1], [0, 65], [9, 97], [8, 93], [7, 111], [44, 111], [50, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [90, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [71, 77, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![117, 13, 56]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37, -29, 56]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-21, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-21, 1, 0]] 
 ![![127, 0, 0], ![106, 1, 0], ![6, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-21, 1, 0], ![2, -22, 8], ![23, -31, -20]]]
  hmulB := by decide  
  f := ![![![-809, 9370, -3408], ![254, 54102, 0]], ![![-667, 7808, -2840], ![255, 45085, 0]], ![![-24, 442, -161], ![98, 2556, 0]]]
  g := ![![![1, 0, 0], ![-106, 127, 0], ![-6, 0, 127]], ![![-1, 1, 0], ![18, -22, 8], ![27, -31, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-41, -61, 1]] ![![127, 0, 0], ![-21, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-2667, 127, 0]], ![![-5207, -7747, 127], ![762, 1270, -508]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-21, 1, 0]]], ![![![-41, -61, 1]], ![![6, 10, -4]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![20, -29, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![20, -29, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![20, 102, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![20, -29, 1], ![-35, 18, -231], ![-669, 898, -40]]]
  hmulB := by decide  
  f := ![![![-19, 29, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -102, 131]], ![![0, -1, 1], ![35, 180, -231], ![1, 38, -40]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [78, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 130], [0, 1]]
 g := ![![[129, 114], [21, 89], [59], [84], [33], [101], [1]], ![[97, 17], [19, 42], [59], [84], [33], [101], [1]]]
 h' := ![![[25, 130], [65, 101], [112, 58], [103, 37], [74, 79], [40, 66], [53, 25], [0, 1]], ![[0, 1], [101, 30], [121, 73], [111, 94], [84, 52], [118, 65], [23, 106], [25, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [57, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [78, 106, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1999, 1844, -10128]
  a := ![5, -2, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1531, 7900, -10128]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-31, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-31, 1, 0]] 
 ![![131, 0, 0], ![100, 1, 0], ![40, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-31, 1, 0], ![2, -32, 8], ![23, -31, -30]]]
  hmulB := by decide  
  f := ![![![-5158, 89969, -22496], ![1965, 368372, 0]], ![![-3919, 68660, -17168], ![1573, 281126, 0]], ![![-1561, 27471, -6869], ![659, 112480, 0]]]
  g := ![![![1, 0, 0], ![-100, 131, 0], ![-40, 0, 131]], ![![-1, 1, 0], ![22, -32, 8], ![33, -31, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![20, -29, 1]] ![![131, 0, 0], ![-31, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-4061, 131, 0]], ![![2620, -3799, 131], ![-655, 917, -262]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-31, 1, 0]]], ![![![20, -29, 1]], ![![-5, 7, -2]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-52, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-52, 1, 0]] 
 ![![137, 0, 0], ![85, 1, 0], ![101, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-52, 1, 0], ![2, -53, 8], ![23, -31, -51]]]
  hmulB := by decide  
  f := ![![![9645, -314777, 47520], ![-5891, -813780, 0]], ![![6019, -195279, 29480], ![-3561, -504845, 0]], ![![7117, -232062, 35033], ![-4326, -599940, 0]]]
  g := ![![![1, 0, 0], ![-85, 137, 0], ![-101, 0, 137]], ![![-1, 1, 0], ![27, -53, 8], ![57, -31, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-33, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-33, 1, 0]] 
 ![![137, 0, 0], ![104, 1, 0], ![134, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-33, 1, 0], ![2, -34, 8], ![23, -31, -32]]]
  hmulB := by decide  
  f := ![![![7641, -141080, 33200], ![-2740, -568550, 0]], ![![5806, -107085, 25200], ![-2054, -431550, 0]], ![![7452, -137990, 32473], ![-2770, -556100, 0]]]
  g := ![![![1, 0, 0], ![-104, 137, 0], ![-134, 0, 137]], ![![-1, 1, 0], ![18, -34, 8], ![55, -31, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-52, 1, 0]] ![![137, 0, 0], ![-52, 1, 0]]
  ![![137, 0, 0], ![30, 4, 1]] where
 M := ![![![18769, 0, 0], ![-7124, 137, 0]], ![![-7124, 137, 0], ![2706, -105, 8]]]
 hmul := by decide  
 g := ![![![![107, -4, -1], ![137, 0, 0]], ![![-52, 1, 0], ![0, 0, 0]]], ![![![-52, 1, 0], ![0, 0, 0]], ![![18, -1, 0], ![8, 0, 0]]]]
 hle2 := by decide  
def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![30, 4, 1]] ![![137, 0, 0], ![-33, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-4521, 137, 0]], ![![4110, 548, 137], ![-959, -137, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-33, 1, 0]]], ![![![30, 4, 1]], ![![-7, -1, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB274I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB274I2 : PrimesBelowBoundCertificateInterval O 79 137 274 where
  m := 11
  g := ![2, 2, 3, 2, 2, 3, 2, 2, 2, 2, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB274I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N0, I137N1]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![97, 97, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![17161, 131]
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
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
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
      exact NI107N1
      exact NI107N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N0, I97N1, I97N2, I101N1, I103N1, I107N0, I107N1, I107N2, I109N1, I113N1, I127N1, I131N1, I137N0, I137N1]
  Il := ![[I83N1], [I89N1], [I97N0, I97N1, I97N2], [I101N1], [I103N1], [I107N0, I107N1, I107N2], [I109N1], [I113N1], [I127N1], [I131N1], [I137N0, I137N0, I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
