
import IdealArithmetic.Examples.NF3_1_933107_2.RI3_1_933107_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-54, 43, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-54, 43, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![29, 43, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-54, 43, 1], ![-218, -17, 44], ![-9592, 1410, 27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -43, 83]], ![![-1, 0, 1], ![-18, -23, 44], ![-125, 3, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [38, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 82], [0, 1]]
 g := ![![[46, 59], [57, 28], [3], [77], [6, 25], [1]], ![[0, 24], [0, 55], [3], [77], [47, 58], [1]]]
 h' := ![![[78, 82], [75, 15], [77, 32], [5, 13], [21, 49], [45, 78], [0, 1]], ![[0, 1], [0, 68], [0, 51], [23, 70], [25, 34], [70, 5], [78, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [2, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [38, 5, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-616, -112, 36]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20, -20, 36]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![39, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![39, 1, 0]] 
 ![![83, 0, 0], ![39, 1, 0], ![56, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![39, 1, 0], ![0, 39, 1], ![-218, 37, 40]]]
  hmulB := by decide  
  f := ![![![937, 24, 0], ![-1992, 0, 0]], ![![429, 11, 0], ![-912, 0, 0]], ![![604, 15, 0], ![-1284, 1, 0]]]
  g := ![![![1, 0, 0], ![-39, 83, 0], ![-56, 0, 83]], ![![0, 1, 0], ![-19, 39, 1], ![-47, 37, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-54, 43, 1]] ![![83, 0, 0], ![39, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![3237, 83, 0]], ![![-4482, 3569, 83], ![-2324, 1660, 83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![39, 1, 0]]], ![![![-54, 43, 1]], ![![-28, 20, 1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![1, -41, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![1, -41, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![1, 48, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![1, -41, 1], ![-218, 38, -40], ![8720, -1698, -2]]]
  hmulB := by decide  
  f := ![![![0, 41, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -48, 89]], ![![0, -1, 1], ![-2, 22, -40], ![98, -18, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [64, 31, 1] where
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
 g := ![![[13, 32], [49], [55], [28, 67], [76, 71], [1]], ![[0, 57], [49], [55], [87, 22], [11, 18], [1]]]
 h' := ![![[58, 88], [15, 78], [6, 7], [77, 77], [31, 44], [25, 58], [0, 1]], ![[0, 1], [0, 11], [56, 82], [4, 12], [2, 45], [7, 31], [58, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [68, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [64, 31, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![688, -2131, 421]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, -251, 421]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![40, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![40, 1, 0]] 
 ![![89, 0, 0], ![40, 1, 0], ![2, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![40, 1, 0], ![0, 40, 1], ![-218, 37, 41]]]
  hmulB := by decide  
  f := ![![![1081, 27, 0], ![-2403, 0, 0]], ![![520, 13, 0], ![-1156, 0, 0]], ![![18, 0, 0], ![-40, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 89, 0], ![-2, 0, 89]], ![![0, 1, 0], ![-18, 40, 1], ![-20, 37, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![1, -41, 1]] ![![89, 0, 0], ![40, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![3560, 89, 0]], ![![89, -3649, 89], ![-178, -1602, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![40, 1, 0]]], ![![![1, -41, 1]], ![![-2, -18, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![26, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![26, 1, 0]] 
 ![![97, 0, 0], ![26, 1, 0], ![3, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![26, 1, 0], ![0, 26, 1], ![-218, 37, 27]]]
  hmulB := by decide  
  f := ![![![989, 38, 0], ![-3686, 0, 0]], ![![234, 9, 0], ![-872, 0, 0]], ![![7, 0, 0], ![-26, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 97, 0], ![-3, 0, 97]], ![![0, 1, 0], ![-7, 26, 1], ![-13, 37, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-15, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-15, 1, 0]] 
 ![![97, 0, 0], ![82, 1, 0], ![66, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-15, 1, 0], ![0, -15, 1], ![-218, 37, -14]]]
  hmulB := by decide  
  f := ![![![256, -17, 0], ![1649, 0, 0]], ![![226, -15, 0], ![1456, 0, 0]], ![![198, -13, 0], ![1276, 1, 0]]]
  g := ![![![1, 0, 0], ![-82, 97, 0], ![-66, 0, 97]], ![![-1, 1, 0], ![12, -15, 1], ![-24, 37, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-12, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-12, 1, 0]] 
 ![![97, 0, 0], ![85, 1, 0], ![50, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-12, 1, 0], ![0, -12, 1], ![-218, 37, -11]]]
  hmulB := by decide  
  f := ![![![1093, -91, 0], ![8827, 0, 0]], ![![961, -80, 0], ![7761, 0, 0]], ![![578, -48, 0], ![4668, 1, 0]]]
  g := ![![![1, 0, 0], ![-85, 97, 0], ![-50, 0, 97]], ![![-1, 1, 0], ![10, -12, 1], ![-29, 37, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![26, 1, 0]] ![![97, 0, 0], ![-15, 1, 0]]
  ![![97, 0, 0], ![-2, 11, 1]] where
 M := ![![![9409, 0, 0], ![-1455, 97, 0]], ![![2522, 97, 0], ![-390, 11, 1]]]
 hmul := by decide  
 g := ![![![![97, 0, 0], ![0, 0, 0]], ![![-13, -10, -1], ![97, 0, 0]]], ![![![26, 1, 0], ![0, 0, 0]], ![![-4, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-2, 11, 1]] ![![97, 0, 0], ![-12, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-1164, 97, 0]], ![![-194, 1067, 97], ![-194, -97, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-12, 1, 0]]], ![![![-2, 11, 1]], ![![-2, -1, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-36, -23, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-36, -23, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![65, 78, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-36, -23, 1], ![-218, 1, -22], ![4796, -1032, -21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -78, 101]], ![![-1, -1, 1], ![12, 17, -22], ![61, 6, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [49, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 100], [0, 1]]
 g := ![![[68, 33], [25], [7, 33], [6], [82], [1, 1]], ![[0, 68], [25], [40, 68], [6], [82], [2, 100]]]
 h' := ![![[1, 100], [72, 29], [61, 5], [10, 29], [100, 39], [52, 53], [0, 1]], ![[0, 1], [0, 72], [66, 96], [39, 72], [38, 62], [4, 48], [1, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [29, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [49, 100, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2037, -283, 65]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-62, -53, 65]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![22, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![22, 1, 0]] 
 ![![101, 0, 0], ![22, 1, 0], ![21, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![22, 1, 0], ![0, 22, 1], ![-218, 37, 23]]]
  hmulB := by decide  
  f := ![![![419, 19, 0], ![-1919, 0, 0]], ![![66, 3, 0], ![-302, 0, 0]], ![![71, 3, 0], ![-325, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 101, 0], ![-21, 0, 101]], ![![0, 1, 0], ![-5, 22, 1], ![-15, 37, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-36, -23, 1]] ![![101, 0, 0], ![22, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![2222, 101, 0]], ![![-3636, -2323, 101], ![-1010, -505, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![22, 1, 0]]], ![![![-36, -23, 1]], ![![-10, -5, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-14, 44, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-14, 44, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![89, 44, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-14, 44, 1], ![-218, 23, 45], ![-9810, 1447, 68]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-89, -44, 103]], ![![-1, 0, 1], ![-41, -19, 45], ![-154, -15, 68]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [44, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 102], [0, 1]]
 g := ![![[74, 50], [93, 34], [48, 55], [49], [18], [40, 1]], ![[14, 53], [11, 69], [85, 48], [49], [18], [80, 102]]]
 h' := ![![[40, 102], [28, 87], [51, 31], [4, 40], [10, 7], [94, 11], [0, 1]], ![[0, 1], [6, 16], [55, 72], [59, 63], [84, 96], [19, 92], [40, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [55, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [44, 63, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-546, -1786, 142]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-128, -78, 142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-45, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-45, 1, 0]] 
 ![![103, 0, 0], ![58, 1, 0], ![35, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-45, 1, 0], ![0, -45, 1], ![-218, 37, -44]]]
  hmulB := by decide  
  f := ![![![4366, -97, 0], ![9991, 0, 0]], ![![2476, -55, 0], ![5666, 0, 0]], ![![1550, -34, 0], ![3547, 1, 0]]]
  g := ![![![1, 0, 0], ![-58, 103, 0], ![-35, 0, 103]], ![![-1, 1, 0], ![25, -45, 1], ![-8, 37, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-14, 44, 1]] ![![103, 0, 0], ![-45, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-4635, 103, 0]], ![![-1442, 4532, 103], ![412, -1957, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-45, 1, 0]]], ![![![-14, 44, 1]], ![![4, -19, 0]]]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [49, 31, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 39, 86], [87, 67, 21], [0, 1]]
 g := ![![[47, 8, 105], [58, 89, 79], [51, 25], [46, 44, 23], [49, 105], [1]], ![[6, 78, 102, 9], [62, 9, 2, 27], [78, 11], [101, 67, 38, 41], [27, 27], [59, 97, 13, 48]], ![[4, 13, 99, 45], [69, 74, 71, 65], [94, 79], [10, 78, 46, 31], [39, 101], [86, 65, 55, 59]]]
 h' := ![![[51, 39, 86], [47, 61, 76], [11, 48, 20], [100, 56, 5], [0, 12, 39], [58, 76, 31], [0, 1]], ![[87, 67, 21], [61, 39, 66], [39, 6, 11], [104, 59, 15], [66, 50, 7], [76, 61, 53], [51, 39, 86]], ![[0, 1], [56, 7, 72], [84, 53, 76], [14, 99, 87], [57, 45, 61], [91, 77, 23], [87, 67, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 27], []]
 b := ![[], [9, 71, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [49, 31, 76, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-55105, 2354, 2354]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-515, 22, 22]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![0, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![0, 1, 0]] 
 ![![109, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![0, 1, 0], ![0, 0, 1], ![-218, 37, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![0, 1, 0], ![0, 0, 1], ![-2, 37, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-37, -1, 1]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-37, -1, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![72, 108, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-37, -1, 1], ![-218, 0, 0], ![0, -218, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -108, 109]], ![![-1, -1, 1], ![-2, 0, 0], ![0, -2, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [48, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 108], [0, 1]]
 g := ![![[107, 25], [74], [47, 20], [89, 31], [35], [96, 1]], ![[0, 84], [74], [5, 89], [13, 78], [35], [83, 108]]]
 h' := ![![[96, 108], [44, 104], [33, 69], [88, 42], [92, 24], [79, 12], [0, 1]], ![[0, 1], [0, 5], [8, 40], [87, 67], [107, 85], [32, 97], [96, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [29, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where
  n := 2
  hpos := by decide
  P := [48, 13, 1]
  hirr := P109P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8440, 1510, 452]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-376, -434, 452]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![0, 1, 0]] ![![109, 0, 0], ![-37, -1, 1]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-4033, -109, 109]], ![![0, 109, 0], ![-218, 0, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-37, -1, 1]]], ![![![0, 1, 0]], ![![-2, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107623, -32397, 3760]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![107623, -32397, 3760]] 
 ![![113, 0, 0], ![0, 113, 0], ![89, 74, 1]] where
  M :=![![![107623, -32397, 3760], ![-819680, 246743, -28637], ![6242866, -1879249, 218106]]]
  hmulB := by decide  
  f := ![![![665, 34, -7]], ![![1526, 406, 27]], ![![1471, 315, 16]]]
  g := ![![![-2009, -2749, 3760], ![15301, 20937, -28637], ![-116536, -159461, 218106]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [101, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 112], [0, 1]]
 g := ![![[86, 112], [91], [52], [22], [12, 8], [15, 1]], ![[71, 1], [91], [52], [22], [19, 105], [30, 112]]]
 h' := ![![[15, 112], [90, 15], [44, 54], [95, 39], [31, 19], [67, 11], [0, 1]], ![[0, 1], [89, 98], [63, 59], [2, 74], [90, 94], [6, 102], [15, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [46, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [101, 98, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1094, -115, -55]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![53, 35, -55]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![665, 34, -7]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![665, 34, -7]] 
 ![![113, 0, 0], ![38, 1, 0], ![25, 0, 1]] where
  M :=![![![665, 34, -7], ![1526, 406, 27], ![-5886, 2525, 433]]]
  hmulB := by decide  
  f := ![![![107623, -32397, 3760]], ![![28938, -8711, 1011]], ![![79057, -23798, 2762]]]
  g := ![![![-4, 34, -7], ![-129, 406, 27], ![-997, 2525, 433]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![107623, -32397, 3760]] ![![665, 34, -7]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![25, 36, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![25, 36, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![25, 36, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![25, 36, 1], ![-218, 62, 37], ![-8066, 1151, 99]]]
  hmulB := by decide  
  f := ![![![-24, -36, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -36, 127]], ![![0, 0, 1], ![-9, -10, 37], ![-83, -19, 99]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [90, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 126], [0, 1]]
 g := ![![[111, 13], [61, 79], [56, 73], [82, 124], [23, 107], [43, 1]], ![[35, 114], [29, 48], [20, 54], [80, 3], [52, 20], [86, 126]]]
 h' := ![![[43, 126], [98, 34], [40, 98], [113, 33], [89, 39], [67, 108], [0, 1]], ![[0, 1], [36, 93], [63, 29], [8, 94], [115, 88], [12, 19], [43, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [104, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [90, 84, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1654, -492, 325]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-77, -96, 325]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-37, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-37, 1, 0]] 
 ![![127, 0, 0], ![90, 1, 0], ![28, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-37, 1, 0], ![0, -37, 1], ![-218, 37, -36]]]
  hmulB := by decide  
  f := ![![![4256, -115, 0], ![14605, 0, 0]], ![![2998, -81, 0], ![10288, 0, 0]], ![![936, -25, 0], ![3212, 1, 0]]]
  g := ![![![1, 0, 0], ![-90, 127, 0], ![-28, 0, 127]], ![![-1, 1, 0], ![26, -37, 1], ![-20, 37, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![25, 36, 1]] ![![127, 0, 0], ![-37, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-4699, 127, 0]], ![![3175, 4572, 127], ![-1143, -1270, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-37, 1, 0]]], ![![![25, 36, 1]], ![![-9, -10, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-72, -38, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-72, -38, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![59, 93, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-72, -38, 1], ![-218, -35, -37], ![8066, -1587, -72]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -93, 131]], ![![-1, -1, 1], ![15, 26, -37], ![94, 39, -72]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [99, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 130], [0, 1]]
 g := ![![[22, 45], [54, 39], [58], [3], [9], [43], [1]], ![[0, 86], [0, 92], [58], [3], [9], [43], [1]]]
 h' := ![![[49, 130], [25, 69], [57, 63], [67, 78], [87, 38], [42, 3], [32, 49], [0, 1]], ![[0, 1], [0, 62], [0, 68], [90, 53], [115, 93], [58, 128], [75, 82], [49, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [70, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [99, 82, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8115, -3064, 384]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-111, -296, 384]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![37, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![37, 1, 0]] 
 ![![131, 0, 0], ![37, 1, 0], ![72, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![37, 1, 0], ![0, 37, 1], ![-218, 37, 38]]]
  hmulB := by decide  
  f := ![![![2036, 55, 0], ![-7205, 0, 0]], ![![518, 14, 0], ![-1833, 0, 0]], ![![1084, 29, 0], ![-3836, 1, 0]]]
  g := ![![![1, 0, 0], ![-37, 131, 0], ![-72, 0, 131]], ![![0, 1, 0], ![-11, 37, 1], ![-33, 37, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-72, -38, 1]] ![![131, 0, 0], ![37, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![4847, 131, 0]], ![![-9432, -4978, 131], ![-2882, -1441, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![37, 1, 0]]], ![![![-72, -38, 1]], ![![-22, -11, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![59, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![59, 1, 0]] 
 ![![137, 0, 0], ![59, 1, 0], ![81, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![59, 1, 0], ![0, 59, 1], ![-218, 37, 60]]]
  hmulB := by decide  
  f := ![![![2597, 44, 0], ![-6028, 0, 0]], ![![1121, 19, 0], ![-2602, 0, 0]], ![![1501, 25, 0], ![-3484, 1, 0]]]
  g := ![![![1, 0, 0], ![-59, 137, 0], ![-81, 0, 137]], ![![0, 1, 0], ![-26, 59, 1], ![-53, 37, 60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-30, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-30, 1, 0]] 
 ![![137, 0, 0], ![107, 1, 0], ![59, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-30, 1, 0], ![0, -30, 1], ![-218, 37, -29]]]
  hmulB := by decide  
  f := ![![![1321, -44, 0], ![6028, 0, 0]], ![![991, -33, 0], ![4522, 0, 0]], ![![547, -18, 0], ![2496, 1, 0]]]
  g := ![![![1, 0, 0], ![-107, 137, 0], ![-59, 0, 137]], ![![-1, 1, 0], ![23, -30, 1], ![-18, 37, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![59, 1, 0]] ![![137, 0, 0], ![-30, 1, 0]]
  ![![137, 0, 0], ![11, 29, 1]] where
 M := ![![![18769, 0, 0], ![-4110, 137, 0]], ![![8083, 137, 0], ![-1770, 29, 1]]]
 hmul := by decide  
 g := ![![![![126, -29, -1], ![137, 0, 0]], ![![-30, 1, 0], ![0, 0, 0]]], ![![![48, -28, -1], ![137, 0, 0]], ![![-13, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![11, 29, 1]] ![![137, 0, 0], ![-30, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-4110, 137, 0]], ![![1507, 3973, 137], ![-548, -822, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-30, 1, 0]]], ![![![11, 29, 1]], ![![-4, -6, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
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
  g := ![2, 2, 3, 2, 2, 1, 2, 2, 2, 2, 3]
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
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N1]
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
    · exact ![1225043]
    · exact ![109, 11881]
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
      exact NI137N1
      exact NI137N1
  β := ![I83N1, I89N1, I97N0, I97N1, I97N2, I101N1, I103N1, I109N0, I113N1, I127N1, I131N1, I137N0, I137N1]
  Il := ![[I83N1], [I89N1], [I97N0, I97N1, I97N2], [I101N1], [I103N1], [], [I109N0], [I113N1], [I127N1], [I131N1], [I137N0, I137N1, I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
