
import IdealArithmetic.Examples.NF3_1_406700_5.RI3_1_406700_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -2, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![1, -2, 0]] 
 ![![83, 0, 0], ![41, 1, 0], ![62, 0, 1]] where
  M :=![![![1, -2, 0], ![0, 1, -2], ![-26, 94, -1]]]
  hmulB := by decide  
  f := ![![![187, -2, 4]], ![![93, -1, 2]], ![![140, -2, 3]]]
  g := ![![![1, -2, 0], ![1, 1, -2], ![-46, 94, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 4, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-1, 4, 0]] 
 ![![83, 0, 0], ![62, 1, 0], ![57, 0, 1]] where
  M :=![![![-1, 4, 0], ![0, -1, 4], ![52, -188, 3]]]
  hmulB := by decide  
  f := ![![![749, -12, 16]], ![![562, -9, 12]], ![![515, -8, 11]]]
  g := ![![![-3, 4, 0], ![-2, -1, 4], ![139, -188, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![1, -2, 0]] ![![-1, 4, 0]]
  ![![-1, 6, -8]] where
 M := ![![![-1, 6, -8]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![-1, 6, -8]] ![![-1, 4, 0]]
  ![![83, 0, 0]] where
 M := ![![![-415, 1494, 0]]]
 hmul := by decide  
 g := ![![![![-5, 18, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![48, -10, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![48, -10, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![48, 79, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![48, -10, 1], ![13, 1, -9], ![-117, 436, -8]]]
  hmulB := by decide  
  f := ![![![-47, 10, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-48, -79, 89]], ![![0, -1, 1], ![5, 8, -9], ![3, 12, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [73, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 88], [0, 1]]
 g := ![![[77, 50], [85], [49], [33, 44], [12, 18], [1]], ![[0, 39], [85], [49], [40, 45], [27, 71], [1]]]
 h' := ![![[75, 88], [30, 53], [19, 21], [83, 82], [14, 20], [16, 75], [0, 1]], ![[0, 1], [0, 36], [81, 68], [3, 7], [1, 69], [34, 14], [75, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [2, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [73, 14, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![112, -142, -57]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![32, 49, -57]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![9, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![9, 1, 0]] 
 ![![89, 0, 0], ![9, 1, 0], ![8, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![9, 1, 0], ![0, 9, 1], ![13, -47, 10]]]
  hmulB := by decide  
  f := ![![![73, 8, 0], ![-712, 0, 0]], ![![-9, -1, 0], ![90, 0, 0]], ![![-8, -1, 0], ![80, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 89, 0], ![-8, 0, 89]], ![![0, 1, 0], ![-1, 9, 1], ![4, -47, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![48, -10, 1]] ![![89, 0, 0], ![9, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![801, 89, 0]], ![![4272, -890, 89], ![445, -89, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![9, 1, 0]]], ![![![48, -10, 1]], ![![5, -1, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![62, -18, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![62, -18, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![62, 79, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![62, -18, 1], ![13, 15, -17], ![-221, 812, -2]]]
  hmulB := by decide  
  f := ![![![-61, 18, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-62, -79, 97]], ![![0, -1, 1], ![11, 14, -17], ![-1, 10, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [37, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 96], [0, 1]]
 g := ![![[32, 1], [8], [81], [27], [43], [77, 1]], ![[12, 96], [8], [81], [27], [43], [57, 96]]]
 h' := ![![[77, 96], [26, 1], [82, 69], [84, 88], [93, 67], [61, 72], [0, 1]], ![[0, 1], [6, 96], [60, 28], [70, 9], [14, 30], [76, 25], [77, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [3, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [37, 20, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21, 222, -368]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![235, 302, -368]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![17, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![17, 1, 0]] 
 ![![97, 0, 0], ![17, 1, 0], ![2, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![17, 1, 0], ![0, 17, 1], ![13, -47, 18]]]
  hmulB := by decide  
  f := ![![![579, 34, 0], ![-3298, 0, 0]], ![![85, 5, 0], ![-484, 0, 0]], ![![-14, -1, 0], ![80, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 97, 0], ![-2, 0, 97]], ![![0, 1, 0], ![-3, 17, 1], ![8, -47, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![62, -18, 1]] ![![97, 0, 0], ![17, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![1649, 97, 0]], ![![6014, -1746, 97], ![1067, -291, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![17, 1, 0]]], ![![![62, -18, 1]], ![![11, -3, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![1, 12, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![1, 12, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![1, 12, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![1, 12, 1], ![13, -46, 13], ![169, -598, -33]]]
  hmulB := by decide  
  f := ![![![0, 4, -1], ![-3, 8, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -12, 101]], ![![0, 0, 1], ![0, -2, 13], ![2, -2, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [28, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 100], [0, 1]]
 g := ![![[75, 21], [21], [60, 77], [25], [81], [21, 1]], ![[11, 80], [21], [61, 24], [25], [81], [42, 100]]]
 h' := ![![[21, 100], [74, 18], [37, 83], [26, 73], [76, 5], [18, 9], [0, 1]], ![[0, 1], [48, 83], [63, 18], [44, 28], [80, 96], [5, 92], [21, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [28, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [28, 80, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1009, 12, 1]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, 0, 1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-13, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-13, 1, 0]] 
 ![![101, 0, 0], ![88, 1, 0], ![33, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-13, 1, 0], ![0, -13, 1], ![13, -47, -12]]]
  hmulB := by decide  
  f := ![![![989, -76, 0], ![7676, 0, 0]], ![![872, -67, 0], ![6768, 0, 0]], ![![327, -25, 0], ![2538, 1, 0]]]
  g := ![![![1, 0, 0], ![-88, 101, 0], ![-33, 0, 101]], ![![-1, 1, 0], ![11, -13, 1], ![45, -47, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![1, 12, 1]] ![![101, 0, 0], ![-13, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-1313, 101, 0]], ![![101, 1212, 101], ![0, -202, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-13, 1, 0]]], ![![![1, 12, 1]], ![![0, -2, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![23, 13, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![23, 13, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![23, 13, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![23, 13, 1], ![13, -24, 14], ![182, -645, -10]]]
  hmulB := by decide  
  f := ![![![-22, -13, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -13, 103]], ![![0, 0, 1], ![-3, -2, 14], ![4, -5, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [47, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 102], [0, 1]]
 g := ![![[30, 23], [5, 59], [11, 79], [26], [28], [32, 1]], ![[45, 80], [39, 44], [67, 24], [26], [28], [64, 102]]]
 h' := ![![[32, 102], [74, 69], [101, 33], [60, 64], [56, 52], [41, 50], [0, 1]], ![[0, 1], [16, 34], [24, 70], [48, 39], [72, 51], [96, 53], [32, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [37, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [47, 71, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![158, 49, -638]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![144, 81, -638]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-14, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-14, 1, 0]] 
 ![![103, 0, 0], ![89, 1, 0], ![10, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-14, 1, 0], ![0, -14, 1], ![13, -47, -13]]]
  hmulB := by decide  
  f := ![![![1219, -87, 0], ![8961, 0, 0]], ![![1037, -74, 0], ![7623, 0, 0]], ![![142, -10, 0], ![1044, 1, 0]]]
  g := ![![![1, 0, 0], ![-89, 103, 0], ![-10, 0, 103]], ![![-1, 1, 0], ![12, -14, 1], ![42, -47, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![23, 13, 1]] ![![103, 0, 0], ![-14, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-1442, 103, 0]], ![![2369, 1339, 103], ![-309, -206, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-14, 1, 0]]], ![![![23, 13, 1]], ![![-3, -2, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![56, 47, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![56, 47, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![56, 47, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![56, 47, 1], ![13, 9, 48], ![624, -2243, 57]]]
  hmulB := by decide  
  f := ![![![-55, -47, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -47, 107]], ![![0, 0, 1], ![-25, -21, 48], ![-24, -46, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [25, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 106], [0, 1]]
 g := ![![[82, 30], [102, 89], [81], [], [39], [90, 1]], ![[0, 77], [87, 18], [81], [], [39], [73, 106]]]
 h' := ![![[90, 106], [18, 64], [8, 14], [0, 9], [104], [104, 50], [0, 1]], ![[0, 1], [0, 43], [91, 93], [61, 98], [104], [3, 57], [90, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [82, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [25, 17, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![64, -145, -60]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![32, 25, -60]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-48, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-48, 1, 0]] 
 ![![107, 0, 0], ![59, 1, 0], ![50, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-48, 1, 0], ![0, -48, 1], ![13, -47, -47]]]
  hmulB := by decide  
  f := ![![![2161, -45, 0], ![4815, 0, 0]], ![![1249, -26, 0], ![2783, 0, 0]], ![![1078, -22, 0], ![2402, 1, 0]]]
  g := ![![![1, 0, 0], ![-59, 107, 0], ![-50, 0, 107]], ![![-1, 1, 0], ![26, -48, 1], ![48, -47, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![56, 47, 1]] ![![107, 0, 0], ![-48, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-5136, 107, 0]], ![![5992, 5029, 107], ![-2675, -2247, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-48, 1, 0]]], ![![![56, 47, 1]], ![![-25, -21, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [47, 82, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 96, 68], [98, 12, 41], [0, 1]]
 g := ![![[101, 67, 31], [68, 88], [54, 74, 27], [23, 90, 97], [26, 27], [1]], ![[26, 36, 21, 47], [55, 64], [72, 70, 42, 2], [39, 22, 17, 67], [5, 9], [67, 60, 4, 76]], ![[75, 79, 38, 103], [34, 3], [45, 32, 97, 70], [71, 71, 70, 13], [83, 46], [66, 26, 76, 33]]]
 h' := ![![[49, 96, 68], [54, 89, 85], [78, 23, 52], [9, 24, 71], [6, 56, 73], [62, 27, 38], [0, 1]], ![[98, 12, 41], [95, 91, 96], [101, 49, 8], [13, 29, 86], [85, 54, 106], [50, 71, 3], [49, 96, 68]], ![[0, 1], [34, 38, 37], [18, 37, 49], [19, 56, 61], [11, 108, 39], [36, 11, 68], [98, 12, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 51], []]
 b := ![[], [45, 40, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [47, 82, 71, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![105839, -362425, -19075]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![971, -3325, -175]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![47, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![47, 1, 0]] 
 ![![113, 0, 0], ![47, 1, 0], ![51, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![47, 1, 0], ![0, 47, 1], ![13, -47, 48]]]
  hmulB := by decide  
  f := ![![![1646, 35, 0], ![-3955, 0, 0]], ![![658, 14, 0], ![-1581, 0, 0]], ![![772, 16, 0], ![-1855, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 113, 0], ![-51, 0, 113]], ![![0, 1, 0], ![-20, 47, 1], ![-2, -47, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-33, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-33, 1, 0]] 
 ![![113, 0, 0], ![80, 1, 0], ![41, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-33, 1, 0], ![0, -33, 1], ![13, -47, -32]]]
  hmulB := by decide  
  f := ![![![1189, -36, 0], ![4068, 0, 0]], ![![826, -25, 0], ![2826, 0, 0]], ![![439, -13, 0], ![1502, 1, 0]]]
  g := ![![![1, 0, 0], ![-80, 113, 0], ![-41, 0, 113]], ![![-1, 1, 0], ![23, -33, 1], ![45, -47, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-15, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-15, 1, 0]] 
 ![![113, 0, 0], ![98, 1, 0], ![1, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-15, 1, 0], ![0, -15, 1], ![13, -47, -14]]]
  hmulB := by decide  
  f := ![![![1531, -102, 0], ![11526, 0, 0]], ![![1336, -89, 0], ![10058, 0, 0]], ![![17, -1, 0], ![128, 1, 0]]]
  g := ![![![1, 0, 0], ![-98, 113, 0], ![-1, 0, 113]], ![![-1, 1, 0], ![13, -15, 1], ![41, -47, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![47, 1, 0]] ![![113, 0, 0], ![-33, 1, 0]]
  ![![113, 0, 0], ![31, 14, 1]] where
 M := ![![![12769, 0, 0], ![-3729, 113, 0]], ![![5311, 113, 0], ![-1551, 14, 1]]]
 hmul := by decide  
 g := ![![![![82, -14, -1], ![113, 0, 0]], ![![-33, 1, 0], ![0, 0, 0]]], ![![![16, -13, -1], ![113, 0, 0]], ![![-14, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![31, 14, 1]] ![![113, 0, 0], ![-15, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-1695, 113, 0]], ![![3503, 1582, 113], ![-452, -226, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-15, 1, 0]]], ![![![31, 14, 1]], ![![-4, -2, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![15, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![15, 1, 0]] 
 ![![127, 0, 0], ![15, 1, 0], ![29, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![15, 1, 0], ![0, 15, 1], ![13, -47, 16]]]
  hmulB := by decide  
  f := ![![![226, 15, 0], ![-1905, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![32, 2, 0], ![-269, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 127, 0], ![-29, 0, 127]], ![![0, 1, 0], ![-2, 15, 1], ![2, -47, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 7, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-2, 7, 0]] 
 ![![127, 0, 0], ![36, 1, 0], ![101, 0, 1]] where
  M :=![![![-2, 7, 0], ![0, -2, 7], ![91, -329, 5]]]
  hmulB := by decide  
  f := ![![![-2293, 35, -49]], ![![-655, 10, -14]], ![![-1825, 28, -39]]]
  g := ![![![-2, 7, 0], ![-5, -2, 7], ![90, -329, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-52, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-52, 1, 0]] 
 ![![127, 0, 0], ![75, 1, 0], ![90, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-52, 1, 0], ![0, -52, 1], ![13, -47, -51]]]
  hmulB := by decide  
  f := ![![![1873, -36, 0], ![4572, 0, 0]], ![![1093, -21, 0], ![2668, 0, 0]], ![![1374, -26, 0], ![3354, 1, 0]]]
  g := ![![![1, 0, 0], ![-75, 127, 0], ![-90, 0, 127]], ![![-1, 1, 0], ![30, -52, 1], ![64, -47, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![15, 1, 0]] ![![-2, 7, 0]]
  ![![127, 0, 0], ![32, 51, 1]] where
 M := ![![![-254, 889, 0]], ![![-30, 103, 7]]]
 hmul := by decide  
 g := ![![![![-34, -44, -1], ![127, 0, 0]]], ![![![-2, -2, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![32, 51, 1]] ![![127, 0, 0], ![-52, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-6604, 127, 0]], ![![4064, 6477, 127], ![-1651, -2667, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-52, 1, 0]]], ![![![32, 51, 1]], ![![-13, -21, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [65, 35, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 39, 120], [32, 91, 11], [0, 1]]
 g := ![![[122, 6, 16], [71, 10, 55], [99, 28], [112, 52], [124, 107], [93, 1], []], ![[41, 18, 64, 110], [83, 93, 126, 126], [50, 84], [3, 39], [34, 75], [64, 28], [46, 121]], ![[76, 82, 114, 117], [69, 91, 73, 65], [3, 13], [7, 80], [24, 28], [51, 80], [24, 121]]]
 h' := ![![[61, 39, 120], [101, 44, 4], [64, 18, 102], [39, 26, 40], [30, 109, 24], [112, 86, 99], [0, 0, 1], [0, 1]], ![[32, 91, 11], [76, 9, 11], [6, 76, 45], [80, 57, 79], [119, 35, 68], [44, 111, 72], [76, 130, 91], [61, 39, 120]], ![[0, 1], [20, 78, 116], [71, 37, 115], [129, 48, 12], [86, 118, 39], [104, 65, 91], [119, 1, 39], [32, 91, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 96], []]
 b := ![[], [109, 18, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [65, 35, 38, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6550, 24628, -3013]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50, 188, -23]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![74, -36, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![74, -36, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![74, 101, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![74, -36, 1], ![13, 27, -35], ![-455, 1658, -8]]]
  hmulB := by decide  
  f := ![![![-73, 36, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-74, -101, 137]], ![![0, -1, 1], ![19, 26, -35], ![1, 18, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [43, 134, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 136], [0, 1]]
 g := ![![[121, 93], [14], [136], [103, 130], [68], [9], [1]], ![[126, 44], [14], [136], [82, 7], [68], [9], [1]]]
 h' := ![![[3, 136], [115, 97], [13, 39], [92, 100], [60, 33], [92, 43], [94, 3], [0, 1]], ![[0, 1], [132, 40], [130, 98], [118, 37], [22, 104], [84, 94], [103, 134], [3, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95]]
 b := ![[], [100, 116]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [43, 134, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![147, -190, 89]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-47, -67, 89]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![35, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![35, 1, 0]] 
 ![![137, 0, 0], ![35, 1, 0], ![8, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![35, 1, 0], ![0, 35, 1], ![13, -47, 36]]]
  hmulB := by decide  
  f := ![![![1366, 39, 0], ![-5343, 0, 0]], ![![350, 10, 0], ![-1369, 0, 0]], ![![44, 1, 0], ![-172, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 137, 0], ![-8, 0, 137]], ![![0, 1, 0], ![-9, 35, 1], ![10, -47, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![74, -36, 1]] ![![137, 0, 0], ![35, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![4795, 137, 0]], ![![10138, -4932, 137], ![2603, -1233, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![35, 1, 0]]], ![![![74, -36, 1]], ![![19, -9, 0]]]]
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


lemma PB181I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB181I2 : PrimesBelowBoundCertificateInterval O 79 137 181 where
  m := 11
  g := ![3, 2, 2, 2, 2, 2, 1, 3, 3, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB181I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0]
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
    · exact ![83, 83, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![113, 113, 113]
    · exact ![127, 127, 127]
    · exact ![2248091]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
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
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N0, I83N1, I89N1, I97N1, I101N1, I103N1, I107N1, I113N0, I113N1, I113N2, I127N0, I127N1, I127N2, I137N1]
  Il := ![[I83N0, I83N1, I83N1], [I89N1], [I97N1], [I101N1], [I103N1], [I107N1], [], [I113N0, I113N1, I113N2], [I127N0, I127N1, I127N2], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
