
import IdealArithmetic.Examples.NF3_3_333617_1.RI3_3_333617_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [80, 5, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 52, 47], [47, 30, 36], [0, 1]]
 g := ![![[36, 78, 68], [80, 66, 40], [62, 10], [47, 65], [33, 72, 1], []], ![[31, 17, 44, 32], [56, 72, 9, 80], [77, 51], [71, 70], [21, 59, 68, 53], [11, 51]], ![[68, 48, 24, 17], [12, 53, 60, 36], [54, 30], [36, 9], [70, 39, 65, 68], [22, 51]]]
 h' := ![![[25, 52, 47], [74, 25, 63], [12, 10, 17], [65, 15, 50], [16, 51, 27], [0, 0, 1], [0, 1]], ![[47, 30, 36], [72, 45, 77], [77, 72, 67], [57, 58, 47], [50, 51, 53], [77, 42, 30], [25, 52, 47]], ![[0, 1], [71, 13, 26], [64, 1, 82], [63, 10, 69], [11, 64, 3], [34, 41, 52], [47, 30, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 74], []]
 b := ![[], [79, 78, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [80, 5, 11, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9545, -10375, -1992]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-115, -125, -24]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [60, 8, 77, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 10, 36], [71, 78, 53], [0, 1]]
 g := ![![[44, 50, 64], [72, 42], [10, 5], [76, 77, 34], [47, 12, 1], []], ![[31, 58, 75, 18], [16, 68], [27, 44], [24, 84, 66, 69], [36, 11, 32, 84], [74, 50]], ![[54, 30, 57, 72], [87, 10], [35, 8], [35, 73, 81, 88], [77, 67, 27, 49], [57, 50]]]
 h' := ![![[30, 10, 36], [46, 33, 8], [19, 80, 24], [68, 6, 70], [28, 61, 52], [0, 0, 1], [0, 1]], ![[71, 78, 53], [39, 68, 32], [51, 14, 35], [46, 37, 69], [50, 64, 22], [20, 34, 78], [30, 10, 36]], ![[0, 1], [49, 77, 49], [14, 84, 30], [44, 46, 39], [7, 53, 15], [19, 55, 10], [71, 78, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 61], []]
 b := ![[], [20, 76, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [60, 8, 77, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-107067, 17088, 89534]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1203, 192, 1006]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-179, -6, 4]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-179, -6, 4]] 
 ![![97, 0, 0], ![0, 97, 0], ![28, 47, 1]] where
  M :=![![![-179, -6, 4], ![220, 9, -6], ![-330, -62, 9]]]
  hmulB := by decide  
  f := ![![![-3, -2, 0]], ![![0, -3, -2]], ![![-2, -3, -1]]]
  g := ![![![-3, -2, 4], ![4, 3, -6], ![-6, -5, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [69, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 96], [0, 1]]
 g := ![![[], [], [], [], [8], [0, 1]], ![[], [], [], [], [8], [0, 96]]]
 h' := ![![[0, 96], [75], [50], [27], [30], [0, 28], [0, 1]], ![[0, 1], [75], [50], [27], [30], [0, 69], [0, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [0, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [69, 0, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4055, -167, 176]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9, -87, 176]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 2, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![3, 2, 0]] 
 ![![97, 0, 0], ![50, 1, 0], ![22, 0, 1]] where
  M :=![![![3, 2, 0], ![0, 3, 2], ![110, 94, 3]]]
  hmulB := by decide  
  f := ![![![179, 6, -4]], ![![90, 3, -2]], ![![44, 2, -1]]]
  g := ![![![-1, 2, 0], ![-2, 3, 2], ![-48, 94, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-179, -6, 4]] ![![3, 2, 0]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![33, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![33, 1, 0]] 
 ![![101, 0, 0], ![33, 1, 0], ![22, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![33, 1, 0], ![0, 33, 1], ![55, 47, 33]]]
  hmulB := by decide  
  f := ![![![1090, 33, 0], ![-3333, 0, 0]], ![![330, 10, 0], ![-1009, 0, 0]], ![![242, 7, 0], ![-740, 1, 0]]]
  g := ![![![1, 0, 0], ![-33, 101, 0], ![-22, 0, 101]], ![![0, 1, 0], ![-11, 33, 1], ![-22, 47, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-32, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-32, 1, 0]] 
 ![![101, 0, 0], ![69, 1, 0], ![87, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-32, 1, 0], ![0, -32, 1], ![55, 47, -32]]]
  hmulB := by decide  
  f := ![![![2433, -76, 0], ![7676, 0, 0]], ![![1633, -51, 0], ![5152, 0, 0]], ![![2059, -64, 0], ![6496, 1, 0]]]
  g := ![![![1, 0, 0], ![-69, 101, 0], ![-87, 0, 101]], ![![-1, 1, 0], ![21, -32, 1], ![-4, 47, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-1, 1, 0]] 
 ![![101, 0, 0], ![100, 1, 0], ![100, 0, 1]] where
  M :=![![![-1, 1, 0], ![0, -1, 1], ![55, 47, -1]]]
  hmulB := by decide  
  f := ![![![-46, 1, 1]], ![![-45, 1, 1]], ![![-45, 2, 1]]]
  g := ![![![-1, 1, 0], ![0, -1, 1], ![-45, 47, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![33, 1, 0]] ![![101, 0, 0], ![-32, 1, 0]]
  ![![-46, 1, 1]] where
 M := ![![![10201, 0, 0], ![-3232, 101, 0]], ![![3333, 101, 0], ![-1056, 1, 1]]]
 hmul := by decide  
 g := ![![![![-101, 101, 0]], ![![32, -33, 1]]], ![![![-33, 32, 1]], ![![11, -10, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-46, 1, 1]] ![![-1, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![101, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12, 9, -1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-12, 9, -1]] 
 ![![103, 0, 0], ![16, 1, 0], ![53, 0, 1]] where
  M :=![![![-12, 9, -1], ![-55, -59, 9], ![495, 368, -59]]]
  hmulB := by decide  
  f := ![![![-169, -163, -22]], ![![-38, -37, -5]], ![![-174, -170, -23]]]
  g := ![![![-1, 9, -1], ![4, -59, 9], ![-22, 368, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 6, -1]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![8, 6, -1]] 
 ![![103, 0, 0], ![71, 1, 0], ![6, 0, 1]] where
  M :=![![![8, 6, -1], ![-55, -39, 6], ![330, 227, -39]]]
  hmulB := by decide  
  f := ![![![-159, -7, 3]], ![![-108, -5, 2]], ![![-13, -2, 0]]]
  g := ![![![-4, 6, -1], ![26, -39, 6], ![-151, 227, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-12, 9, -1]] ![![-12, 9, -1]]
  ![![-846, -1007, 152]] where
 M := ![![![-846, -1007, 152]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-846, -1007, 152]] ![![8, 6, -1]]
  ![![103, 0, 0]] where
 M := ![![![98777, 68701, -11124]]]
 hmul := by decide  
 g := ![![![![959, 667, -108]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![10, -48, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![10, -48, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![10, 59, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![10, -48, 1], ![55, 57, -48], ![-2640, -2201, 57]]]
  hmulB := by decide  
  f := ![![![-9, 48, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -59, 107]], ![![0, -1, 1], ![5, 27, -48], ![-30, -52, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [50, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 106], [0, 1]]
 g := ![![[59, 36], [10, 53], [42], [34, 33], [19], [46, 1]], ![[3, 71], [94, 54], [42], [54, 74], [19], [92, 106]]]
 h' := ![![[46, 106], [35, 101], [77, 69], [12, 16], [40, 51], [54, 33], [0, 1]], ![[0, 1], [80, 6], [41, 38], [106, 91], [32, 56], [74, 74], [46, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [81, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [50, 61, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-218, 276, 235]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24, -127, 235]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![48, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![48, 1, 0]] 
 ![![107, 0, 0], ![48, 1, 0], ![50, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![48, 1, 0], ![0, 48, 1], ![55, 47, 48]]]
  hmulB := by decide  
  f := ![![![1105, 23, 0], ![-2461, 0, 0]], ![![432, 9, 0], ![-962, 0, 0]], ![![502, 10, 0], ![-1118, 1, 0]]]
  g := ![![![1, 0, 0], ![-48, 107, 0], ![-50, 0, 107]], ![![0, 1, 0], ![-22, 48, 1], ![-43, 47, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![10, -48, 1]] ![![107, 0, 0], ![48, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![5136, 107, 0]], ![![1070, -5136, 107], ![535, -2247, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![48, 1, 0]]], ![![![10, -48, 1]], ![![5, -21, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18, 34, 5]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![18, 34, 5]] 
 ![![109, 0, 0], ![0, 109, 0], ![69, 94, 1]] where
  M :=![![![18, 34, 5], ![275, 253, 34], ![1870, 1873, 253]]]
  hmulB := by decide  
  f := ![![![3, 7, -1]], ![![-55, -44, 7]], ![![-42, -31, 5]]]
  g := ![![![-3, -4, 5], ![-19, -27, 34], ![-143, -201, 253]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [88, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 108], [0, 1]]
 g := ![![[73, 83], [22], [10, 93], [59, 84], [104], [7, 1]], ![[0, 26], [22], [7, 16], [102, 25], [104], [14, 108]]]
 h' := ![![[7, 108], [90, 65], [101, 26], [40, 86], [31, 53], [38, 70], [0, 1]], ![[0, 1], [0, 44], [65, 83], [97, 23], [75, 56], [92, 39], [7, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [23, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [88, 102, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![198, 47, -54]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![36, 47, -54]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -7, 1]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-3, -7, 1]] 
 ![![109, 0, 0], ![15, 1, 0], ![102, 0, 1]] where
  M :=![![![-3, -7, 1], ![55, 44, -7], ![-385, -274, 44]]]
  hmulB := by decide  
  f := ![![![-18, -34, -5]], ![![-5, -7, -1]], ![![-34, -49, -7]]]
  g := ![![![0, -7, 1], ![1, 44, -7], ![-7, -274, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![18, 34, 5]] ![![-3, -7, 1]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [105, 39, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 83, 7], [75, 29, 106], [0, 1]]
 g := ![![[31, 43, 88], [58, 51], [54, 31], [98, 4], [11, 90, 30], [1]], ![[48, 103, 17, 2], [79, 13], [75, 62], [71, 91], [31, 83, 70, 72], [50, 111, 46, 4]], ![[54, 56, 90, 18], [70, 100], [106, 91], [111, 105], [4, 95, 24, 62], [4, 111, 33, 109]]]
 h' := ![![[22, 83, 7], [65, 27, 75], [77, 101, 86], [53, 43, 101], [88, 16, 111], [8, 74, 97], [0, 1]], ![[75, 29, 106], [17, 44, 104], [17, 39, 37], [35, 74, 66], [91, 11, 54], [87, 13, 54], [22, 83, 7]], ![[0, 1], [36, 42, 47], [43, 86, 103], [72, 109, 59], [38, 86, 61], [78, 26, 75], [75, 29, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 8], []]
 b := ![[], [12, 106, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [105, 39, 16, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![567486, 549406, 64071]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5022, 4862, 567]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [114, 59, 97, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 79, 14], [99, 47, 113], [0, 1]]
 g := ![![[24, 84, 16], [51, 118, 64], [58, 69, 107], [42, 11, 32], [22, 92, 11], [1]], ![[110, 30, 47, 126], [48, 13, 48, 66], [29, 33, 111, 20], [26, 3, 122, 118], [84, 73, 84, 92], [58, 38, 121, 77]], ![[90, 50, 101, 76], [21, 124, 121, 36], [120, 110, 48, 104], [125, 82, 71, 70], [22, 2, 34, 49], [123, 15, 53, 50]]]
 h' := ![![[58, 79, 14], [28, 113, 123], [119, 62, 8], [38, 86, 108], [32, 67, 64], [13, 68, 30], [0, 1]], ![[99, 47, 113], [78, 65, 124], [86, 16, 101], [40, 69, 57], [32, 19, 9], [32, 82, 76], [58, 79, 14]], ![[0, 1], [113, 76, 7], [13, 49, 18], [77, 99, 89], [20, 41, 54], [94, 104, 21], [99, 47, 113]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 107], []]
 b := ![[], [54, 21, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [114, 59, 97, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9144, -7239, 2413]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-72, -57, 19]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀



lemma PB129I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 128 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 128 (by omega)

def PB129I2 : PrimesBelowBoundCertificateInterval O 79 128 129 where
  m := 9
  g := ![1, 1, 2, 3, 3, 2, 2, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127]
  hP := PB129I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![2048383]
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
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
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
  β := ![I97N1, I101N0, I101N1, I101N2, I103N0, I103N1, I107N1, I109N1]
  Il := ![[], [], [I97N1], [I101N0, I101N1, I101N2], [I103N0, I103N0, I103N1], [I107N1], [I109N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
