
import IdealArithmetic.Examples.NF3_1_186151_1.RI3_1_186151_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1121, -427, -42]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-1121, -427, -42]] 
 ![![83, 0, 0], ![0, 83, 0], ![1, 24, 1]] where
  M :=![![![-1121, -427, -42], ![-11466, -4355, -427], ![-116571, -44345, -4355]]]
  hmulB := by decide  
  f := ![![![-370, -35, 7]], ![![1911, 169, -35]], ![![433, 39, -8]]]
  g := ![![![-13, 7, -42], ![-133, 71, -427], ![-1352, 725, -4355]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [61, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 82], [0, 1]]
 g := ![![[58, 49], [9, 1], [65], [68], [30, 48], [1]], ![[0, 34], [40, 82], [65], [68], [24, 35], [1]]]
 h' := ![![[31, 82], [32, 7], [11, 82], [18, 27], [79, 63], [22, 31], [0, 1]], ![[0, 1], [0, 76], [63, 1], [25, 56], [40, 20], [70, 52], [31, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [46, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [61, 52, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![607, 375, 26]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, -3, 26]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![370, 35, -7]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![370, 35, -7]] 
 ![![83, 0, 0], ![59, 1, 0], ![5, 0, 1]] where
  M :=![![![370, 35, -7], ![-1911, -169, 35], ![9555, 784, -169]]]
  hmulB := by decide  
  f := ![![![1121, 427, 42]], ![![935, 356, 35]], ![![1472, 560, 55]]]
  g := ![![![-20, 35, -7], ![95, -169, 35], ![-432, 784, -169]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-1121, -427, -42]] ![![370, 35, -7]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-75, -25, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-75, -25, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![14, 64, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-75, -25, 1], ![273, 2, -25], ![-6825, -1652, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -64, 89]], ![![-1, -1, 1], ![7, 18, -25], ![-77, -20, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [27, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 88], [0, 1]]
 g := ![![[18, 39], [32], [50], [1, 34], [43, 79], [1]], ![[21, 50], [32], [50], [31, 55], [8, 10], [1]]]
 h' := ![![[48, 88], [30, 67], [2, 11], [62, 36], [85, 37], [62, 48], [0, 1]], ![[0, 1], [42, 22], [85, 78], [10, 53], [81, 52], [52, 41], [48, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [72, 86]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [27, 41, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3289, 1455, 814]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-165, -569, 814]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![25, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![25, 1, 0]] 
 ![![89, 0, 0], ![25, 1, 0], ![87, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![25, 1, 0], ![0, 25, 1], ![273, 77, 25]]]
  hmulB := by decide  
  f := ![![![926, 37, 0], ![-3293, 0, 0]], ![![250, 10, 0], ![-889, 0, 0]], ![![908, 36, 0], ![-3229, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 89, 0], ![-87, 0, 89]], ![![0, 1, 0], ![-8, 25, 1], ![-43, 77, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-75, -25, 1]] ![![89, 0, 0], ![25, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![2225, 89, 0]], ![![-6675, -2225, 89], ![-1602, -623, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![25, 1, 0]]], ![![![-75, -25, 1]], ![![-18, -7, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [16, 65, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 18, 81], [69, 78, 16], [0, 1]]
 g := ![![[32, 81, 8], [32, 47], [6, 66], [94, 2], [49, 18], [1]], ![[35, 88, 61, 24], [12, 54], [28, 4], [8, 75], [74, 73], [7, 20, 96, 75]], ![[83, 87, 41, 89], [53, 93], [10, 11], [75, 35], [74, 49], [46, 10, 9, 22]]]
 h' := ![![[70, 18, 81], [22, 63, 28], [7, 89, 85], [54, 69, 39], [54, 62, 83], [81, 32, 42], [0, 1]], ![[69, 78, 16], [67, 61, 12], [29, 11, 65], [34, 35, 95], [29, 52, 50], [90, 82, 48], [70, 18, 81]], ![[0, 1], [69, 70, 57], [23, 94, 44], [59, 90, 60], [80, 80, 61], [10, 80, 7], [69, 78, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81, 54], []]
 b := ![[], [30, 95, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [16, 65, 55, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22601, -35987, -21340]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![233, -371, -220]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-55, -27, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-55, -27, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![46, 74, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-55, -27, 1], ![273, 22, -27], ![-7371, -1806, 22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-46, -74, 101]], ![![-1, -1, 1], ![15, 20, -27], ![-83, -34, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [48, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 100], [0, 1]]
 g := ![![[35, 37], [92], [6, 30], [100], [64], [37, 1]], ![[91, 64], [92], [5, 71], [100], [64], [74, 100]]]
 h' := ![![[37, 100], [51, 80], [15, 71], [73, 63], [5, 10], [42, 8], [0, 1]], ![[0, 1], [82, 21], [16, 30], [81, 38], [72, 91], [35, 93], [37, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [48, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [48, 64, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1525, 2061, 496]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-241, -343, 496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![27, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![27, 1, 0]] 
 ![![101, 0, 0], ![27, 1, 0], ![79, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![27, 1, 0], ![0, 27, 1], ![273, 77, 27]]]
  hmulB := by decide  
  f := ![![![352, 13, 0], ![-1313, 0, 0]], ![![54, 2, 0], ![-201, 0, 0]], ![![278, 10, 0], ![-1037, 1, 0]]]
  g := ![![![1, 0, 0], ![-27, 101, 0], ![-79, 0, 101]], ![![0, 1, 0], ![-8, 27, 1], ![-39, 77, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-55, -27, 1]] ![![101, 0, 0], ![27, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![2727, 101, 0]], ![![-5555, -2727, 101], ![-1212, -707, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![27, 1, 0]]], ![![![-55, -27, 1]], ![![-12, -7, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-99, -9, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-99, -9, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![4, 94, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-99, -9, 1], ![273, -22, -9], ![-2457, -420, -22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -94, 103]], ![![-1, -1, 1], ![3, 8, -9], ![-23, 16, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [56, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 102], [0, 1]]
 g := ![![[64, 46], [21, 91], [62, 63], [15], [8], [21, 1]], ![[0, 57], [78, 12], [46, 40], [15], [8], [42, 102]]]
 h' := ![![[21, 102], [60, 56], [30, 20], [17, 75], [62, 18], [60, 76], [0, 1]], ![[0, 1], [0, 47], [38, 83], [47, 28], [28, 85], [8, 27], [21, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [30, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [56, 82, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![602, 345, -4]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, 7, -4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![9, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![9, 1, 0]] 
 ![![103, 0, 0], ![9, 1, 0], ![22, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![9, 1, 0], ![0, 9, 1], ![273, 77, 9]]]
  hmulB := by decide  
  f := ![![![190, 21, 0], ![-2163, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![28, 3, 0], ![-318, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 103, 0], ![-22, 0, 103]], ![![0, 1, 0], ![-1, 9, 1], ![-6, 77, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-99, -9, 1]] ![![103, 0, 0], ![9, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![927, 103, 0]], ![![-10197, -927, 103], ![-618, -103, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![9, 1, 0]]], ![![![-99, -9, 1]], ![![-6, -1, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![44, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![44, 1, 0]] 
 ![![107, 0, 0], ![44, 1, 0], ![97, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![44, 1, 0], ![0, 44, 1], ![273, 77, 44]]]
  hmulB := by decide  
  f := ![![![1585, 36, 0], ![-3852, 0, 0]], ![![660, 15, 0], ![-1604, 0, 0]], ![![1427, 32, 0], ![-3468, 1, 0]]]
  g := ![![![1, 0, 0], ![-44, 107, 0], ![-97, 0, 107]], ![![0, 1, 0], ![-19, 44, 1], ![-69, 77, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-26, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-26, 1, 0]] 
 ![![107, 0, 0], ![81, 1, 0], ![73, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-26, 1, 0], ![0, -26, 1], ![273, 77, -26]]]
  hmulB := by decide  
  f := ![![![2133, -82, 0], ![8774, 0, 0]], ![![1639, -63, 0], ![6742, 0, 0]], ![![1463, -56, 0], ![6018, 1, 0]]]
  g := ![![![1, 0, 0], ![-81, 107, 0], ![-73, 0, 107]], ![![-1, 1, 0], ![19, -26, 1], ![-38, 77, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-18, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-18, 1, 0]] 
 ![![107, 0, 0], ![89, 1, 0], ![104, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-18, 1, 0], ![0, -18, 1], ![273, 77, -18]]]
  hmulB := by decide  
  f := ![![![145, -8, 0], ![856, 0, 0]], ![![127, -7, 0], ![750, 0, 0]], ![![148, -8, 0], ![874, 1, 0]]]
  g := ![![![1, 0, 0], ![-89, 107, 0], ![-104, 0, 107]], ![![-1, 1, 0], ![14, -18, 1], ![-44, 77, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![44, 1, 0]] ![![107, 0, 0], ![-26, 1, 0]]
  ![![107, 0, 0], ![-74, 18, 1]] where
 M := ![![![11449, 0, 0], ![-2782, 107, 0]], ![![4708, 107, 0], ![-1144, 18, 1]]]
 hmul := by decide  
 g := ![![![![107, 0, 0], ![0, 0, 0]], ![![48, -17, -1], ![107, 0, 0]]], ![![![44, 1, 0], ![0, 0, 0]], ![![64, -18, -1], ![108, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-74, 18, 1]] ![![107, 0, 0], ![-18, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-1926, 107, 0]], ![![-7918, 1926, 107], ![1605, -321, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-18, 1, 0]]], ![![![-74, 18, 1]], ![![15, -3, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![46, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![46, 1, 0]] 
 ![![109, 0, 0], ![46, 1, 0], ![64, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![46, 1, 0], ![0, 46, 1], ![273, 77, 46]]]
  hmulB := by decide  
  f := ![![![1657, 36, 0], ![-3924, 0, 0]], ![![690, 15, 0], ![-1634, 0, 0]], ![![940, 20, 0], ![-2226, 1, 0]]]
  g := ![![![1, 0, 0], ![-46, 109, 0], ![-64, 0, 109]], ![![0, 1, 0], ![-20, 46, 1], ![-57, 77, 46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-27, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-27, 1, 0]] 
 ![![109, 0, 0], ![82, 1, 0], ![34, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-27, 1, 0], ![0, -27, 1], ![273, 77, -27]]]
  hmulB := by decide  
  f := ![![![2890, -107, 0], ![11663, 0, 0]], ![![2188, -81, 0], ![8830, 0, 0]], ![![952, -35, 0], ![3842, 1, 0]]]
  g := ![![![1, 0, 0], ![-82, 109, 0], ![-34, 0, 109]], ![![-1, 1, 0], ![20, -27, 1], ![-47, 77, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-19, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-19, 1, 0]] 
 ![![109, 0, 0], ![90, 1, 0], ![75, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-19, 1, 0], ![0, -19, 1], ![273, 77, -19]]]
  hmulB := by decide  
  f := ![![![590, -31, 0], ![3379, 0, 0]], ![![476, -25, 0], ![2726, 0, 0]], ![![384, -20, 0], ![2199, 1, 0]]]
  g := ![![![1, 0, 0], ![-90, 109, 0], ![-75, 0, 109]], ![![-1, 1, 0], ![15, -19, 1], ![-48, 77, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![46, 1, 0]] ![![109, 0, 0], ![-27, 1, 0]]
  ![![109, 0, 0], ![-43, 19, 1]] where
 M := ![![![11881, 0, 0], ![-2943, 109, 0]], ![![5014, 109, 0], ![-1242, 19, 1]]]
 hmul := by decide  
 g := ![![![![109, 0, 0], ![0, 0, 0]], ![![16, -18, -1], ![109, 0, 0]]], ![![![46, 1, 0], ![0, 0, 0]], ![![32, -19, -1], ![110, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-43, 19, 1]] ![![109, 0, 0], ![-19, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-2071, 109, 0]], ![![-4687, 2071, 109], ![1090, -327, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-19, 1, 0]]], ![![![-43, 19, 1]], ![![10, -3, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![121, 48, 5]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![121, 48, 5]] 
 ![![113, 0, 0], ![0, 113, 0], ![92, 100, 1]] where
  M :=![![![121, 48, 5], ![1365, 506, 48], ![13104, 5061, 506]]]
  hmulB := by decide  
  f := ![![![116, 9, -2]], ![![-546, -38, 9]], ![![-367, -25, 6]]]
  g := ![![![-3, -4, 5], ![-27, -38, 48], ![-296, -403, 506]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [110, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 112], [0, 1]]
 g := ![![[78, 81], [32], [25], [104], [30, 82], [8, 1]], ![[48, 32], [32], [25], [104], [8, 31], [16, 112]]]
 h' := ![![[8, 112], [107, 104], [89, 22], [50, 5], [90, 45], [24, 67], [0, 1]], ![[0, 1], [35, 9], [39, 91], [90, 108], [111, 68], [108, 46], [8, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [12, 110]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [110, 105, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10590, 5232, 545]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-350, -436, 545]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-116, -9, 2]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-116, -9, 2]] 
 ![![113, 0, 0], ![13, 1, 0], ![57, 0, 1]] where
  M :=![![![-116, -9, 2], ![546, 38, -9], ![-2457, -147, 38]]]
  hmulB := by decide  
  f := ![![![-121, -48, -5]], ![![-26, -10, -1]], ![![-177, -69, -7]]]
  g := ![![![-1, -9, 2], ![5, 38, -9], ![-24, -147, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![121, 48, 5]] ![![-116, -9, 2]]
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


lemma PB123I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 122 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 122 (by omega)

def PB123I2 : PrimesBelowBoundCertificateInterval O 79 122 123 where
  m := 8
  g := ![2, 2, 1, 2, 2, 3, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB123I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![109, 109, 109]
    · exact ![12769, 113]
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
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
  β := ![I83N1, I89N1, I101N1, I103N1, I107N0, I107N1, I107N2, I109N0, I109N1, I109N2, I113N1]
  Il := ![[I83N1], [I89N1], [], [I101N1], [I103N1], [I107N0, I107N1, I107N2], [I109N0, I109N1, I109N2], [I113N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
