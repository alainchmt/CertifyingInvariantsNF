
import IdealArithmetic.Examples.NF3_3_260820_1.RI3_3_260820_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-72, 15, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-72, 15, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![11, 15, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-72, 15, 1], ![82, -24, 15], ![1230, 802, -24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -15, 83]], ![![-1, 0, 1], ![-1, -3, 15], ![18, 14, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [50, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 82], [0, 1]]
 g := ![![[27, 81], [37, 37], [23], [75], [18, 69], [1]], ![[71, 2], [53, 46], [23], [75], [77, 14], [1]]]
 h' := ![![[61, 82], [59, 9], [73, 28], [71, 40], [13, 65], [33, 61], [0, 1]], ![[0, 1], [27, 74], [38, 55], [21, 43], [77, 18], [19, 22], [61, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [80, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [50, 22, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![214, 156, 27]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, -3, 27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-15, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-15, 1, 0]] 
 ![![83, 0, 0], ![68, 1, 0], ![24, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-15, 1, 0], ![0, -15, 1], ![82, 48, -15]]]
  hmulB := by decide  
  f := ![![![1141, -76, 0], ![6308, 0, 0]], ![![946, -63, 0], ![5230, 0, 0]], ![![348, -23, 0], ![1924, 1, 0]]]
  g := ![![![1, 0, 0], ![-68, 83, 0], ![-24, 0, 83]], ![![-1, 1, 0], ![12, -15, 1], ![-34, 48, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-72, 15, 1]] ![![83, 0, 0], ![-15, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1245, 83, 0]], ![![-5976, 1245, 83], ![1162, -249, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-15, 1, 0]]], ![![![-72, 15, 1]], ![![14, -3, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![7, 1, 0]] 
 ![![89, 0, 0], ![7, 1, 0], ![40, 0, 1]] where
  M :=![![![7, 1, 0], ![0, 7, 1], ![82, 48, 7]]]
  hmulB := by decide  
  f := ![![![1, -7, 1]], ![![1, 0, 0]], ![![-6, -6, 1]]]
  g := ![![![0, 1, 0], ![-1, 7, 1], ![-6, 48, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85, 61, 8]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![85, 61, 8]] 
 ![![89, 0, 0], ![25, 1, 0], ![87, 0, 1]] where
  M :=![![![85, 61, 8], ![656, 469, 61], ![5002, 3584, 469]]]
  hmulB := by decide  
  f := ![![![-1337, -63, 31]], ![![-347, -16, 8]], ![![-1365, -67, 32]]]
  g := ![![![-24, 61, 8], ![-184, 469, 61], ![-1409, 3584, 469]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-273, -18, 7]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![-273, -18, 7]] 
 ![![89, 0, 0], ![57, 1, 0], ![44, 0, 1]] where
  M :=![![![-273, -18, 7], ![574, 63, -18], ![-1476, -290, 63]]]
  hmulB := by decide  
  f := ![![![1251, 896, 117]], ![![909, 651, 85]], ![![1444, 1034, 135]]]
  g := ![![![5, -18, 7], ![-25, 63, -18], ![138, -290, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![7, 1, 0]] ![![85, 61, 8]]
  ![![1251, 896, 117]] where
 M := ![![![1251, 896, 117]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![1251, 896, 117]] ![![-273, -18, 7]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-26, -33, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-26, -33, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![71, 64, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-26, -33, 1], ![82, 22, -33], ![-2706, -1502, 22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -64, 97]], ![![-1, -1, 1], ![25, 22, -33], ![-44, -30, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [80, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 96], [0, 1]]
 g := ![![[30, 85], [43], [9], [86], [11], [25, 1]], ![[21, 12], [43], [9], [86], [11], [50, 96]]]
 h' := ![![[25, 96], [61, 52], [3, 72], [23, 3], [4, 59], [37, 60], [0, 1]], ![[0, 1], [3, 45], [57, 25], [1, 94], [24, 38], [82, 37], [25, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [78, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [80, 72, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-596, -70, 105]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-83, -70, 105]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![33, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![33, 1, 0]] 
 ![![97, 0, 0], ![33, 1, 0], ![75, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![33, 1, 0], ![0, 33, 1], ![82, 48, 33]]]
  hmulB := by decide  
  f := ![![![1123, 34, 0], ![-3298, 0, 0]], ![![363, 11, 0], ![-1066, 0, 0]], ![![837, 25, 0], ![-2458, 1, 0]]]
  g := ![![![1, 0, 0], ![-33, 97, 0], ![-75, 0, 97]], ![![0, 1, 0], ![-12, 33, 1], ![-41, 48, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-26, -33, 1]] ![![97, 0, 0], ![33, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![3201, 97, 0]], ![![-2522, -3201, 97], ![-776, -1067, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![33, 1, 0]]], ![![![-26, -33, 1]], ![![-8, -11, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-27, -18, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-27, -18, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![74, 83, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-27, -18, 1], ![82, 21, -18], ![-1476, -782, 21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-74, -83, 101]], ![![-1, -1, 1], ![14, 15, -18], ![-30, -25, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [9, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 100], [0, 1]]
 g := ![![[34, 45], [56], [], [], [], [98, 1]], ![[0, 56], [56], [], [], [], [95, 100]]]
 h' := ![![[98, 100], [1, 34], [0, 37], [80], [22], [27], [0, 1]], ![[0, 1], [0, 67], [91, 64], [80], [22], [27], [98, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [45, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [9, 3, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-479, 455, 418]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-311, -339, 418]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![18, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![18, 1, 0]] 
 ![![101, 0, 0], ![18, 1, 0], ![80, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![18, 1, 0], ![0, 18, 1], ![82, 48, 18]]]
  hmulB := by decide  
  f := ![![![955, 53, 0], ![-5353, 0, 0]], ![![162, 9, 0], ![-908, 0, 0]], ![![760, 42, 0], ![-4260, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 101, 0], ![-80, 0, 101]], ![![0, 1, 0], ![-4, 18, 1], ![-22, 48, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-27, -18, 1]] ![![101, 0, 0], ![18, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![1818, 101, 0]], ![![-2727, -1818, 101], ![-404, -303, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![18, 1, 0]]], ![![![-27, -18, 1]], ![![-4, -3, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-30, 11, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-30, 11, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![73, 11, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-30, 11, 1], ![82, 18, 11], ![902, 610, 18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-73, -11, 103]], ![![-1, 0, 1], ![-7, -1, 11], ![-4, 4, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [67, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 102], [0, 1]]
 g := ![![[1, 18], [17, 72], [0, 59], [9], [49], [36, 1]], ![[31, 85], [34, 31], [64, 44], [9], [49], [72, 102]]]
 h' := ![![[36, 102], [97, 11], [0, 22], [79, 70], [8, 100], [60, 96], [0, 1]], ![[0, 1], [81, 92], [71, 81], [24, 33], [3, 3], [14, 7], [36, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [85, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [67, 67, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![231, 111, -18]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15, 3, -18]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-11, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-11, 1, 0]] 
 ![![103, 0, 0], ![92, 1, 0], ![85, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-11, 1, 0], ![0, -11, 1], ![82, 48, -11]]]
  hmulB := by decide  
  f := ![![![892, -81, 0], ![8343, 0, 0]], ![![782, -71, 0], ![7314, 0, 0]], ![![728, -66, 0], ![6809, 1, 0]]]
  g := ![![![1, 0, 0], ![-92, 103, 0], ![-85, 0, 103]], ![![-1, 1, 0], ![9, -11, 1], ![-33, 48, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-30, 11, 1]] ![![103, 0, 0], ![-11, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-1133, 103, 0]], ![![-3090, 1133, 103], ![412, -103, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-11, 1, 0]]], ![![![-30, 11, 1]], ![![4, -1, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 2, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![3, 2, 0]] 
 ![![107, 0, 0], ![55, 1, 0], ![78, 0, 1]] where
  M :=![![![3, 2, 0], ![0, 3, 2], ![164, 96, 3]]]
  hmulB := by decide  
  f := ![![![-183, -6, 4]], ![![-91, -3, 2]], ![![-138, -4, 3]]]
  g := ![![![-1, 2, 0], ![-3, 3, 2], ![-50, 96, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45, -31, -4]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-45, -31, -4]] 
 ![![107, 0, 0], ![64, 1, 0], ![77, 0, 1]] where
  M :=![![![-45, -31, -4], ![-328, -237, -31], ![-2542, -1816, -237]]]
  hmulB := by decide  
  f := ![![![127, 83, -13]], ![![66, 45, -7]], ![![155, 87, -14]]]
  g := ![![![21, -31, -4], ![161, -237, -31], ![1233, -1816, -237]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, -5, -1]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![97, -5, -1]] 
 ![![107, 0, 0], ![95, 1, 0], ![70, 0, 1]] where
  M :=![![![97, -5, -1], ![-82, 49, -5], ![-410, -322, 49]]]
  hmulB := by decide  
  f := ![![![-791, -567, -74]], ![![-759, -544, -71]], ![![-952, -682, -89]]]
  g := ![![![6, -5, -1], ![-41, 49, -5], ![250, -322, 49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![3, 2, 0]] ![![-45, -31, -4]]
  ![![-791, -567, -74]] where
 M := ![![![-791, -567, -74]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-791, -567, -74]] ![![97, -5, -1]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91, -67, -9]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-91, -67, -9]] 
 ![![109, 0, 0], ![0, 109, 0], ![107, 68, 1]] where
  M :=![![![-91, -67, -9], ![-738, -523, -67], ![-5494, -3954, -523]]]
  hmulB := by decide  
  f := ![![![79, 5, -2]], ![![-164, -17, 5]], ![![-21, -5, 1]]]
  g := ![![![8, 5, -9], ![59, 37, -67], ![463, 290, -523]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [80, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 108], [0, 1]]
 g := ![![[70, 15], [78], [93, 104], [97, 49], [66], [68, 1]], ![[0, 94], [78], [80, 5], [50, 60], [66], [27, 108]]]
 h' := ![![[68, 108], [103, 61], [81, 80], [88, 39], [52, 102], [10, 75], [0, 1]], ![[0, 1], [0, 48], [71, 29], [15, 70], [12, 7], [96, 34], [68, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [100, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [80, 41, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3238, 2723, 452]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-414, -257, 452]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 5, -2]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![79, 5, -2]] 
 ![![109, 0, 0], ![41, 1, 0], ![63, 0, 1]] where
  M :=![![![79, 5, -2], ![-164, -17, 5], ![410, 76, -17]]]
  hmulB := by decide  
  f := ![![![-91, -67, -9]], ![![-41, -30, -4]], ![![-103, -75, -10]]]
  g := ![![![0, 5, -2], ![2, -17, 5], ![-15, 76, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-91, -67, -9]] ![![79, 5, -2]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [41, 93, 99, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 72, 24], [11, 40, 89], [0, 1]]
 g := ![![[33, 77, 95], [104, 85], [21, 1], [82, 9], [47, 27, 83], [1]], ![[84, 89, 68, 38], [99, 91], [112, 8], [19, 85], [22, 15, 50, 40], [84, 109, 83, 38]], ![[62, 40, 59, 34], [110, 9], [66, 31], [78, 97], [33, 0, 36, 27], [109, 73, 110, 75]]]
 h' := ![![[3, 72, 24], [99, 97, 78], [71, 44, 57], [64, 53, 112], [107, 45, 110], [72, 20, 14], [0, 1]], ![[11, 40, 89], [53, 97, 24], [48, 104, 59], [81, 0, 102], [42, 41, 56], [86, 59, 23], [3, 72, 24]], ![[0, 1], [23, 32, 11], [37, 78, 110], [101, 60, 12], [94, 27, 60], [26, 34, 76], [11, 40, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96, 77], []]
 b := ![[], [82, 20, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [41, 93, 99, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16272, -8136, 2712]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-144, -72, 24]
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



lemma PB114I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 113 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 113 (by omega)

def PB114I2 : PrimesBelowBoundCertificateInterval O 79 113 114 where
  m := 8
  g := ![2, 3, 2, 2, 2, 3, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB114I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
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
    · exact ![89, 89, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![1442897]
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
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
  β := ![I83N1, I89N0, I89N1, I89N2, I97N1, I101N1, I103N1, I107N0, I107N1, I107N2, I109N1]
  Il := ![[I83N1], [I89N0, I89N1, I89N2], [I97N1], [I101N1], [I103N1], [I107N0, I107N1, I107N2], [I109N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
