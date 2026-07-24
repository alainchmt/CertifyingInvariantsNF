
import IdealArithmetic.Examples.NF3_1_143468_1.RI3_1_143468_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![15, 19, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![15, 19, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![15, 19, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![15, 19, 1], ![-115, 48, 20], ![-2300, 545, 68]]]
  hmulB := by decide  
  f := ![![![-14, -19, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -19, 83]], ![![0, 0, 1], ![-5, -4, 20], ![-40, -9, 68]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [38, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 82], [0, 1]]
 g := ![![[65, 59], [62, 78], [11], [78], [6, 68], [1]], ![[0, 24], [45, 5], [11], [78], [38, 15], [1]]]
 h' := ![![[20, 82], [51, 68], [7, 59], [50, 54], [21, 59], [45, 20], [0, 1]], ![[0, 1], [0, 15], [25, 24], [51, 29], [39, 24], [30, 63], [20, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [63, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [38, 63, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-307, -79, -26]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1, 5, -26]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-20, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-20, 1, 0]] 
 ![![83, 0, 0], ![63, 1, 0], ![15, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-20, 1, 0], ![0, -20, 1], ![-115, 33, -19]]]
  hmulB := by decide  
  f := ![![![1281, -64, 0], ![5312, 0, 0]], ![![981, -49, 0], ![4068, 0, 0]], ![![245, -12, 0], ![1016, 1, 0]]]
  g := ![![![1, 0, 0], ![-63, 83, 0], ![-15, 0, 83]], ![![-1, 1, 0], ![15, -20, 1], ![-23, 33, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![15, 19, 1]] ![![83, 0, 0], ![-20, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1660, 83, 0]], ![![1245, 1577, 83], ![-415, -332, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-20, 1, 0]]], ![![![15, 19, 1]], ![![-5, -4, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-143, -15, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-143, -15, 1]] 
 ![![89, 0, 0], ![3, 1, 0], ![80, 0, 1]] where
  M :=![![![-143, -15, 1], ![-115, -110, -14], ![1610, -577, -124]]]
  hmulB := by decide  
  f := ![![![5562, -2437, 320]], ![![-226, 99, -13]], ![![7735, -3389, 445]]]
  g := ![![![-2, -15, 1], ![15, -110, -14], ![149, -577, -124]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![142, -5, -4]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![142, -5, -4]] 
 ![![89, 0, 0], ![82, 1, 0], ![40, 0, 1]] where
  M :=![![![142, -5, -4], ![460, 10, -9], ![1035, 163, 1]]]
  hmulB := by decide  
  f := ![![![1477, -647, 85]], ![![1251, -548, 72]], ![![1390, -609, 80]]]
  g := ![![![8, -5, -4], ![0, 10, -9], ![-139, 163, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-143, -15, 1]] ![![-143, -15, 1]]
  ![![23784, 3218, -57]] where
 M := ![![![23784, 3218, -57]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI89N1 : IdealMulLeCertificate' Table 
  ![![23784, 3218, -57]] ![![142, -5, -4]]
  ![![89, 0, 0]] where
 M := ![![![4798613, -96031, -124155]]]
 hmul := by decide  
 g := ![![![![53917, -1079, -1395]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 5, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-3, 5, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![94, 5, 1]] where
  M :=![![![-3, 5, 1], ![-115, 30, 6], ![-690, 83, 36]]]
  hmulB := by decide  
  f := ![![![6, -1, 0]], ![![0, 6, -1]], ![![7, -1, 0]]]
  g := ![![![-1, 0, 1], ![-7, 0, 6], ![-42, -1, 36]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [71, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 96], [0, 1]]
 g := ![![[30, 96], [66], [89], [70], [18], [4, 1]], ![[26, 1], [66], [89], [70], [18], [8, 96]]]
 h' := ![![[4, 96], [14, 22], [74, 39], [31, 34], [32, 78], [7, 42], [0, 1]], ![[0, 1], [5, 75], [36, 58], [70, 63], [53, 19], [78, 55], [4, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [55, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [71, 93, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![324, -1316, 571]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-550, -43, 571]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-6, 1, 0]] 
 ![![97, 0, 0], ![91, 1, 0], ![61, 0, 1]] where
  M :=![![![-6, 1, 0], ![0, -6, 1], ![-115, 33, -5]]]
  hmulB := by decide  
  f := ![![![3, -5, -1]], ![![4, -5, -1]], ![![9, -4, -1]]]
  g := ![![![-1, 1, 0], ![5, -6, 1], ![-29, 33, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-3, 5, 1]] ![![-6, 1, 0]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-63, 30, -4]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-63, 30, -4]] 
 ![![101, 0, 0], ![0, 101, 0], ![41, 43, 1]] where
  M :=![![![-63, 30, -4], ![460, -195, 26], ![-2990, 1318, -169]]]
  hmulB := by decide  
  f := ![![![13, 2, 0]], ![![0, 13, 2]], ![![3, 7, 1]]]
  g := ![![![1, 2, -4], ![-6, -13, 26], ![39, 85, -169]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [100, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 100], [0, 1]]
 g := ![![[82, 100], [65], [23, 79], [16], [47], [82, 1]], ![[0, 1], [65], [37, 22], [16], [47], [63, 100]]]
 h' := ![![[82, 100], [89, 10], [23, 60], [32, 68], [4, 97], [82, 59], [0, 1]], ![[0, 1], [0, 91], [95, 41], [53, 33], [80, 4], [72, 42], [82, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [73, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [100, 19, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3095, -257, 142]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-27, -63, 142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 2, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![13, 2, 0]] 
 ![![101, 0, 0], ![57, 1, 0], ![84, 0, 1]] where
  M :=![![![13, 2, 0], ![0, 13, 2], ![-230, 66, 15]]]
  hmulB := by decide  
  f := ![![![-63, 30, -4]], ![![-31, 15, -2]], ![![-82, 38, -5]]]
  g := ![![![-1, 2, 0], ![-9, 13, 2], ![-52, 66, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-63, 30, -4]] ![![13, 2, 0]]
  ![![101, 0, 0]] where
 M := ![![![101, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-106, 47, -6]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-106, 47, -6]] 
 ![![103, 0, 0], ![0, 103, 0], ![52, 78, 1]] where
  M :=![![![-106, 47, -6], ![690, -304, 41], ![-4715, 2043, -263]]]
  hmulB := by decide  
  f := ![![![37, -1, -1]], ![![115, 4, -2]], ![![108, 3, -2]]]
  g := ![![![2, 5, -6], ![-14, -34, 41], ![87, 219, -263]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [102, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 102], [0, 1]]
 g := ![![[9, 56], [45, 23], [66, 14], [93], [29], [9, 1]], ![[101, 47], [46, 80], [89, 89], [93], [29], [18, 102]]]
 h' := ![![[9, 102], [45, 46], [66, 69], [39, 23], [7, 89], [9, 82], [0, 1]], ![[0, 1], [47, 57], [69, 34], [40, 80], [87, 14], [26, 21], [9, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [51, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [102, 94, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-148, -840, 13]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, -18, 13]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, 1, 1]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-37, 1, 1]] 
 ![![103, 0, 0], ![24, 1, 0], ![42, 0, 1]] where
  M :=![![![-37, 1, 1], ![-115, -4, 2], ![-230, -49, -2]]]
  hmulB := by decide  
  f := ![![![106, -47, 6]], ![![18, -8, 1]], ![![89, -39, 5]]]
  g := ![![![-1, 1, 1], ![-1, -4, 2], ![10, -49, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-106, 47, -6]] ![![-37, 1, 1]]
  ![![103, 0, 0]] where
 M := ![![![-103, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![43, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![43, 1, 0]] 
 ![![107, 0, 0], ![43, 1, 0], ![77, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![43, 1, 0], ![0, 43, 1], ![-115, 33, 44]]]
  hmulB := by decide  
  f := ![![![130, 3, 0], ![-321, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![104, 2, 0], ![-257, 1, 0]]]
  g := ![![![1, 0, 0], ![-43, 107, 0], ![-77, 0, 107]], ![![0, 1, 0], ![-18, 43, 1], ![-46, 33, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-26, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-26, 1, 0]] 
 ![![107, 0, 0], ![81, 1, 0], ![73, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-26, 1, 0], ![0, -26, 1], ![-115, 33, -25]]]
  hmulB := by decide  
  f := ![![![2133, -82, 0], ![8774, 0, 0]], ![![1639, -63, 0], ![6742, 0, 0]], ![![1463, -56, 0], ![6018, 1, 0]]]
  g := ![![![1, 0, 0], ![-81, 107, 0], ![-73, 0, 107]], ![![-1, 1, 0], ![19, -26, 1], ![-9, 33, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, -6, -1]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![4, -6, -1]] 
 ![![107, 0, 0], ![89, 1, 0], ![104, 0, 1]] where
  M :=![![![4, -6, -1], ![115, -29, -7], ![805, -116, -36]]]
  hmulB := by decide  
  f := ![![![-232, 100, -13]], ![![-179, 77, -10]], ![![-319, 138, -18]]]
  g := ![![![6, -6, -1], ![32, -29, -7], ![139, -116, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![43, 1, 0]] ![![107, 0, 0], ![-26, 1, 0]]
  ![![232, -100, 13]] where
 M := ![![![11449, 0, 0], ![-2782, 107, 0]], ![![4601, 107, 0], ![-1118, 17, 1]]]
 hmul := by decide  
 g := ![![![![-428, 642, 107]], ![![-11, -127, -19]]], ![![![-287, 287, 50]], ![![16, -57, -9]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![232, -100, 13]] ![![4, -6, -1]]
  ![![107, 0, 0]] where
 M := ![![![-107, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB108I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 107 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 107 (by omega)

def PB108I2 : PrimesBelowBoundCertificateInterval O 79 107 108 where
  m := 6
  g := ![2, 3, 2, 2, 2, 3]
  P := ![83, 89, 97, 101, 103, 107]
  hP := PB108I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
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
      exact NI107N2
  β := ![I83N1, I89N0, I89N1, I97N1, I101N1, I103N1, I107N0, I107N1, I107N2]
  Il := ![[I83N1], [I89N0, I89N0, I89N1], [I97N1], [I101N1], [I103N1], [I107N0, I107N1, I107N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
