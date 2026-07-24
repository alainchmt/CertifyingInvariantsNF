
import IdealArithmetic.Examples.NF3_1_894348_3.RI3_1_894348_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 5, -3]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-3, 5, -3]] 
 ![![83, 0, 0], ![0, 83, 0], ![1, 26, 1]] where
  M :=![![![-3, 5, -3], ![-546, -3, 35], ![910, -78, -3]]]
  hmulB := by decide  
  f := ![![![33, 3, 2]], ![![364, 33, 21]], ![![121, 11, 7]]]
  g := ![![![0, 1, -3], ![-7, -11, 35], ![11, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [75, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 82], [0, 1]]
 g := ![![[54, 31], [80, 49], [3], [28], [39, 40], [1]], ![[0, 52], [0, 34], [3], [28], [55, 43], [1]]]
 h' := ![![[17, 82], [59, 60], [47, 7], [43, 13], [63, 51], [8, 17], [0, 1]], ![[0, 1], [0, 23], [0, 76], [15, 70], [17, 32], [48, 66], [17, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [6, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [75, 66, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![439, -40, -59]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, 18, -59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, 3, 2]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![33, 3, 2]] 
 ![![83, 0, 0], ![67, 1, 0], ![82, 0, 1]] where
  M :=![![![33, 3, 2], ![364, 33, 21], ![546, 52, 33]]]
  hmulB := by decide  
  f := ![![![-3, 5, -3]], ![![-9, 4, -2]], ![![8, 4, -3]]]
  g := ![![![-4, 3, 2], ![-43, 33, 21], ![-68, 52, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-3, 5, -3]] ![![33, 3, 2]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-14, -40, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-14, -40, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![75, 49, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-14, -40, 1], ![182, -14, -280], ![-7280, 26, -14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-75, -49, 89]], ![![-1, -1, 1], ![238, 154, -280], ![-70, 8, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [46, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 88], [0, 1]]
 g := ![![[50, 1], [5], [84], [0, 67], [32, 18], [1]], ![[64, 88], [5], [84], [48, 22], [17, 71], [1]]]
 h' := ![![[14, 88], [71, 88], [52, 19], [0, 23], [41, 45], [43, 14], [0, 1]], ![[0, 1], [57, 1], [51, 70], [55, 66], [48, 44], [61, 75], [14, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [16, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [46, 75, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2212, 88, 247]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-233, -135, 247]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![13, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![13, 1, 0]] 
 ![![89, 0, 0], ![13, 1, 0], ![14, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![13, 1, 0], ![0, 13, 7], ![182, 0, 13]]]
  hmulB := by decide  
  f := ![![![521, 40, 0], ![-3560, 0, 0]], ![![65, 5, 0], ![-444, 0, 0]], ![![58, -3, -4], ![-396, 51, 0]]]
  g := ![![![1, 0, 0], ![-13, 89, 0], ![-14, 0, 89]], ![![0, 1, 0], ![-3, 13, 7], ![0, 0, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-14, -40, 1]] ![![89, 0, 0], ![13, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![1157, 89, 0]], ![![-1246, -3560, 89], ![0, -534, -267]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![13, 1, 0]]], ![![![-14, -40, 1]], ![![0, -6, -3]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [40, 30, 95, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 34, 58], [73, 62, 39], [0, 1]]
 g := ![![[43, 38, 31], [64, 73], [14, 47], [3, 64], [82, 4], [1]], ![[17, 78, 39, 14], [55, 8], [73, 1], [62, 18], [14, 22], [13, 45, 32, 45]], ![[71, 35, 25, 17], [89, 12], [75, 72], [64, 89], [36, 61], [58, 74, 61, 52]]]
 h' := ![![[26, 34, 58], [15, 59, 82], [76, 15, 49], [65, 29, 12], [66, 71, 8], [57, 67, 2], [0, 1]], ![[73, 62, 39], [78, 78, 67], [85, 44, 28], [17, 84, 1], [84, 2, 55], [81, 26, 33], [26, 34, 58]], ![[0, 1], [37, 57, 45], [69, 38, 20], [81, 81, 84], [33, 24, 34], [55, 4, 62], [73, 62, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 64], []]
 b := ![[], [2, 4, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [40, 30, 95, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![156946, -2910, -291]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1618, -30, -3]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-34, 23, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-34, 23, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![67, 23, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-34, 23, 1], ![182, -34, 161], ![4186, 26, -34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-67, -23, 101]], ![![-1, 0, 1], ![-105, -37, 161], ![64, 8, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [47, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 100], [0, 1]]
 g := ![![[12, 43], [58], [], [], [], [42, 1]], ![[0, 58], [58], [], [], [], [84, 100]]]
 h' := ![![[42, 100], [1, 12], [0, 19], [25], [96], [46], [0, 1]], ![[0, 1], [0, 89], [91, 82], [25], [96], [46], [42, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [4, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [47, 59, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-985, 295, -176]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![107, 43, -176]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![41, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![41, 1, 0]] 
 ![![101, 0, 0], ![41, 1, 0], ![34, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![41, 1, 0], ![0, 41, 7], ![182, 0, 41]]]
  hmulB := by decide  
  f := ![![![1436, 35, 0], ![-3535, 0, 0]], ![![574, 14, 0], ![-1413, 0, 0]], ![![442, -1, -2], ![-1088, 29, 0]]]
  g := ![![![1, 0, 0], ![-41, 101, 0], ![-34, 0, 101]], ![![0, 1, 0], ![-19, 41, 7], ![-12, 0, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-34, 23, 1]] ![![101, 0, 0], ![41, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![4141, 101, 0]], ![![-3434, 2323, 101], ![-1212, 909, 202]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![41, 1, 0]]], ![![![-34, 23, 1]], ![![-12, 9, 2]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [32, 72, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 64, 32], [9, 38, 71], [0, 1]]
 g := ![![[55, 52, 60], [44, 30, 97], [85, 35, 16], [18, 23], [], [1]], ![[79, 70, 1, 59], [18, 74, 73, 79], [101, 4, 4, 81], [63, 50], [8, 2], [32, 43, 84, 14]], ![[33, 43, 44, 12], [4, 102, 65, 53], [84, 93, 4, 51], [59, 28], [21, 2], [73, 36, 37, 89]]]
 h' := ![![[94, 64, 32], [34, 5, 67], [61, 80, 71], [78, 43, 4], [97, 76, 34], [71, 31], [0, 1]], ![[9, 38, 71], [16, 70, 28], [86, 11, 5], [100, 56, 86], [57, 76, 16], [101, 27, 65], [94, 64, 32]], ![[0, 1], [86, 28, 8], [9, 12, 27], [98, 4, 13], [82, 54, 53], [41, 45, 38], [9, 38, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101, 74], []]
 b := ![[], [50, 2, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [32, 72, 0, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5974, -618, -618]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-58, -6, -6]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![50, -38, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![50, -38, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![50, 69, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![50, -38, 1], ![182, 50, -266], ![-6916, 26, 50]]]
  hmulB := by decide  
  f := ![![![-49, 38, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-50, -69, 107]], ![![0, -1, 1], ![126, 172, -266], ![-88, -32, 50]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [71, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 106], [0, 1]]
 g := ![![[38, 42], [54, 25], [62], [53, 34], [44], [84, 1]], ![[35, 65], [14, 82], [62], [20, 73], [44], [61, 106]]]
 h' := ![![[84, 106], [18, 16], [95, 5], [89, 94], [14, 26], [28, 30], [0, 1]], ![[0, 1], [78, 91], [87, 102], [67, 13], [58, 81], [87, 77], [84, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [89, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [71, 23, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7011, 501, 2552]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1127, -1641, 2552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![52, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![52, 1, 0]] 
 ![![107, 0, 0], ![52, 1, 0], ![57, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![52, 1, 0], ![0, 52, 7], ![182, 0, 52]]]
  hmulB := by decide  
  f := ![![![1301, 25, 0], ![-2675, 0, 0]], ![![572, 11, 0], ![-1176, 0, 0]], ![![695, -9, -3], ![-1429, 46, 0]]]
  g := ![![![1, 0, 0], ![-52, 107, 0], ![-57, 0, 107]], ![![0, 1, 0], ![-29, 52, 7], ![-26, 0, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![50, -38, 1]] ![![107, 0, 0], ![52, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![5564, 107, 0]], ![![5350, -4066, 107], ![2782, -1926, -214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![52, 1, 0]]], ![![![50, -38, 1]], ![![26, -18, -2]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![31, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![31, 1, 0]] 
 ![![109, 0, 0], ![31, 1, 0], ![34, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![31, 1, 0], ![0, 31, 7], ![182, 0, 31]]]
  hmulB := by decide  
  f := ![![![1551, 50, 0], ![-5450, 0, 0]], ![![403, 13, 0], ![-1416, 0, 0]], ![![440, -8, -5], ![-1546, 78, 0]]]
  g := ![![![1, 0, 0], ![-31, 109, 0], ![-34, 0, 109]], ![![0, 1, 0], ![-11, 31, 7], ![-8, 0, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-22, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-22, 1, 0]] 
 ![![109, 0, 0], ![87, 1, 0], ![71, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-22, 1, 0], ![0, -22, 7], ![182, 0, -22]]]
  hmulB := by decide  
  f := ![![![155, -7, 0], ![763, 0, 0]], ![![133, -6, 0], ![655, 0, 0]], ![![105, 11, -5], ![517, 78, 0]]]
  g := ![![![1, 0, 0], ![-87, 109, 0], ![-71, 0, 109]], ![![-1, 1, 0], ![13, -22, 7], ![16, 0, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-9, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-9, 1, 0]] 
 ![![109, 0, 0], ![100, 1, 0], ![4, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-9, 1, 0], ![0, -9, 7], ![182, 0, -9]]]
  hmulB := by decide  
  f := ![![![892, -99, 0], ![10791, 0, 0]], ![![820, -91, 0], ![9920, 0, 0]], ![![40, 2, -5], ![484, 78, 0]]]
  g := ![![![1, 0, 0], ![-100, 109, 0], ![-4, 0, 109]], ![![-1, 1, 0], ![8, -9, 7], ![2, 0, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![31, 1, 0]] ![![109, 0, 0], ![-22, 1, 0]]
  ![![109, 0, 0], ![-4, 48, 1]] where
 M := ![![![11881, 0, 0], ![-2398, 109, 0]], ![![3379, 109, 0], ![-682, 9, 7]]]
 hmul := by decide  
 g := ![![![![109, 0, 0], ![0, 0, 0]], ![![-18, -47, -1], ![109, 0, 0]]], ![![![31, 1, 0], ![0, 0, 0]], ![![-6, -3, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-4, 48, 1]] ![![109, 0, 0], ![-9, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-981, 109, 0]], ![![-436, 5232, 109], ![218, -436, 327]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-9, 1, 0]]], ![![![-4, 48, 1]], ![![2, -4, 3]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-56, 52, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-56, 52, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![57, 52, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-56, 52, 1], ![182, -56, 364], ![9464, 26, -56]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -52, 113]], ![![-1, 0, 1], ![-182, -168, 364], ![112, 26, -56]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [60, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 112], [0, 1]]
 g := ![![[38, 81], [11], [28], [82], [7, 1], [93, 1]], ![[0, 32], [11], [28], [82], [100, 112], [73, 112]]]
 h' := ![![[93, 112], [67, 9], [106, 24], [59, 49], [32, 67], [70, 1], [0, 1]], ![[0, 1], [0, 104], [78, 89], [96, 64], [48, 46], [50, 112], [93, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [14, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [60, 20, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1051, 80, 45]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32, -20, 45]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-25, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-25, 1, 0]] 
 ![![113, 0, 0], ![88, 1, 0], ![56, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-25, 1, 0], ![0, -25, 7], ![182, 0, -25]]]
  hmulB := by decide  
  f := ![![![2701, -108, 0], ![12204, 0, 0]], ![![2126, -85, 0], ![9606, 0, 0]], ![![1362, -33, -6], ![6154, 97, 0]]]
  g := ![![![1, 0, 0], ![-88, 113, 0], ![-56, 0, 113]], ![![-1, 1, 0], ![16, -25, 7], ![14, 0, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-56, 52, 1]] ![![113, 0, 0], ![-25, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-2825, 113, 0]], ![![-6328, 5876, 113], ![1582, -1356, 339]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-25, 1, 0]]], ![![![-56, 52, 1]], ![![14, -12, 3]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![33, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![33, 1, 0]] 
 ![![127, 0, 0], ![33, 1, 0], ![44, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![33, 1, 0], ![0, 33, 7], ![182, 0, 33]]]
  hmulB := by decide  
  f := ![![![1750, 53, 0], ![-6731, 0, 0]], ![![462, 14, 0], ![-1777, 0, 0]], ![![572, -11, -6], ![-2200, 109, 0]]]
  g := ![![![1, 0, 0], ![-33, 127, 0], ![-44, 0, 127]], ![![0, 1, 0], ![-11, 33, 7], ![-10, 0, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-25, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-25, 1, 0]] 
 ![![127, 0, 0], ![102, 1, 0], ![74, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-25, 1, 0], ![0, -25, 7], ![182, 0, -25]]]
  hmulB := by decide  
  f := ![![![1876, -75, 0], ![9525, 0, 0]], ![![1476, -59, 0], ![7494, 0, 0]], ![![1112, -23, -6], ![5646, 109, 0]]]
  g := ![![![1, 0, 0], ![-102, 127, 0], ![-74, 0, 127]], ![![-1, 1, 0], ![16, -25, 7], ![16, 0, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-8, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-8, 1, 0]] 
 ![![127, 0, 0], ![119, 1, 0], ![9, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-8, 1, 0], ![0, -8, 7], ![182, 0, -8]]]
  hmulB := by decide  
  f := ![![![145, -18, 0], ![2286, 0, 0]], ![![137, -17, 0], ![2160, 0, 0]], ![![23, 4, -6], ![364, 109, 0]]]
  g := ![![![1, 0, 0], ![-119, 127, 0], ![-9, 0, 127]], ![![-1, 1, 0], ![7, -8, 7], ![2, 0, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![33, 1, 0]] ![![127, 0, 0], ![-25, 1, 0]]
  ![![127, 0, 0], ![-9, -17, 1]] where
 M := ![![![16129, 0, 0], ![-3175, 127, 0]], ![![4191, 127, 0], ![-825, 8, 7]]]
 hmul := by decide  
 g := ![![![![127, 0, 0], ![0, 0, 0]], ![![-16, 18, -1], ![127, 0, 0]]], ![![![33, 1, 0], ![0, 0, 0]], ![![-6, 1, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-9, -17, 1]] ![![127, 0, 0], ![-8, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-1016, 127, 0]], ![![-1143, -2159, 127], ![254, 127, -127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-8, 1, 0]]], ![![![-9, -17, 1]], ![![2, 1, -1]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-23, -41, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-23, -41, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![108, 90, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-23, -41, 1], ![182, -23, -287], ![-7462, 26, -23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-108, -90, 131]], ![![-1, -1, 1], ![238, 197, -287], ![-38, 16, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [19, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 130], [0, 1]]
 g := ![![[79, 109], [98, 45], [5], [109], [75], [63], [1]], ![[89, 22], [18, 86], [5], [109], [75], [63], [1]]]
 h' := ![![[71, 130], [103, 90], [12, 62], [99, 23], [27, 90], [81, 72], [112, 71], [0, 1]], ![[0, 1], [74, 41], [91, 69], [29, 108], [129, 41], [84, 59], [44, 60], [71, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [55, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [19, 60, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![747, 164, 127]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-99, -86, 127]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![25, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![25, 1, 0]] 
 ![![131, 0, 0], ![25, 1, 0], ![23, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![25, 1, 0], ![0, 25, 7], ![182, 0, 25]]]
  hmulB := by decide  
  f := ![![![476, 19, 0], ![-2489, 0, 0]], ![![50, 2, 0], ![-261, 0, 0]], ![![58, -12, -4], ![-303, 75, 0]]]
  g := ![![![1, 0, 0], ![-25, 131, 0], ![-23, 0, 131]], ![![0, 1, 0], ![-6, 25, 7], ![-3, 0, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-23, -41, 1]] ![![131, 0, 0], ![25, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![3275, 131, 0]], ![![-3013, -5371, 131], ![-393, -1048, -262]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![25, 1, 0]]], ![![![-23, -41, 1]], ![![-3, -8, -2]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-64, 21, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-64, 21, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![73, 21, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-64, 21, 1], ![182, -64, 147], ![3822, 26, -64]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-73, -21, 137]], ![![-1, 0, 1], ![-77, -23, 147], ![62, 10, -64]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [70, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [95, 136], [0, 1]]
 g := ![![[28, 68], [107], [105], [31, 25], [50], [120], [1]], ![[49, 69], [107], [105], [77, 112], [50], [120], [1]]]
 h' := ![![[95, 136], [27, 94], [121, 45], [22, 67], [70, 132], [62, 18], [67, 95], [0, 1]], ![[0, 1], [52, 43], [12, 92], [85, 70], [6, 5], [128, 119], [50, 42], [95, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [115, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [70, 42, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7122, -356, 792]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-474, -124, 792]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-10, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-10, 1, 0]] 
 ![![137, 0, 0], ![127, 1, 0], ![64, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-10, 1, 0], ![0, -10, 7], ![182, 0, -10]]]
  hmulB := by decide  
  f := ![![![1021, -102, 0], ![13974, 0, 0]], ![![931, -93, 0], ![12742, 0, 0]], ![![472, -40, -5], ![6460, 98, 0]]]
  g := ![![![1, 0, 0], ![-127, 137, 0], ![-64, 0, 137]], ![![-1, 1, 0], ![6, -10, 7], ![6, 0, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-64, 21, 1]] ![![137, 0, 0], ![-10, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-1370, 137, 0]], ![![-8768, 2877, 137], ![822, -274, 137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-10, 1, 0]]], ![![![-64, 21, 1]], ![![6, -2, 1]]]]
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


lemma PB268I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB268I2 : PrimesBelowBoundCertificateInterval O 79 137 268 where
  m := 11
  g := ![2, 2, 1, 2, 1, 2, 3, 2, 3, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB268I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
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
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
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
  β := ![I83N1, I89N1, I101N1, I107N1, I109N0, I109N1, I109N2, I113N1, I127N0, I127N1, I127N2, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [], [I101N1], [], [I107N1], [I109N0, I109N1, I109N2], [I113N1], [I127N0, I127N1, I127N2], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
