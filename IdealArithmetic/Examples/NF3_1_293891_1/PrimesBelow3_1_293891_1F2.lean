
import IdealArithmetic.Examples.NF3_1_293891_1.RI3_1_293891_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 4, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-11, 4, 0]] 
 ![![83, 0, 0], ![18, 1, 0], ![8, 0, 1]] where
  M :=![![![-11, 4, 0], ![0, -11, 4], ![364, -104, -11]]]
  hmulB := by decide  
  f := ![![![-537, -44, -16]], ![![-134, -11, -4]], ![![-100, -8, -3]]]
  g := ![![![-1, 4, 0], ![2, -11, 4], ![28, -104, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1203, -98, -36]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-1203, -98, -36]] 
 ![![83, 0, 0], ![26, 1, 0], ![71, 0, 1]] where
  M :=![![![-1203, -98, -36], ![-3276, -267, -98], ![-8918, -728, -267]]]
  hmulB := by decide  
  f := ![![![55, -42, 8]], ![![26, -15, 2]], ![![1, -14, 5]]]
  g := ![![![47, -98, -36], ![128, -267, -98], ![349, -728, -267]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -2, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![5, -2, 0]] 
 ![![83, 0, 0], ![39, 1, 0], ![56, 0, 1]] where
  M :=![![![5, -2, 0], ![0, 5, -2], ![-182, 52, 5]]]
  hmulB := by decide  
  f := ![![![-129, -10, -4]], ![![-65, -5, -2]], ![![-98, -8, -3]]]
  g := ![![![1, -2, 0], ![-1, 5, -2], ![-30, 52, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-11, 4, 0]] ![![-1203, -98, -36]]
  ![![129, 10, 4]] where
 M := ![![![129, 10, 4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![129, 10, 4]] ![![5, -2, 0]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![4, 45, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![4, 45, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![4, 45, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![4, 45, 1], ![91, -22, 45], ![4095, -1079, -22]]]
  hmulB := by decide  
  f := ![![![-3, -45, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -45, 89]], ![![0, 0, 1], ![-1, -23, 45], ![47, -1, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [18, 14, 1] where
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
 g := ![![[70, 5], [84], [81], [7, 45], [74, 18], [1]], ![[0, 84], [84], [81], [0, 44], [0, 71], [1]]]
 h' := ![![[75, 88], [1, 70], [0, 66], [52, 80], [3, 32], [71, 75], [0, 1]], ![[0, 1], [0, 19], [55, 23], [0, 9], [0, 57], [0, 14], [75, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [53, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [18, 14, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![200, 25, -39]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, 20, -39]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![44, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![44, 1, 0]] 
 ![![89, 0, 0], ![44, 1, 0], ![22, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![44, 1, 0], ![0, 44, 1], ![91, -26, 44]]]
  hmulB := by decide  
  f := ![![![837, 19, 0], ![-1691, 0, 0]], ![![396, 9, 0], ![-800, 0, 0]], ![![198, 4, 0], ![-400, 1, 0]]]
  g := ![![![1, 0, 0], ![-44, 89, 0], ![-22, 0, 89]], ![![0, 1, 0], ![-22, 44, 1], ![3, -26, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![4, 45, 1]] ![![89, 0, 0], ![44, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![3916, 89, 0]], ![![356, 4005, 89], ![267, 1958, 89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![44, 1, 0]]], ![![![4, 45, 1]], ![![3, 22, 1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![4, 47, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![4, 47, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![4, 47, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![4, 47, 1], ![91, -22, 47], ![4277, -1131, -22]]]
  hmulB := by decide  
  f := ![![![-3, -47, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -47, 97]], ![![0, 0, 1], ![-1, -23, 47], ![45, -1, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [24, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 96], [0, 1]]
 g := ![![[8, 93], [79], [66], [16], [12], [2, 1]], ![[0, 4], [79], [66], [16], [12], [4, 96]]]
 h' := ![![[2, 96], [9, 44], [16, 51], [57, 58], [76, 4], [49, 77], [0, 1]], ![[0, 1], [0, 53], [21, 46], [76, 39], [84, 93], [9, 20], [2, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [78, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [24, 95, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1162, 945, 49]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, -14, 49]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-47, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-47, 1, 0]] 
 ![![97, 0, 0], ![50, 1, 0], ![22, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-47, 1, 0], ![0, -47, 1], ![91, -26, -47]]]
  hmulB := by decide  
  f := ![![![3855, -82, 0], ![7954, 0, 0]], ![![2022, -43, 0], ![4172, 0, 0]], ![![916, -19, 0], ![1890, 1, 0]]]
  g := ![![![1, 0, 0], ![-50, 97, 0], ![-22, 0, 97]], ![![-1, 1, 0], ![24, -47, 1], ![25, -26, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![4, 47, 1]] ![![97, 0, 0], ![-47, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-4559, 97, 0]], ![![388, 4559, 97], ![-97, -2231, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-47, 1, 0]]], ![![![4, 47, 1]], ![![-1, -23, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![13, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![13, 1, 0]] 
 ![![101, 0, 0], ![13, 1, 0], ![33, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![13, 1, 0], ![0, 13, 1], ![91, -26, 13]]]
  hmulB := by decide  
  f := ![![![729, 56, 0], ![-5656, 0, 0]], ![![91, 7, 0], ![-706, 0, 0]], ![![223, 17, 0], ![-1730, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 101, 0], ![-33, 0, 101]], ![![0, 1, 0], ![-2, 13, 1], ![0, -26, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![21, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![21, 1, 0]] 
 ![![101, 0, 0], ![21, 1, 0], ![64, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![21, 1, 0], ![0, 21, 1], ![91, -26, 21]]]
  hmulB := by decide  
  f := ![![![1114, 53, 0], ![-5353, 0, 0]], ![![210, 10, 0], ![-1009, 0, 0]], ![![698, 33, 0], ![-3354, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 101, 0], ![-64, 0, 101]], ![![0, 1, 0], ![-5, 21, 1], ![-7, -26, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-34, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-34, 1, 0]] 
 ![![101, 0, 0], ![67, 1, 0], ![56, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-34, 1, 0], ![0, -34, 1], ![91, -26, -34]]]
  hmulB := by decide  
  f := ![![![171, -5, 0], ![505, 0, 0]], ![![137, -4, 0], ![405, 0, 0]], ![![148, -4, 0], ![438, 1, 0]]]
  g := ![![![1, 0, 0], ![-67, 101, 0], ![-56, 0, 101]], ![![-1, 1, 0], ![22, -34, 1], ![37, -26, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![13, 1, 0]] ![![101, 0, 0], ![21, 1, 0]]
  ![![101, 0, 0], ![-30, 34, 1]] where
 M := ![![![10201, 0, 0], ![2121, 101, 0]], ![![1313, 101, 0], ![273, 34, 1]]]
 hmul := by decide  
 g := ![![![![101, 0, 0], ![0, 0, 0]], ![![21, 1, 0], ![0, 0, 0]]], ![![![13, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-30, 34, 1]] ![![101, 0, 0], ![-34, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-3434, 101, 0]], ![![-3030, 3434, 101], ![1111, -1212, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-34, 1, 0]]], ![![![-30, 34, 1]], ![![11, -12, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-94, 29, 2]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-94, 29, 2]] 
 ![![103, 0, 0], ![0, 103, 0], ![56, 66, 1]] where
  M :=![![![-94, 29, 2], ![182, -146, 29], ![2639, -572, -146]]]
  hmulB := by decide  
  f := ![![![-368, -30, -11]], ![![-1001, -82, -30]], ![![-868, -71, -26]]]
  g := ![![![-2, -1, 2], ![-14, -20, 29], ![105, 88, -146]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [72, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 102], [0, 1]]
 g := ![![[13, 93], [79, 66], [66, 76], [83], [81], [94, 1]], ![[0, 10], [0, 37], [0, 27], [83], [81], [85, 102]]]
 h' := ![![[94, 102], [80, 89], [89, 90], [39, 73], [12, 17], [30, 9], [0, 1]], ![[0, 1], [0, 14], [0, 13], [0, 30], [65, 86], [52, 94], [94, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [9, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [72, 9, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3410, 24, 94]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, -60, 94]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![368, 30, 11]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![368, 30, 11]] 
 ![![103, 0, 0], ![37, 1, 0], ![73, 0, 1]] where
  M :=![![![368, 30, 11], ![1001, 82, 30], ![2730, 221, 82]]]
  hmulB := by decide  
  f := ![![![94, -29, -2]], ![![32, -9, -1]], ![![41, -15, 0]]]
  g := ![![![-15, 30, 11], ![-41, 82, 30], ![-111, 221, 82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-94, 29, 2]] ![![368, 30, 11]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![21, 40, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![21, 40, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![21, 40, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![21, 40, 1], ![91, -5, 40], ![3640, -949, -5]]]
  hmulB := by decide  
  f := ![![![-20, -40, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -40, 107]], ![![0, 0, 1], ![-7, -15, 40], ![35, -7, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [85, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [103, 106], [0, 1]]
 g := ![![[29, 34], [5, 29], [100], [78, 29], [53], [103, 1]], ![[0, 73], [103, 78], [100], [69, 78], [53], [99, 106]]]
 h' := ![![[103, 106], [3, 81], [76, 55], [4, 97], [29, 55], [19, 38], [0, 1]], ![[0, 1], [0, 26], [70, 52], [44, 10], [23, 52], [81, 69], [103, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [37, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [85, 4, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-456, 981, -251]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![45, 103, -251]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-40, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-40, 1, 0]] 
 ![![107, 0, 0], ![67, 1, 0], ![5, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-40, 1, 0], ![0, -40, 1], ![91, -26, -40]]]
  hmulB := by decide  
  f := ![![![4201, -105, 0], ![11235, 0, 0]], ![![2641, -66, 0], ![7063, 0, 0]], ![![215, -5, 0], ![575, 1, 0]]]
  g := ![![![1, 0, 0], ![-67, 107, 0], ![-5, 0, 107]], ![![-1, 1, 0], ![25, -40, 1], ![19, -26, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![21, 40, 1]] ![![107, 0, 0], ![-40, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-4280, 107, 0]], ![![2247, 4280, 107], ![-749, -1605, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-40, 1, 0]]], ![![![21, 40, 1]], ![![-7, -15, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![20, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![20, 1, 0]] 
 ![![109, 0, 0], ![20, 1, 0], ![36, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![20, 1, 0], ![0, 20, 1], ![91, -26, 20]]]
  hmulB := by decide  
  f := ![![![961, 48, 0], ![-5232, 0, 0]], ![![140, 7, 0], ![-762, 0, 0]], ![![284, 14, 0], ![-1546, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 109, 0], ![-36, 0, 109]], ![![0, 1, 0], ![-4, 20, 1], ![-1, -26, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3141, -256, -94]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-3141, -256, -94]] 
 ![![109, 0, 0], ![98, 1, 0], ![97, 0, 1]] where
  M :=![![![-3141, -256, -94], ![-8554, -697, -256], ![-23296, -1898, -697]]]
  hmulB := by decide  
  f := ![![![79, 20, -18]], ![![56, 23, -16]], ![![87, -2, -11]]]
  g := ![![![285, -256, -94], ![776, -697, -256], ![2113, -1898, -697]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-9, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-9, 1, 0]] 
 ![![109, 0, 0], ![100, 1, 0], ![28, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-9, 1, 0], ![0, -9, 1], ![91, -26, -9]]]
  hmulB := by decide  
  f := ![![![892, -99, 0], ![10791, 0, 0]], ![![820, -91, 0], ![9920, 0, 0]], ![![244, -27, 0], ![2952, 1, 0]]]
  g := ![![![1, 0, 0], ![-100, 109, 0], ![-28, 0, 109]], ![![-1, 1, 0], ![8, -9, 1], ![27, -26, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![20, 1, 0]] ![![-3141, -256, -94]]
  ![![109, 0, 0], ![-2, 9, 1]] where
 M := ![![![-342369, -27904, -10246]], ![![-71374, -5817, -2136]]]
 hmul := by decide  
 g := ![![![![-3139, -265, -95], ![109, 0, 0]]], ![![![-654, -57, -20], ![44, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-2, 9, 1]] ![![109, 0, 0], ![-9, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-981, 109, 0]], ![![-218, 981, 109], ![109, -109, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-9, 1, 0]]], ![![![-2, 9, 1]], ![![1, -1, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [3, 90, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 78, 19], [83, 34, 94], [0, 1]]
 g := ![![[48, 92, 82], [2, 25], [40, 15], [65, 91], [68, 55, 105], [1]], ![[22, 25, 63, 92], [49, 81], [54, 62], [54, 1], [23, 38, 51, 71], [26, 33, 103, 79]], ![[70, 99, 85, 10], [9, 83], [111, 32], [54, 97], [58, 11, 76, 55], [27, 58, 57, 34]]]
 h' := ![![[82, 78, 19], [43, 48, 46], [7, 62, 108], [63, 7, 44], [22, 52, 54], [110, 23, 52], [0, 1]], ![[83, 34, 94], [64, 16, 103], [95, 112, 104], [12, 36, 47], [93, 112, 112], [76, 51, 58], [82, 78, 19]], ![[0, 1], [85, 49, 77], [15, 52, 14], [3, 70, 22], [74, 62, 60], [39, 39, 3], [83, 34, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 82], []]
 b := ![[], [8, 61, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [3, 90, 61, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9831, 4746, -2486]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![87, 42, -22]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![67, 26, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![67, 26, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![67, 26, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![67, 26, 1], ![91, 41, 26], ![2366, -585, 41]]]
  hmulB := by decide  
  f := ![![![-66, -26, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-67, -26, 127]], ![![0, 0, 1], ![-13, -5, 26], ![-3, -13, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [72, 77, 1] where
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
 g := ![![[24, 30], [32, 104], [103, 69], [21, 35], [24, 98], [50, 1]], ![[0, 97], [25, 23], [124, 58], [120, 92], [98, 29], [100, 126]]]
 h' := ![![[50, 126], [109, 41], [77, 72], [12, 14], [50, 17], [83, 15], [0, 1]], ![[0, 1], [0, 86], [121, 55], [77, 113], [11, 110], [71, 112], [50, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [92, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [72, 77, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3608, 604, 414]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-190, -80, 414]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-26, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-26, 1, 0]] 
 ![![127, 0, 0], ![101, 1, 0], ![86, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-26, 1, 0], ![0, -26, 1], ![91, -26, -26]]]
  hmulB := by decide  
  f := ![![![1457, -56, 0], ![7112, 0, 0]], ![![1171, -45, 0], ![5716, 0, 0]], ![![994, -38, 0], ![4852, 1, 0]]]
  g := ![![![1, 0, 0], ![-101, 127, 0], ![-86, 0, 127]], ![![-1, 1, 0], ![20, -26, 1], ![39, -26, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![67, 26, 1]] ![![127, 0, 0], ![-26, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-3302, 127, 0]], ![![8509, 3302, 127], ![-1651, -635, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-26, 1, 0]]], ![![![67, 26, 1]], ![![-13, -5, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36, 19, -2]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-36, 19, -2]] 
 ![![131, 0, 0], ![0, 131, 0], ![18, 56, 1]] where
  M :=![![![-36, 19, -2], ![-182, 16, 19], ![1729, -676, 16]]]
  hmulB := by decide  
  f := ![![![100, 8, 3]], ![![273, 22, 8]], ![![136, 11, 4]]]
  g := ![![![0, 1, -2], ![-4, -8, 19], ![11, -12, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [98, 126, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 130], [0, 1]]
 g := ![![[20, 107], [107, 108], [53], [89], [45], [25], [1]], ![[31, 24], [123, 23], [53], [89], [45], [25], [1]]]
 h' := ![![[5, 130], [125, 32], [16, 97], [25, 70], [25, 58], [80, 62], [33, 5], [0, 1]], ![[0, 1], [23, 99], [108, 34], [113, 61], [53, 73], [128, 69], [58, 126], [5, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [106, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [98, 126, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-573, 619, -141]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15, 65, -141]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![100, 8, 3]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![100, 8, 3]] 
 ![![131, 0, 0], ![75, 1, 0], ![8, 0, 1]] where
  M :=![![![100, 8, 3], ![273, 22, 8], ![728, 65, 22]]]
  hmulB := by decide  
  f := ![![![-36, 19, -2]], ![![-22, 11, -1]], ![![11, -4, 0]]]
  g := ![![![-4, 8, 3], ![-11, 22, 8], ![-33, 65, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-36, 19, -2]] ![![100, 8, 3]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![28, -31, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![28, -31, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![28, 106, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![28, -31, 1], ![91, 2, -31], ![-2821, 897, 2]]]
  hmulB := by decide  
  f := ![![![-27, 31, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -106, 137]], ![![0, -1, 1], ![7, 24, -31], ![-21, 5, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [105, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 136], [0, 1]]
 g := ![![[19, 107], [129], [19], [107, 107], [107], [38], [1]], ![[0, 30], [129], [19], [88, 30], [107], [38], [1]]]
 h' := ![![[60, 136], [40, 45], [61, 102], [136, 108], [111, 45], [48, 92], [32, 60], [0, 1]], ![[0, 1], [0, 92], [16, 35], [40, 29], [71, 92], [88, 45], [70, 77], [60, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [106, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [105, 77, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![469, 337, 51]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7, -37, 51]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![31, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![31, 1, 0]] 
 ![![137, 0, 0], ![31, 1, 0], ![135, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![31, 1, 0], ![0, 31, 1], ![91, -26, 31]]]
  hmulB := by decide  
  f := ![![![1861, 60, 0], ![-8220, 0, 0]], ![![403, 13, 0], ![-1780, 0, 0]], ![![1837, 59, 0], ![-8114, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 137, 0], ![-135, 0, 137]], ![![0, 1, 0], ![-8, 31, 1], ![-24, -26, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![28, -31, 1]] ![![137, 0, 0], ![31, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![4247, 137, 0]], ![![3836, -4247, 137], ![959, -959, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![31, 1, 0]]], ![![![28, -31, 1]], ![![7, -7, 0]]]]
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


lemma PB154I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB154I2 : PrimesBelowBoundCertificateInterval O 79 137 154 where
  m := 11
  g := ![3, 2, 2, 3, 2, 2, 3, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB154I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
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
    · exact ![83, 83, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![1442897]
    · exact ![16129, 127]
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
      exact NI83N2
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
      exact NI101N2
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
      exact NI109N1
      exact NI109N2
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
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N0, I83N1, I83N2, I89N1, I97N1, I101N0, I101N1, I101N2, I103N1, I107N1, I109N0, I109N1, I109N2, I127N1, I131N1, I137N1]
  Il := ![[I83N0, I83N1, I83N2], [I89N1], [I97N1], [I101N0, I101N1, I101N2], [I103N1], [I107N1], [I109N0, I109N1, I109N2], [], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
