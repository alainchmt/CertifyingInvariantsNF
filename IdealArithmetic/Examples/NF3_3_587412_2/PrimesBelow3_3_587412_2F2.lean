
import IdealArithmetic.Examples.NF3_3_587412_2.RI3_3_587412_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![0, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![0, 1, 0]] 
 ![![83, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![0, 1, 0], ![0, 0, 1], ![1162, 210, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![0, 1, 0], ![0, 0, 1], ![14, 210, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![25, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![25, 1, 0]] 
 ![![83, 0, 0], ![25, 1, 0], ![39, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![25, 1, 0], ![0, 25, 1], ![1162, 210, 25]]]
  hmulB := by decide  
  f := ![![![201, 8, 0], ![-664, 0, 0]], ![![25, 1, 0], ![-82, 0, 0]], ![![83, 3, 0], ![-274, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 83, 0], ![-39, 0, 83]], ![![0, 1, 0], ![-8, 25, 1], ![-61, 210, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-25, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-25, 1, 0]] 
 ![![83, 0, 0], ![58, 1, 0], ![39, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-25, 1, 0], ![0, -25, 1], ![1162, 210, -25]]]
  hmulB := by decide  
  f := ![![![401, -16, 0], ![1328, 0, 0]], ![![276, -11, 0], ![914, 0, 0]], ![![183, -7, 0], ![606, 1, 0]]]
  g := ![![![1, 0, 0], ![-58, 83, 0], ![-39, 0, 83]], ![![-1, 1, 0], ![17, -25, 1], ![-121, 210, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![0, 1, 0]] ![![83, 0, 0], ![25, 1, 0]]
  ![![83, 0, 0], ![-166, 25, 1]] where
 M := ![![![6889, 0, 0], ![2075, 83, 0]], ![![0, 83, 0], ![0, 25, 1]]]
 hmul := by decide  
 g := ![![![![83, 0, 0], ![0, 0, 0]], ![![25, 1, 0], ![0, 0, 0]]], ![![![166, -24, -1], ![83, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-166, 25, 1]] ![![83, 0, 0], ![-25, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-2075, 83, 0]], ![![-13778, 2075, 83], ![5312, -581, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-25, 1, 0]]], ![![![-166, 25, 1]], ![![64, -7, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-153, 18, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-153, 18, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![25, 18, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-153, 18, 1], ![1162, 57, 18], ![20916, 4942, 57]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -18, 89]], ![![-2, 0, 1], ![8, -3, 18], ![219, 44, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [22, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 88], [0, 1]]
 g := ![![[44, 85], [42], [22], [47, 5], [46, 32], [1]], ![[0, 4], [42], [22], [13, 84], [42, 57], [1]]]
 h' := ![![[11, 88], [53, 68], [49, 65], [34, 72], [56, 19], [67, 11], [0, 1]], ![[0, 1], [0, 21], [52, 24], [25, 17], [87, 70], [10, 78], [11, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [30, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [22, 78, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2346, 1504, 133]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, -10, 133]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-18, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-18, 1, 0]] 
 ![![89, 0, 0], ![71, 1, 0], ![32, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-18, 1, 0], ![0, -18, 1], ![1162, 210, -18]]]
  hmulB := by decide  
  f := ![![![127, -7, 0], ![623, 0, 0]], ![![109, -6, 0], ![535, 0, 0]], ![![76, -4, 0], ![374, 1, 0]]]
  g := ![![![1, 0, 0], ![-71, 89, 0], ![-32, 0, 89]], ![![-1, 1, 0], ![14, -18, 1], ![-148, 210, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-153, 18, 1]] ![![89, 0, 0], ![-18, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1602, 89, 0]], ![![-13617, 1602, 89], ![3916, -267, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-18, 1, 0]]], ![![![-153, 18, 1]], ![![44, -3, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-111, 14, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-111, 14, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![83, 14, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-111, 14, 1], ![1162, 99, 14], ![16268, 4102, 99]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-83, -14, 97]], ![![-2, 0, 1], ![0, -1, 14], ![83, 28, 99]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [27, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 96], [0, 1]]
 g := ![![[46, 18], [72], [79], [89], [6], [19, 1]], ![[0, 79], [72], [79], [89], [6], [38, 96]]]
 h' := ![![[19, 96], [75, 42], [51, 84], [70, 46], [40, 34], [69, 43], [0, 1]], ![[0, 1], [0, 55], [95, 13], [71, 51], [7, 63], [13, 54], [19, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [48, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [27, 78, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13994, 7786, 2122]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1960, -226, 2122]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-14, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-14, 1, 0]] 
 ![![97, 0, 0], ![83, 1, 0], ![95, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-14, 1, 0], ![0, -14, 1], ![1162, 210, -14]]]
  hmulB := by decide  
  f := ![![![127, -9, 0], ![873, 0, 0]], ![![113, -8, 0], ![777, 0, 0]], ![![129, -9, 0], ![887, 1, 0]]]
  g := ![![![1, 0, 0], ![-83, 97, 0], ![-95, 0, 97]], ![![-1, 1, 0], ![11, -14, 1], ![-154, 210, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-111, 14, 1]] ![![97, 0, 0], ![-14, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-1358, 97, 0]], ![![-10767, 1358, 97], ![2716, -97, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-14, 1, 0]]], ![![![-111, 14, 1]], ![![28, -1, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![40, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![40, 1, 0]] 
 ![![101, 0, 0], ![40, 1, 0], ![16, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![40, 1, 0], ![0, 40, 1], ![1162, 210, 40]]]
  hmulB := by decide  
  f := ![![![1281, 32, 0], ![-3232, 0, 0]], ![![440, 11, 0], ![-1110, 0, 0]], ![![176, 4, 0], ![-444, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 101, 0], ![-16, 0, 101]], ![![0, 1, 0], ![-16, 40, 1], ![-78, 210, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-31, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-31, 1, 0]] 
 ![![101, 0, 0], ![70, 1, 0], ![49, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-31, 1, 0], ![0, -31, 1], ![1162, 210, -31]]]
  hmulB := by decide  
  f := ![![![2977, -96, 0], ![9696, 0, 0]], ![![2078, -67, 0], ![6768, 0, 0]], ![![1467, -47, 0], ![4778, 1, 0]]]
  g := ![![![1, 0, 0], ![-70, 101, 0], ![-49, 0, 101]], ![![-1, 1, 0], ![21, -31, 1], ![-119, 210, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-9, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-9, 1, 0]] 
 ![![101, 0, 0], ![92, 1, 0], ![20, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-9, 1, 0], ![0, -9, 1], ![1162, 210, -9]]]
  hmulB := by decide  
  f := ![![![460, -51, 0], ![5151, 0, 0]], ![![406, -45, 0], ![4546, 0, 0]], ![![100, -11, 0], ![1120, 1, 0]]]
  g := ![![![1, 0, 0], ![-92, 101, 0], ![-20, 0, 101]], ![![-1, 1, 0], ![8, -9, 1], ![-178, 210, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![40, 1, 0]] ![![101, 0, 0], ![-31, 1, 0]]
  ![![101, 0, 0], ![-129, 9, 1]] where
 M := ![![![10201, 0, 0], ![-3131, 101, 0]], ![![4040, 101, 0], ![-1240, 9, 1]]]
 hmul := by decide  
 g := ![![![![101, 0, 0], ![0, 0, 0]], ![![98, -8, -1], ![101, 0, 0]]], ![![![40, 1, 0], ![0, 0, 0]], ![![118, -9, -1], ![102, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-129, 9, 1]] ![![101, 0, 0], ![-9, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-909, 101, 0]], ![![-13029, 909, 101], ![2323, 0, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-9, 1, 0]]], ![![![-129, 9, 1]], ![![23, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-149, 24, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-149, 24, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![57, 24, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-149, 24, 1], ![1162, 61, 24], ![27888, 6202, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -24, 103]], ![![-2, 0, 1], ![-2, -5, 24], ![237, 46, 61]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [13, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 102], [0, 1]]
 g := ![![[71, 8], [40, 93], [36, 4], [59], [9], [4, 1]], ![[0, 95], [0, 10], [52, 99], [59], [9], [8, 102]]]
 h' := ![![[4, 102], [98, 27], [47, 14], [98, 101], [12, 33], [51, 3], [0, 1]], ![[0, 1], [0, 76], [0, 89], [90, 2], [41, 70], [63, 100], [4, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [80, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [13, 99, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4551, 713, 240]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-177, -49, 240]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-24, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-24, 1, 0]] 
 ![![103, 0, 0], ![79, 1, 0], ![42, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-24, 1, 0], ![0, -24, 1], ![1162, 210, -24]]]
  hmulB := by decide  
  f := ![![![1993, -83, 0], ![8549, 0, 0]], ![![1537, -64, 0], ![6593, 0, 0]], ![![822, -34, 0], ![3526, 1, 0]]]
  g := ![![![1, 0, 0], ![-79, 103, 0], ![-42, 0, 103]], ![![-1, 1, 0], ![18, -24, 1], ![-140, 210, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-149, 24, 1]] ![![103, 0, 0], ![-24, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-2472, 103, 0]], ![![-15347, 2472, 103], ![4738, -515, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-24, 1, 0]]], ![![![-149, 24, 1]], ![![46, -5, 0]]]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [65, 64, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 61, 40], [56, 45, 67], [0, 1]]
 g := ![![[63, 58, 49], [106, 44, 62], [81, 14], [58, 38, 14], [70, 87], [1]], ![[66, 106, 102, 11], [105, 72, 35, 9], [100, 99], [21, 83, 17, 19], [62, 83], [51, 29, 105, 14]], ![[38, 73, 42, 93], [30, 65, 80, 63], [50, 86], [15, 50, 89, 72], [13, 86], [89, 84, 17, 93]]]
 h' := ![![[78, 61, 40], [65, 9, 7], [68, 38, 94], [82, 40, 11], [103, 4, 11], [42, 43, 27], [0, 1]], ![[56, 45, 67], [91, 2, 33], [38, 78, 79], [15, 6, 62], [10, 57, 13], [9, 24, 46], [78, 61, 40]], ![[0, 1], [102, 96, 67], [52, 98, 41], [29, 61, 34], [67, 46, 83], [22, 40, 34], [56, 45, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 81], []]
 b := ![[], [27, 72, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [65, 64, 80, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30445352, -11232967, -1004944]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-284536, -104981, -9392]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-161, 7, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-161, 7, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![57, 7, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-161, 7, 1], ![1162, 49, 7], ![8134, 2632, 49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -7, 109]], ![![-2, 0, 1], ![7, 0, 7], ![49, 21, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [73, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 108], [0, 1]]
 g := ![![[2, 3], [20], [71, 97], [11, 83], [35], [72, 1]], ![[0, 106], [20], [79, 12], [101, 26], [35], [35, 108]]]
 h' := ![![[72, 108], [69, 49], [49, 67], [69, 36], [92, 44], [85, 97], [0, 1]], ![[0, 1], [0, 60], [77, 42], [45, 73], [99, 65], [93, 12], [72, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [28, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [73, 37, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2397, 1545, 174]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-69, 3, 174]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-7, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-7, 1, 0]] 
 ![![109, 0, 0], ![102, 1, 0], ![60, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-7, 1, 0], ![0, -7, 1], ![1162, 210, -7]]]
  hmulB := by decide  
  f := ![![![575, -82, 0], ![8938, 0, 0]], ![![540, -77, 0], ![8394, 0, 0]], ![![316, -45, 0], ![4912, 1, 0]]]
  g := ![![![1, 0, 0], ![-102, 109, 0], ![-60, 0, 109]], ![![-1, 1, 0], ![6, -7, 1], ![-182, 210, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-161, 7, 1]] ![![109, 0, 0], ![-7, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-763, 109, 0]], ![![-17549, 763, 109], ![2289, 0, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-7, 1, 0]]], ![![![-161, 7, 1]], ![![21, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-154, 13, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-154, 13, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![72, 13, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-154, 13, 1], ![1162, 56, 13], ![15106, 3892, 56]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -13, 113]], ![![-2, 0, 1], ![2, -1, 13], ![98, 28, 56]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [63, 107, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 112], [0, 1]]
 g := ![![[86, 61], [56], [64], [8], [39, 51], [6, 1]], ![[0, 52], [56], [64], [8], [6, 62], [12, 112]]]
 h' := ![![[6, 112], [106, 20], [40, 13], [111, 8], [29, 11], [74, 86], [0, 1]], ![[0, 1], [0, 93], [5, 100], [46, 105], [95, 102], [25, 27], [6, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [91, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [63, 107, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44327, 11213, 680]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-41, 21, 680]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-13, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-13, 1, 0]] 
 ![![113, 0, 0], ![100, 1, 0], ![57, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-13, 1, 0], ![0, -13, 1], ![1162, 210, -13]]]
  hmulB := by decide  
  f := ![![![1210, -93, 0], ![10509, 0, 0]], ![![1080, -83, 0], ![9380, 0, 0]], ![![626, -48, 0], ![5437, 1, 0]]]
  g := ![![![1, 0, 0], ![-100, 113, 0], ![-57, 0, 113]], ![![-1, 1, 0], ![11, -13, 1], ![-169, 210, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-154, 13, 1]] ![![113, 0, 0], ![-13, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-1469, 113, 0]], ![![-17402, 1469, 113], ![3164, -113, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-13, 1, 0]]], ![![![-154, 13, 1]], ![![28, -1, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [10, 44, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 124, 69], [81, 2, 58], [0, 1]]
 g := ![![[25, 13, 124], [30, 63, 17], [114, 66, 121], [99, 24, 41], [121, 93, 113], [1]], ![[15, 92, 107, 122], [94, 97, 93, 107], [58, 45, 116, 47], [121, 67, 15, 42], [91, 42, 107, 64], [26, 42, 106, 87]], ![[101, 125, 48, 45], [116, 79, 112, 83], [81, 1, 2, 93], [36, 43, 36, 116], [87, 20, 99, 23], [75, 104, 89, 40]]]
 h' := ![![[4, 124, 69], [81, 91, 88], [3, 80, 12], [26, 20, 116], [60, 69, 101], [117, 83, 85], [0, 1]], ![[81, 2, 58], [91, 123, 105], [90, 68, 83], [55, 81, 88], [100, 57, 10], [58, 70, 55], [4, 124, 69]], ![[0, 1], [100, 40, 61], [31, 106, 32], [25, 26, 50], [28, 1, 16], [85, 101, 114], [81, 2, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 33], []]
 b := ![[], [95, 23, 121], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [10, 44, 42, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![605409, -120777, -30734]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4767, -951, -242]
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

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-198, 55, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-198, 55, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![64, 55, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-198, 55, 1], ![1162, 12, 55], ![63910, 12712, 12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -55, 131]], ![![-2, 0, 1], ![-18, -23, 55], ![482, 92, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [107, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 130], [0, 1]]
 g := ![![[59, 60], [96, 84], [58], [117], [105], [101], [1]], ![[0, 71], [92, 47], [58], [117], [105], [101], [1]]]
 h' := ![![[106, 130], [77, 45], [6, 52], [102, 78], [69, 36], [118, 74], [24, 106], [0, 1]], ![[0, 1], [0, 86], [16, 79], [117, 53], [86, 95], [102, 57], [125, 25], [106, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123]]
 b := ![[], [81, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [107, 25, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4755, 5513, 891]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-399, -332, 891]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-55, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-55, 1, 0]] 
 ![![131, 0, 0], ![76, 1, 0], ![119, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-55, 1, 0], ![0, -55, 1], ![1162, 210, -55]]]
  hmulB := by decide  
  f := ![![![5776, -105, 0], ![13755, 0, 0]], ![![3356, -61, 0], ![7992, 0, 0]], ![![5194, -94, 0], ![12369, 1, 0]]]
  g := ![![![1, 0, 0], ![-76, 131, 0], ![-119, 0, 131]], ![![-1, 1, 0], ![31, -55, 1], ![-63, 210, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-198, 55, 1]] ![![131, 0, 0], ![-55, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-7205, 131, 0]], ![![-25938, 7205, 131], ![12052, -3013, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-55, 1, 0]]], ![![![-198, 55, 1]], ![![92, -23, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [91, 113, 113, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 11, 134], [28, 125, 3], [0, 1]]
 g := ![![[125, 22, 34], [13, 49], [], [85, 55, 98], [119, 101], [24, 1], []], ![[126, 70, 70, 31], [132, 74], [91, 63], [134, 1, 63, 80], [0, 28], [63, 7], [13, 9]], ![[52, 114, 89, 111], [4, 107], [49, 63], [15, 83, 5, 131], [43, 99], [102, 121], [7, 9]]]
 h' := ![![[133, 11, 134], [66, 60, 87], [133, 5, 7], [74, 125], [58, 55, 80], [8, 74, 52], [0, 0, 1], [0, 1]], ![[28, 125, 3], [88, 133, 9], [27, 0, 38], [122, 5, 36], [49, 133, 108], [130, 14, 113], [66, 90, 125], [133, 11, 134]], ![[0, 1], [13, 81, 41], [69, 132, 92], [12, 7, 101], [69, 86, 86], [134, 49, 109], [10, 47, 11], [28, 125, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117, 27], []]
 b := ![[], [127, 127, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [91, 113, 113, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25172791, -1352738, 452374]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-183743, -9874, 3302]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB171I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB171I2 : PrimesBelowBoundCertificateInterval O 79 137 171 where
  m := 11
  g := ![3, 2, 2, 3, 2, 1, 2, 2, 1, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB171I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0, I131N1]
    · exact ![I137N0]
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
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![17161, 131]
    · exact ![2571353]
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
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N0, I83N1, I83N2, I89N1, I97N1, I101N0, I101N1, I101N2, I103N1, I109N1, I113N1, I131N1]
  Il := ![[I83N0, I83N1, I83N2], [I89N1], [I97N1], [I101N0, I101N1, I101N2], [I103N1], [], [I109N1], [I113N1], [], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
