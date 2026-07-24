
import IdealArithmetic.Examples.NF3_1_672300_4.RI3_1_672300_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![13, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![13, 1, 0]] 
 ![![83, 0, 0], ![13, 1, 0], ![61, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![13, 1, 0], ![2, 12, 7], ![156, -9, 14]]]
  hmulB := by decide  
  f := ![![![-498, -3071, -1792], ![-83, 21248, 0]], ![![-80, -480, -280], ![1, 3320, 0]], ![![-366, -2257, -1317], ![-61, 15616, 0]]]
  g := ![![![1, 0, 0], ![-13, 83, 0], ![-61, 0, 83]], ![![0, 1, 0], ![-7, 12, 7], ![-7, -9, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![35, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![35, 1, 0]] 
 ![![83, 0, 0], ![35, 1, 0], ![20, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![35, 1, 0], ![2, 34, 7], ![156, -9, 36]]]
  hmulB := by decide  
  f := ![![![-622, -13561, -2793], ![-415, 33117, 0]], ![![-266, -5710, -1176], ![-165, 13944, 0]], ![![-160, -3268, -673], ![-76, 7980, 0]]]
  g := ![![![1, 0, 0], ![-35, 83, 0], ![-20, 0, 83]], ![![0, 1, 0], ![-16, 34, 7], ![-3, -9, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![13, 1, 0]] ![![83, 0, 0], ![35, 1, 0]]
  ![![83, 0, 0], ![6, -17, 1]] where
 M := ![![![6889, 0, 0], ![2905, 83, 0]], ![![1079, 83, 0], ![457, 47, 7]]]
 hmul := by decide  
 g := ![![![![77, 17, -1], ![83, 0, 0]], ![![29, 18, -1], ![83, 0, 0]]], ![![![7, 18, -1], ![83, 0, 0]], ![![5, 2, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![6, -17, 1]] ![![83, 0, 0], ![35, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![2905, 83, 0]], ![![498, -1411, 83], ![332, -581, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![35, 1, 0]]], ![![![6, -17, 1]], ![![4, -7, -1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3871, 216, 205]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![3871, 216, 205]] 
 ![![89, 0, 0], ![0, 89, 0], ![28, 8, 1]] where
  M :=![![![3871, 216, 205], ![32412, 1810, 1717], ![42306, 2361, 2242]]]
  hmulB := by decide  
  f := ![![![47, -3, -2]], ![![-318, 68, -23]], ![![-20, 5, -2]]]
  g := ![![![-21, -16, 205], ![-176, -134, 1717], ![-230, -175, 2242]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [72, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 88], [0, 1]]
 g := ![![[34, 68], [49], [47], [16, 49], [83, 67], [1]], ![[0, 21], [49], [47], [36, 40], [5, 22], [1]]]
 h' := ![![[44, 88], [27, 54], [23, 82], [5, 15], [76, 7], [17, 44], [0, 1]], ![[0, 1], [0, 35], [71, 7], [42, 74], [28, 82], [84, 45], [44, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [59, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [72, 45, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2044, 1029, -728]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![252, 77, -728]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, -3, -2]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![47, -3, -2]] 
 ![![89, 0, 0], ![32, 1, 0], ![62, 0, 1]] where
  M :=![![![47, -3, -2], ![-318, 68, -23], ![-552, -15, 62]]]
  hmulB := by decide  
  f := ![![![3871, 216, 205]], ![![1756, 98, 93]], ![![3172, 177, 168]]]
  g := ![![![3, -3, -2], ![-12, 68, -23], ![-44, -15, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![3871, 216, 205]] ![![47, -3, -2]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-26, -40, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-26, -40, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![71, 57, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-26, -40, 1], ![76, 5, -279], ![-6198, 381, -75]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -57, 97]], ![![-1, -1, 1], ![205, 164, -279], ![-9, 48, -75]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [52, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 96], [0, 1]]
 g := ![![[61, 49], [33], [88], [88], [72], [29, 1]], ![[27, 48], [33], [88], [88], [72], [58, 96]]]
 h' := ![![[29, 96], [83, 7], [76, 18], [44, 66], [35, 31], [44, 13], [0, 1]], ![[0, 1], [92, 90], [16, 79], [18, 31], [61, 66], [33, 84], [29, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [31, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [52, 68, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14005, 8009, -1517]
  a := ![5, -5, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![966, 974, -1517]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-12, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-12, 1, 0]] 
 ![![97, 0, 0], ![85, 1, 0], ![75, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-12, 1, 0], ![2, -13, 7], ![156, -9, -11]]]
  hmulB := by decide  
  f := ![![![-1355, 9045, -4872], ![291, 67512, 0]], ![![-1181, 7914, -4263], ![292, 59073, 0]], ![![-1041, 6993, -3767], ![279, 52200, 0]]]
  g := ![![![1, 0, 0], ![-85, 97, 0], ![-75, 0, 97]], ![![-1, 1, 0], ![6, -13, 7], ![18, -9, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-26, -40, 1]] ![![97, 0, 0], ![-12, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-1164, 97, 0]], ![![-2522, -3880, 97], ![388, 485, -291]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-12, 1, 0]]], ![![![-26, -40, 1]], ![![4, 5, -3]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-2, 28, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-2, 28, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![99, 28, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-2, 28, 1], ![212, -39, 197], ![4410, -231, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-99, -28, 101]], ![![-1, 0, 1], ![-191, -55, 197], ![27, -7, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [2, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [76, 100], [0, 1]]
 g := ![![[63, 33], [4], [29, 1], [92], [87], [76, 1]], ![[46, 68], [4], [4, 100], [92], [87], [51, 100]]]
 h' := ![![[76, 100], [23, 72], [43, 2], [27, 1], [3, 30], [50, 17], [0, 1]], ![[0, 1], [41, 29], [94, 99], [2, 100], [61, 71], [29, 84], [76, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [62, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [2, 25, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1541782, 838567, -335884]
  a := ![-66, 2, -199]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![344498, 101419, -335884]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![5, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![5, 1, 0]] 
 ![![101, 0, 0], ![5, 1, 0], ![84, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![5, 1, 0], ![2, 4, 7], ![156, -9, 6]]]
  hmulB := by decide  
  f := ![![![10010, 20081, 35154], ![707, -507222, 0]], ![![491, 991, 1736], ![102, -25048, 0]], ![![8325, 16701, 29237], ![591, -421848, 0]]]
  g := ![![![1, 0, 0], ![-5, 101, 0], ![-84, 0, 101]], ![![0, 1, 0], ![-6, 4, 7], ![-3, -9, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-2, 28, 1]] ![![101, 0, 0], ![5, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![505, 101, 0]], ![![-202, 2828, 101], ![202, 101, 202]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![5, 1, 0]]], ![![![-2, 28, 1]], ![![2, 1, 2]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![42, -37, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![42, -37, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![42, 66, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![42, -37, 1], ![82, 70, -258], ![-5730, 354, -4]]]
  hmulB := by decide  
  f := ![![![-41, 37, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -66, 103]], ![![0, -1, 1], ![106, 166, -258], ![-54, 6, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [82, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 102], [0, 1]]
 g := ![![[95, 49], [56, 4], [60, 58], [56], [14], [38, 1]], ![[0, 54], [2, 99], [101, 45], [56], [14], [76, 102]]]
 h' := ![![[38, 102], [43, 7], [24, 101], [38, 26], [43, 57], [77, 23], [0, 1]], ![[0, 1], [0, 96], [51, 2], [99, 77], [46, 46], [24, 80], [38, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [22, 91]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [82, 65, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9042, 8304, -3938]
  a := ![-5, 4, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1518, 2604, -3938]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-51, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-51, 1, 0]] 
 ![![103, 0, 0], ![52, 1, 0], ![4, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-51, 1, 0], ![2, -52, 7], ![156, -9, -50]]]
  hmulB := by decide  
  f := ![![![-81, 4782, -644], ![206, 9476, 0]], ![![-40, 2391, -322], ![104, 4738, 0]], ![![33, 185, -25], ![81, 368, 0]]]
  g := ![![![1, 0, 0], ![-52, 103, 0], ![-4, 0, 103]], ![![-1, 1, 0], ![26, -52, 7], ![8, -9, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![42, -37, 1]] ![![103, 0, 0], ![-51, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-5253, 103, 0]], ![![4326, -3811, 103], ![-2060, 1957, -309]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-51, 1, 0]]], ![![![42, -37, 1]], ![![-20, 19, -3]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-13, 35, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-13, 35, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![94, 35, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-13, 35, 1], ![226, -57, 246], ![5502, -294, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-94, -35, 107]], ![![-1, 0, 1], ![-214, -81, 246], ![40, -7, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [83, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 106], [0, 1]]
 g := ![![[49, 49], [85, 85], [9], [88, 36], [90], [106, 1]], ![[0, 58], [0, 22], [9], [52, 71], [90], [105, 106]]]
 h' := ![![[106, 106], [7, 7], [37, 37], [79, 3], [61, 101], [83, 25], [0, 1]], ![[0, 1], [0, 100], [0, 70], [76, 104], [67, 6], [58, 82], [106, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [75, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [83, 1, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2143, 1029, -420]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![389, 147, -420]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-32, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-32, 1, 0]] 
 ![![107, 0, 0], ![75, 1, 0], ![94, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-32, 1, 0], ![2, -33, 7], ![156, -9, -31]]]
  hmulB := by decide  
  f := ![![![-1811, 34641, -7350], ![963, 112350, 0]], ![![-1277, 24249, -5145], ![643, 78645, 0]], ![![-1614, 30433, -6457], ![769, 98700, 0]]]
  g := ![![![1, 0, 0], ![-75, 107, 0], ![-94, 0, 107]], ![![-1, 1, 0], ![17, -33, 7], ![35, -9, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-13, 35, 1]] ![![107, 0, 0], ![-32, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-3424, 107, 0]], ![![-1391, 3745, 107], ![642, -1177, 214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-32, 1, 0]]], ![![![-13, 35, 1]], ![![6, -11, 2]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![0, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![0, 1, 0]] 
 ![![109, 0, 0], ![0, 1, 0], ![47, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![0, 1, 0], ![2, -1, 7], ![156, -9, 1]]]
  hmulB := by decide  
  f := ![![![-109, 54, -385], ![109, 5995, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-47, 23, -166], ![78, 2585, 0]]]
  g := ![![![1, 0, 0], ![0, 109, 0], ![-47, 0, 109]], ![![0, 1, 0], ![-3, -1, 7], ![1, -9, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![7, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![7, 1, 0]] 
 ![![109, 0, 0], ![7, 1, 0], ![41, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![7, 1, 0], ![2, 6, 7], ![156, -9, 8]]]
  hmulB := by decide  
  f := ![![![15659, 47254, 55146], ![1526, -858702, 0]], ![![1003, 3029, 3535], ![110, -55045, 0]], ![![5887, 17774, 20743], ![622, -322998, 0]]]
  g := ![![![1, 0, 0], ![-7, 109, 0], ![-41, 0, 109]], ![![0, 1, 0], ![-3, 6, 7], ![-1, -9, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-7, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-7, 1, 0]] 
 ![![109, 0, 0], ![102, 1, 0], ![39, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-7, 1, 0], ![2, -8, 7], ![156, -9, -6]]]
  hmulB := by decide  
  f := ![![![-5847, 23554, -20615], ![654, 321005, 0]], ![![-5467, 22034, -19285], ![655, 300295, 0]], ![![-2088, 8427, -7376], ![297, 114855, 0]]]
  g := ![![![1, 0, 0], ![-102, 109, 0], ![-39, 0, 109]], ![![-1, 1, 0], ![5, -8, 7], ![12, -9, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![0, 1, 0]] ![![109, 0, 0], ![7, 1, 0]]
  ![![109, 0, 0], ![47, 32, 1]] where
 M := ![![![11881, 0, 0], ![763, 109, 0]], ![![0, 109, 0], ![2, 6, 7]]]
 hmul := by decide  
 g := ![![![![62, -32, -1], ![109, 0, 0]], ![![-40, -31, -1], ![109, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-3, -2, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![47, 32, 1]] ![![109, 0, 0], ![-7, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-763, 109, 0]], ![![5123, 3488, 109], ![-109, -218, 218]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-7, 1, 0]]], ![![![47, 32, 1]], ![![-1, -2, 2]]]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [51, 94, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 26, 106], [71, 86, 7], [0, 1]]
 g := ![![[69, 38, 14], [32, 8], [26, 22], [109, 28], [47, 95, 87], [1]], ![[103, 96, 101, 50], [94, 106], [102, 85], [17, 4], [4, 59, 6, 81], [57, 8, 99, 109]], ![[39, 81, 97, 1], [47, 52], [16, 88], [6, 62], [25, 9, 77, 41], [109, 88, 93, 4]]]
 h' := ![![[97, 26, 106], [38, 48, 63], [38, 111, 102], [102, 64, 19], [89, 5, 49], [62, 19, 55], [0, 1]], ![[71, 86, 7], [54, 4, 110], [21, 54, 85], [5, 53, 56], [104, 79, 111], [3, 77, 77], [97, 26, 106]], ![[0, 1], [28, 61, 53], [39, 61, 39], [105, 109, 38], [33, 29, 66], [18, 17, 94], [71, 86, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 69], []]
 b := ![[], [35, 85, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [51, 94, 58, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7329858, 1249554, 407026]
  a := ![3, 18, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![64866, 11058, 3602]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [31, 22, 83, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 75, 76], [38, 51, 51], [0, 1]]
 g := ![![[8, 84, 117], [68, 23, 117], [97, 103, 18], [84, 13, 17], [100, 63, 31], [1]], ![[77, 114, 95, 60], [84, 71, 98, 16], [97, 76, 104, 88], [20, 77, 37, 76], [16, 66, 118, 19], [61, 92, 31, 64]], ![[71, 101, 95, 28], [26, 29, 75, 110], [105, 18, 41, 97], [42, 9, 106, 75], [120, 8, 45, 123], [2, 24, 40, 63]]]
 h' := ![![[6, 75, 76], [51, 107, 25], [41, 39, 102], [63, 72, 79], [75, 110, 115], [96, 105, 44], [0, 1]], ![[38, 51, 51], [111, 52, 9], [95, 103, 38], [124, 124, 103], [39, 73, 1], [103, 96, 64], [6, 75, 76]], ![[0, 1], [56, 95, 93], [123, 112, 114], [111, 58, 72], [27, 71, 11], [73, 53, 19], [38, 51, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101, 13], []]
 b := ![[], [71, 105, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [31, 22, 83, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5138547, 627380, -8382]
  a := ![-3, 4, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-40461, 4940, -66]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![39, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![39, 1, 0]] 
 ![![131, 0, 0], ![39, 1, 0], ![88, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![39, 1, 0], ![2, 38, 7], ![156, -9, 40]]]
  hmulB := by decide  
  f := ![![![-19226, -414893, -76440], ![-8777, 1430520, 0]], ![![-5720, -123480, -22750], ![-2619, 425750, 0]], ![![-12925, -278707, -51349], ![-5863, 960960, 0]]]
  g := ![![![1, 0, 0], ![-39, 131, 0], ![-88, 0, 131]], ![![0, 1, 0], ![-16, 38, 7], ![-23, -9, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-35, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-35, 1, 0]] 
 ![![131, 0, 0], ![96, 1, 0], ![101, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-35, 1, 0], ![2, -36, 7], ![156, -9, -34]]]
  hmulB := by decide  
  f := ![![![22769, -455112, 88508], ![-9432, -1656364, 0]], ![![16676, -333487, 64855], ![-6942, -1213715, 0]], ![![17559, -350888, 68239], ![-7256, -1277044, 0]]]
  g := ![![![1, 0, 0], ![-96, 131, 0], ![-101, 0, 131]], ![![-1, 1, 0], ![21, -36, 7], ![34, -9, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-4, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-4, 1, 0]] 
 ![![131, 0, 0], ![127, 1, 0], ![91, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-4, 1, 0], ![2, -5, 7], ![156, -9, -3]]]
  hmulB := by decide  
  f := ![![![11353, -28416, 39788], ![-524, -744604, 0]], ![![11005, -27546, 38570], ![-523, -721810, 0]], ![![7889, -19740, 27639], ![-280, -517244, 0]]]
  g := ![![![1, 0, 0], ![-127, 131, 0], ![-91, 0, 131]], ![![-1, 1, 0], ![0, -5, 7], ![12, -9, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![39, 1, 0]] ![![131, 0, 0], ![-35, 1, 0]]
  ![![131, 0, 0], ![-45, -37, 1]] where
 M := ![![![17161, 0, 0], ![-4585, 131, 0]], ![![5109, 131, 0], ![-1363, 3, 7]]]
 hmul := by decide  
 g := ![![![![131, 0, 0], ![0, 0, 0]], ![![10, 38, -1], ![131, 0, 0]]], ![![![39, 1, 0], ![0, 0, 0]], ![![-8, 2, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-45, -37, 1]] ![![131, 0, 0], ![-4, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-524, 131, 0]], ![![-5895, -4847, 131], ![262, 131, -262]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-4, 1, 0]]], ![![![-45, -37, 1]], ![![2, 1, -2]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![56, 67, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![56, 67, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![56, 67, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![56, 67, 1], ![290, -20, 470], ![10494, -582, 114]]]
  hmulB := by decide  
  f := ![![![-55, -67, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -67, 137]], ![![0, 0, 1], ![-190, -230, 470], ![30, -60, 114]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [111, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 136], [0, 1]]
 g := ![![[], [], [88], [], [], [], [1]], ![[], [], [88], [], [], [], [1]]]
 h' := ![![[0, 136], [37], [96], [0, 122], [81], [128], [26], [0, 1]], ![[0, 1], [37], [96], [0, 15], [81], [128], [26], [0, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [0, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [111, 0, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3993, 4359, -1673]
  a := ![4, -1, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![713, 850, -1673]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-59, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-59, 1, 0]] 
 ![![137, 0, 0], ![78, 1, 0], ![23, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-59, 1, 0], ![2, -60, 7], ![156, -9, -58]]]
  hmulB := by decide  
  f := ![![![3087, -120884, 14105], ![-2192, -276055, 0]], ![![1764, -68811, 8029], ![-1232, -157139, 0]], ![![554, -20295, 2368], ![-285, -46345, 0]]]
  g := ![![![1, 0, 0], ![-78, 137, 0], ![-23, 0, 137]], ![![-1, 1, 0], ![33, -60, 7], ![16, -9, -58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![56, 67, 1]] ![![137, 0, 0], ![-59, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-8083, 137, 0]], ![![7672, 9179, 137], ![-3014, -3973, 411]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-59, 1, 0]]], ![![![56, 67, 1]], ![![-22, -29, 3]]]]
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


lemma PB233I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB233I2 : PrimesBelowBoundCertificateInterval O 79 137 233 where
  m := 11
  g := ![3, 2, 2, 2, 2, 2, 3, 1, 1, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB233I2_primes
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
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
    · exact ![I127N0]
    · exact ![I131N0, I131N1, I131N2]
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
    · exact ![109, 109, 109]
    · exact ![1442897]
    · exact ![2048383]
    · exact ![131, 131, 131]
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
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N0, I83N1, I89N1, I97N1, I101N1, I103N1, I107N1, I109N0, I109N1, I109N2, I131N0, I131N1, I131N2, I137N1]
  Il := ![[I83N0, I83N1, I83N1], [I89N1], [I97N1], [I101N1], [I103N1], [I107N1], [I109N0, I109N1, I109N2], [], [], [I131N0, I131N1, I131N2], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
