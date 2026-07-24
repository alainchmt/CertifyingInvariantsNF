
import IdealArithmetic.Examples.NF3_1_662796_1.RI3_1_662796_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![27, 6, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![27, 6, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![27, 6, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![27, 6, 1], ![72, 16, 58], ![475, -125, -7]]]
  hmulB := by decide  
  f := ![![![-26, -6, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -6, 83]], ![![0, 0, 1], ![-18, -4, 58], ![8, -1, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [7, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 82], [0, 1]]
 g := ![![[39, 12], [65, 81], [29], [3], [41, 78], [1]], ![[0, 71], [30, 2], [29], [3], [78, 5], [1]]]
 h' := ![![[59, 82], [43, 26], [24, 9], [12, 19], [45, 13], [76, 59], [0, 1]], ![[0, 1], [0, 57], [57, 74], [54, 64], [65, 70], [71, 24], [59, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [46, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [7, 24, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![979, -179, -680]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![233, 47, -680]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![25, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![25, 1, 0]] 
 ![![83, 0, 0], ![25, 1, 0], ![7, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![25, 1, 0], ![-2, 27, 10], ![84, -23, 23]]]
  hmulB := by decide  
  f := ![![![-1034, 14311, 5300], ![-83, -43990, 0]], ![![-318, 4293, 1590], ![1, -13197, 0]], ![![-86, 1207, 447], ![-11, -3710, 0]]]
  g := ![![![1, 0, 0], ![-25, 83, 0], ![-7, 0, 83]], ![![0, 1, 0], ![-9, 27, 10], ![6, -23, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![27, 6, 1]] ![![83, 0, 0], ![25, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![2075, 83, 0]], ![![2241, 498, 83], ![747, 166, 83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![25, 1, 0]]], ![![![27, 6, 1]], ![![9, 2, 1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![5, -29, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![5, -29, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![5, 60, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![5, -29, 1], ![142, -76, -292], ![-2465, 680, 41]]]
  hmulB := by decide  
  f := ![![![-4, 29, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -60, 89]], ![![0, -1, 1], ![18, 196, -292], ![-30, -20, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [24, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 88], [0, 1]]
 g := ![![[43, 53], [10], [42], [12, 11], [72, 50], [1]], ![[82, 36], [10], [42], [52, 78], [3, 39], [1]]]
 h' := ![![[36, 88], [48, 26], [56, 59], [68, 24], [52, 10], [65, 36], [0, 1]], ![[0, 1], [5, 63], [44, 30], [42, 65], [56, 79], [26, 53], [36, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [65, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [24, 53, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5810, 2548, -3654]
  a := ![-3, 0, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![140, 2492, -3654]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![25, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![25, 1, 0]] 
 ![![89, 0, 0], ![25, 1, 0], ![48, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![25, 1, 0], ![-2, 27, 10], ![84, -23, 23]]]
  hmulB := by decide  
  f := ![![![8479, -118515, -43890], ![1068, 390621, 0]], ![![2364, -33268, -12320], ![357, 109648, 0]], ![![4553, -63919, -23671], ![647, 210672, 0]]]
  g := ![![![1, 0, 0], ![-25, 89, 0], ![-48, 0, 89]], ![![0, 1, 0], ![-13, 27, 10], ![-5, -23, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![5, -29, 1]] ![![89, 0, 0], ![25, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![2225, 89, 0]], ![![445, -2581, 89], ![267, -801, -267]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![25, 1, 0]]], ![![![5, -29, 1]], ![![3, -9, -3]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![47, 46, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![47, 46, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![47, 46, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![47, 46, 1], ![-8, 116, 458], ![3835, -1045, -67]]]
  hmulB := by decide  
  f := ![![![-46, -46, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -46, 97]], ![![0, 0, 1], ![-222, -216, 458], ![72, 21, -67]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [5, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 96], [0, 1]]
 g := ![![[28, 11], [72], [18], [1], [1], [54, 1]], ![[40, 86], [72], [18], [1], [1], [11, 96]]]
 h' := ![![[54, 96], [71, 37], [72, 13], [68, 55], [48, 96], [21, 1], [0, 1]], ![[0, 1], [32, 60], [95, 84], [31, 42], [91, 1], [75, 96], [54, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [10, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [5, 43, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![595676, -135931, -84551]
  a := ![1, -64, -69]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![47109, 38695, -84551]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![27, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![27, 1, 0]] 
 ![![97, 0, 0], ![27, 1, 0], ![67, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![27, 1, 0], ![-2, 29, 10], ![84, -23, 25]]]
  hmulB := by decide  
  f := ![![![-107, 1566, 540], ![0, -5238, 0]], ![![-30, 435, 150], ![1, -1455, 0]], ![![-92, 1081, 373], ![65, -3618, 0]]]
  g := ![![![1, 0, 0], ![-27, 97, 0], ![-67, 0, 97]], ![![0, 1, 0], ![-15, 29, 10], ![-10, -23, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![47, 46, 1]] ![![97, 0, 0], ![27, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![2619, 97, 0]], ![![4559, 4462, 97], ![1261, 1358, 485]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![27, 1, 0]]], ![![![47, 46, 1]], ![![13, 14, 5]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![35, 32, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![35, 32, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![35, 32, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![35, 32, 1], ![20, 76, 318], ![2659, -723, -51]]]
  hmulB := by decide  
  f := ![![![-34, -32, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -32, 101]], ![![0, 0, 1], ![-110, -100, 318], ![44, 9, -51]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [10, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 100], [0, 1]]
 g := ![![[77, 30], [1], [], [], [97], [38, 1]], ![[5, 71], [1], [], [], [97], [76, 100]]]
 h' := ![![[38, 100], [91, 38], [0, 1], [100], [10], [24, 20], [0, 1]], ![[0, 1], [20, 63], [38, 100], [100], [10], [77, 81], [38, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [77, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [10, 63, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3126, 1837, -5324]
  a := ![3, -1, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1814, 1705, -5324]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-15, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-15, 1, 0]] 
 ![![101, 0, 0], ![86, 1, 0], ![51, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-15, 1, 0], ![-2, -13, 10], ![84, -23, -17]]]
  hmulB := by decide  
  f := ![![![14340, 94287, -72520], ![-1111, 732452, 0]], ![![12199, 80272, -61740], ![-1009, 623574, 0]], ![![7245, 47610, -36619], ![-534, 369852, 0]]]
  g := ![![![1, 0, 0], ![-86, 101, 0], ![-51, 0, 101]], ![![-1, 1, 0], ![6, -13, 10], ![29, -23, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![35, 32, 1]] ![![101, 0, 0], ![-15, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-1515, 101, 0]], ![![3535, 3232, 101], ![-505, -404, 303]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-15, 1, 0]]], ![![![35, 32, 1]], ![![-5, -4, 3]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [96, 22, 81, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 57, 70], [56, 45, 33], [0, 1]]
 g := ![![[54, 14, 97], [85, 77, 81], [1, 0, 59], [86, 41], [101, 72], [1]], ![[46, 62, 43, 57], [4, 102, 22, 6], [10, 98, 101, 57], [12, 93], [24, 92], [100, 55, 9, 10]], ![[3, 33, 10, 91], [13, 85, 27, 18], [58, 66, 32, 13], [86, 58], [1, 66], [3, 0, 20, 93]]]
 h' := ![![[69, 57, 70], [80, 57, 32], [7, 89, 94], [76, 54, 70], [35, 34, 91], [7, 81, 22], [0, 1]], ![[56, 45, 33], [52, 101, 74], [81, 23, 57], [62, 80, 29], [94, 80, 89], [21, 58, 68], [69, 57, 70]], ![[0, 1], [95, 48, 100], [94, 94, 55], [45, 72, 4], [79, 92, 26], [22, 67, 13], [56, 45, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 21], []]
 b := ![[], [96, 74, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [96, 22, 81, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![145230, -16583, -113300]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1410, -161, -1100]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [103, 85, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 7, 103], [45, 99, 4], [0, 1]]
 g := ![![[81, 28, 92], [66, 27, 13], [92, 36], [32, 62, 23], [33, 57], [1]], ![[59, 69, 74, 60], [73, 50, 32, 58], [65, 4], [33, 24, 83, 22], [31, 10], [28, 35, 46, 43]], ![[75, 23], [76, 2, 7, 47], [74, 16], [12, 42, 83, 76], [51, 16], [62, 38, 13, 64]]]
 h' := ![![[3, 7, 103], [50, 24, 78], [60, 83, 86], [21, 65, 101], [41, 60, 68], [4, 22, 48], [0, 1]], ![[45, 99, 4], [87, 49, 29], [18, 41, 50], [87, 102, 2], [78, 105, 72], [32, 89, 63], [3, 7, 103]], ![[0, 1], [55, 34], [39, 90, 78], [8, 47, 4], [15, 49, 74], [102, 103, 103], [45, 99, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 65], []]
 b := ![[], [4, 81, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [103, 85, 59, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3974836, -679878, -1132488]
  a := ![-1, 21, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![37148, -6354, -10584]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![26, 13, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![26, 13, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![26, 13, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![26, 13, 1], ![58, 29, 128], ![1063, -286, -22]]]
  hmulB := by decide  
  f := ![![![-25, -13, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -13, 109]], ![![0, 0, 1], ![-30, -15, 128], ![15, 0, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [49, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 108], [0, 1]]
 g := ![![[22, 89], [3], [19, 60], [11, 46], [87], [12, 1]], ![[0, 20], [3], [85, 49], [18, 63], [87], [24, 108]]]
 h' := ![![[12, 108], [64, 31], [50, 49], [6, 96], [93, 68], [66, 95], [0, 1]], ![[0, 1], [0, 78], [93, 60], [68, 13], [37, 41], [7, 14], [12, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [92, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [49, 97, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1907, 845, -1352]
  a := ![1, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![305, 169, -1352]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-19, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-19, 1, 0]] 
 ![![109, 0, 0], ![90, 1, 0], ![22, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-19, 1, 0], ![-2, -17, 10], ![84, -23, -21]]]
  hmulB := by decide  
  f := ![![![7627, 65796, -38700], ![-654, 421830, 0]], ![![6296, 54320, -31950], ![-544, 348255, 0]], ![![1538, 13280, -7811], ![-140, 85140, 0]]]
  g := ![![![1, 0, 0], ![-90, 109, 0], ![-22, 0, 109]], ![![-1, 1, 0], ![12, -17, 10], ![24, -23, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![26, 13, 1]] ![![109, 0, 0], ![-19, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-2071, 109, 0]], ![![2834, 1417, 109], ![-436, -218, 109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-19, 1, 0]]], ![![![26, 13, 1]], ![![-4, -2, 1]]]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [100, 97, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 22, 24], [13, 90, 89], [0, 1]]
 g := ![![[103, 78, 63], [95, 97], [33, 32], [80, 72], [46, 34, 16], [1]], ![[22, 61, 99, 39], [21, 14], [88, 9], [2, 32], [37, 104, 88, 38], [37, 55, 9, 38]], ![[30, 43, 8, 74], [81, 9], [74, 60], [63, 87], [8, 42, 18, 5], [76, 95, 71, 75]]]
 h' := ![![[96, 22, 24], [80, 23, 17], [75, 69, 60], [95, 40, 91], [33, 104, 80], [13, 16, 109], [0, 1]], ![[13, 90, 89], [107, 48, 48], [25, 81, 50], [24, 17, 110], [26, 33, 91], [88, 41, 24], [96, 22, 24]], ![[0, 1], [99, 42, 48], [17, 76, 3], [80, 56, 25], [74, 89, 55], [21, 56, 93], [13, 90, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 109], []]
 b := ![[], [52, 47, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [100, 97, 4, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28702, -115373, 529970]
  a := ![-2, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![254, -1021, 4690]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [102, 126, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 99, 16], [6, 27, 111], [0, 1]]
 g := ![![[24, 86, 79], [115, 110, 4], [64, 48, 44], [42, 121, 17], [76, 64, 79], [1]], ![[45, 59, 72, 70], [61, 27, 38, 103], [71, 23, 112, 107], [23, 117, 89, 11], [16, 20, 107, 19], [45, 23, 47, 32]], ![[121, 86, 64, 78], [73, 22, 111, 116], [73, 93, 44, 54], [104, 96, 0, 57], [73, 70, 40, 46], [29, 77, 74, 95]]]
 h' := ![![[92, 99, 16], [81, 5, 98], [76, 7, 125], [34, 44, 67], [122, 15, 12], [25, 1, 98], [0, 1]], ![[6, 27, 111], [76, 97, 59], [123, 105, 58], [15, 51, 100], [4, 60, 56], [33, 82, 122], [92, 99, 16]], ![[0, 1], [5, 25, 97], [45, 15, 71], [13, 32, 87], [15, 52, 59], [52, 44, 34], [6, 27, 111]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 124], []]
 b := ![[], [72, 40, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [102, 126, 29, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![527177, -141605, -46355]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4151, -1115, -365]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [21, 115, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 32, 22], [85, 98, 109], [0, 1]]
 g := ![![[55, 77, 64], [36, 121, 91], [112, 65], [39, 53], [123, 52], [109, 1], []], ![[22, 11, 95, 30], [90, 51, 99, 98], [63, 1], [60, 108], [104, 58], [42, 41], [61, 91]], ![[42, 113, 8, 109], [58, 128, 15, 112], [17, 94], [25, 117], [102, 55], [54, 107], [105, 91]]]
 h' := ![![[24, 32, 22], [30, 101, 8], [106, 50, 109], [10, 27, 14], [82, 99, 61], [69, 20, 107], [0, 0, 1], [0, 1]], ![[85, 98, 109], [89, 49, 124], [48, 37, 123], [89, 108, 1], [63, 5, 34], [46, 102, 53], [81, 77, 98], [24, 32, 22]], ![[0, 1], [43, 112, 130], [26, 44, 30], [11, 127, 116], [55, 27, 36], [106, 9, 102], [42, 54, 32], [85, 98, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 37], []]
 b := ![[], [89, 76, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [21, 115, 22, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7246527, -2072682, -42444]
  a := ![-2, -6, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![55317, -15822, -324]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-39, 36, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-39, 36, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![98, 36, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-39, 36, 1], ![12, 10, 358], ![2995, -815, -133]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-98, -36, 137]], ![![-1, 0, 1], ![-256, -94, 358], ![117, 29, -133]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [9, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 136], [0, 1]]
 g := ![![[113, 61], [101], [37], [113, 93], [22], [76], [1]], ![[0, 76], [101], [37], [62, 44], [22], [76], [1]]]
 h' := ![![[79, 136], [65, 46], [17, 85], [79, 41], [87, 97], [82, 61], [128, 79], [0, 1]], ![[0, 1], [0, 91], [19, 52], [30, 96], [78, 40], [106, 76], [67, 58], [79, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [115, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [9, 58, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29530, -5486, -5366]
  a := ![-1, 13, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4054, 1370, -5366]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![53, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![53, 1, 0]] 
 ![![137, 0, 0], ![53, 1, 0], ![133, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![53, 1, 0], ![-2, 55, 10], ![84, -23, 51]]]
  hmulB := by decide  
  f := ![![![19452, -571365, -103880], ![3425, 1423156, 0]], ![![7506, -221000, -40180], ![1371, 550466, 0]], ![![18874, -554683, -100847], ![3351, 1381604, 0]]]
  g := ![![![1, 0, 0], ![-53, 137, 0], ![-133, 0, 137]], ![![0, 1, 0], ![-31, 55, 10], ![-40, -23, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-39, 36, 1]] ![![137, 0, 0], ![53, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![7261, 137, 0]], ![![-5343, 4932, 137], ![-2055, 1918, 411]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![53, 1, 0]]], ![![![-39, 36, 1]], ![![-15, 14, 3]]]]
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


lemma PB231I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB231I2 : PrimesBelowBoundCertificateInterval O 79 137 231 where
  m := 11
  g := ![2, 2, 2, 2, 1, 1, 2, 1, 1, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB231I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![2048383]
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
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I97N1, I101N1, I109N1, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N1], [], [], [I109N1], [], [], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
