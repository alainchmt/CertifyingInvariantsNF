
import IdealArithmetic.Examples.NF3_1_644799_1.RI3_1_644799_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![10, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![10, 1, 0]] 
 ![![83, 0, 0], ![10, 1, 0], ![0, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![10, 1, 0], ![-3, 8, 9], ![-156, 1, 13]]]
  hmulB := by decide  
  f := ![![![-9, -1, 0], ![83, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-3, -4, -4], ![36, 37, 0]]]
  g := ![![![1, 0, 0], ![-10, 83, 0], ![0, 0, 83]], ![![0, 1, 0], ![-1, 8, 9], ![-2, 1, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![30, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![30, 1, 0]] 
 ![![83, 0, 0], ![30, 1, 0], ![17, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![30, 1, 0], ![-3, 28, 9], ![-156, 1, 33]]]
  hmulB := by decide  
  f := ![![![3559, -36299, -11664], ![913, 107568, 0]], ![![1284, -13108, -4212], ![333, 38844, 0]], ![![721, -7435, -2389], ![209, 22032, 0]]]
  g := ![![![1, 0, 0], ![-30, 83, 0], ![-17, 0, 83]], ![![0, 1, 0], ![-12, 28, 9], ![-9, 1, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-41, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-41, 1, 0]] 
 ![![83, 0, 0], ![42, 1, 0], ![62, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-41, 1, 0], ![-3, -43, 9], ![-156, 1, -38]]]
  hmulB := by decide  
  f := ![![![55, 774, -162], ![0, 1494, 0]], ![![28, 387, -81], ![1, 747, 0]], ![![48, 578, -121], ![14, 1116, 0]]]
  g := ![![![1, 0, 0], ![-42, 83, 0], ![-62, 0, 83]], ![![-1, 1, 0], ![15, -43, 9], ![26, 1, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![10, 1, 0]] ![![83, 0, 0], ![30, 1, 0]]
  ![![83, 0, 0], ![33, -5, 1]] where
 M := ![![![6889, 0, 0], ![2490, 83, 0]], ![![830, 83, 0], ![297, 38, 9]]]
 hmul := by decide  
 g := ![![![![50, 5, -1], ![83, 0, 0]], ![![-3, 6, -1], ![83, 0, 0]]], ![![![-23, 6, -1], ![83, 0, 0]], ![![0, 1, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![33, -5, 1]] ![![83, 0, 0], ![-41, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-3403, 83, 0]], ![![2739, -415, 83], ![-1494, 249, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-41, 1, 0]]], ![![![33, -5, 1]], ![![-18, 3, -1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![17, -27, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![17, -27, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![17, 62, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![17, -27, 1], ![-75, 72, -240], ![4125, -44, -61]]]
  hmulB := by decide  
  f := ![![![-16, 27, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -62, 89]], ![![0, -1, 1], ![45, 168, -240], ![58, 42, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [38, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 88], [0, 1]]
 g := ![![[86, 44], [49], [39], [65, 53], [19, 2], [1]], ![[29, 45], [49], [39], [55, 36], [69, 87], [1]]]
 h' := ![![[25, 88], [12, 69], [70, 7], [22, 67], [79, 63], [51, 25], [0, 1]], ![[0, 1], [46, 20], [67, 82], [6, 22], [52, 26], [53, 64], [25, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [74, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [38, 64, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5179, -3711, -624]
  a := ![5, 3, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![61, 393, -624]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-27, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-27, 1, 0]] 
 ![![89, 0, 0], ![62, 1, 0], ![61, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-27, 1, 0], ![-3, -29, 9], ![-156, 1, -24]]]
  hmulB := by decide  
  f := ![![![2554, 25989, -8064], ![-445, 79744, 0]], ![![1792, 18099, -5616], ![-266, 55536, 0]], ![![1769, 17812, -5527], ![-244, 54656, 0]]]
  g := ![![![1, 0, 0], ![-62, 89, 0], ![-61, 0, 89]], ![![-1, 1, 0], ![14, -29, 9], ![14, 1, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![17, -27, 1]] ![![89, 0, 0], ![-27, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-2403, 89, 0]], ![![1513, -2403, 89], ![-534, 801, -267]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-27, 1, 0]]], ![![![17, -27, 1]], ![![-6, 9, -3]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-43, -31, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-43, -31, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![54, 66, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-43, -31, 1], ![-63, 20, -276], ![4749, -48, -133]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-54, -66, 97]], ![![-1, -1, 1], ![153, 188, -276], ![123, 90, -133]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [13, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 96], [0, 1]]
 g := ![![[28, 35], [24], [73], [93], [70], [24, 1]], ![[92, 62], [24], [73], [93], [70], [48, 96]]]
 h' := ![![[24, 96], [49, 61], [19, 86], [17, 48], [16, 53], [76, 78], [0, 1]], ![[0, 1], [58, 36], [46, 11], [5, 49], [27, 44], [8, 19], [24, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [23, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [13, 73, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![45, -3728, 1278]
  a := ![-5, -4, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-711, -908, 1278]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-15, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-15, 1, 0]] 
 ![![97, 0, 0], ![82, 1, 0], ![36, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-15, 1, 0], ![-3, -17, 9], ![-156, 1, -12]]]
  hmulB := by decide  
  f := ![![![6463, 37134, -19656], ![-582, 211848, 0]], ![![5464, 31387, -16614], ![-484, 179062, 0]], ![![2409, 13781, -7295], ![-149, 78624, 0]]]
  g := ![![![1, 0, 0], ![-82, 97, 0], ![-36, 0, 97]], ![![-1, 1, 0], ![11, -17, 9], ![2, 1, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-43, -31, 1]] ![![97, 0, 0], ![-15, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-1455, 97, 0]], ![![-4171, -3007, 97], ![582, 485, -291]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-15, 1, 0]]], ![![![-43, -31, 1]], ![![6, 5, -3]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-31, -36, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-31, -36, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![70, 65, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-31, -36, 1], ![-48, 42, -321], ![5529, -53, -136]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-70, -65, 101]], ![![-1, -1, 1], ![222, 207, -321], ![149, 87, -136]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [28, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 100], [0, 1]]
 g := ![![[6, 95], [1], [73, 30], [58], [87], [34, 1]], ![[4, 6], [1], [83, 71], [58], [87], [68, 100]]]
 h' := ![![[34, 100], [43, 87], [77, 1], [50, 38], [19, 82], [58, 17], [0, 1]], ![[0, 1], [72, 14], [10, 100], [29, 63], [80, 19], [30, 84], [34, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [1, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [28, 67, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-369546, -76380, 8451]
  a := ![1, 1, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9516, -6195, 8451]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![18, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![18, 1, 0]] 
 ![![101, 0, 0], ![18, 1, 0], ![35, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![18, 1, 0], ![-3, 16, 9], ![-156, 1, 21]]]
  hmulB := by decide  
  f := ![![![11137, -60750, -34164], ![1414, 383396, 0]], ![![1974, -10819, -6084], ![304, 68276, 0]], ![![3859, -21052, -11839], ![492, 132860, 0]]]
  g := ![![![1, 0, 0], ![-18, 101, 0], ![-35, 0, 101]], ![![0, 1, 0], ![-6, 16, 9], ![-9, 1, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-31, -36, 1]] ![![101, 0, 0], ![18, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![1818, 101, 0]], ![![-3131, -3636, 101], ![-606, -606, -303]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![18, 1, 0]]], ![![![-31, -36, 1]], ![![-6, -6, -3]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-51, -21, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-51, -21, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![52, 82, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-51, -21, 1], ![-93, -8, -186], ![3189, -38, -111]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -82, 103]], ![![-1, -1, 1], ![93, 148, -186], ![87, 88, -111]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [38, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 102], [0, 1]]
 g := ![![[22, 19], [21, 79], [69, 83], [28], [9], [91, 1]], ![[0, 84], [0, 24], [0, 20], [28], [9], [79, 102]]]
 h' := ![![[91, 102], [26, 88], [56, 39], [101, 17], [49, 53], [44, 3], [0, 1]], ![[0, 1], [0, 15], [0, 64], [0, 86], [31, 50], [8, 100], [91, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [53, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [38, 12, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3504, -6920, 305]
  a := ![7, 5, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-188, -310, 305]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-20, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-20, 1, 0]] 
 ![![103, 0, 0], ![83, 1, 0], ![8, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-20, 1, 0], ![-3, -22, 9], ![-156, 1, -17]]]
  hmulB := by decide  
  f := ![![![-627, -4753, 1944], ![103, -22248, 0]], ![![-501, -3829, 1566], ![104, -17922, 0]], ![![-32, -370, 151], ![94, -1728, 0]]]
  g := ![![![1, 0, 0], ![-83, 103, 0], ![-8, 0, 103]], ![![-1, 1, 0], ![17, -22, 9], ![-1, 1, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-51, -21, 1]] ![![103, 0, 0], ![-20, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-2060, 103, 0]], ![![-5253, -2163, 103], ![927, 412, -206]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-20, 1, 0]]], ![![![-51, -21, 1]], ![![9, 4, -2]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![37, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![37, 1, 0]] 
 ![![107, 0, 0], ![37, 1, 0], ![46, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![37, 1, 0], ![-3, 35, 9], ![-156, 1, 40]]]
  hmulB := by decide  
  f := ![![![1105, -14178, -3645], ![321, 43335, 0]], ![![383, -4901, -1260], ![108, 14980, 0]], ![![483, -6095, -1567], ![115, 18630, 0]]]
  g := ![![![1, 0, 0], ![-37, 107, 0], ![-46, 0, 107]], ![![0, 1, 0], ![-16, 35, 9], ![-19, 1, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-31, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-31, 1, 0]] 
 ![![107, 0, 0], ![76, 1, 0], ![100, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-31, 1, 0], ![-3, -33, 9], ![-156, 1, -28]]]
  hmulB := by decide  
  f := ![![![19471, 225456, -61479], ![-3531, 730917, 0]], ![![13841, 160106, -43659], ![-2460, 519057, 0]], ![![18214, 210706, -57457], ![-3242, 683100, 0]]]
  g := ![![![1, 0, 0], ![-76, 107, 0], ![-100, 0, 107]], ![![-1, 1, 0], ![15, -33, 9], ![24, 1, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-7, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-7, 1, 0]] 
 ![![107, 0, 0], ![100, 1, 0], ![64, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-7, 1, 0], ![-3, -9, 9], ![-156, 1, -4]]]
  hmulB := by decide  
  f := ![![![18076, 54357, -54351], ![-642, 646173, 0]], ![![16895, 50792, -50787], ![-534, 603801, 0]], ![![10816, 32512, -32509], ![-320, 386496, 0]]]
  g := ![![![1, 0, 0], ![-100, 107, 0], ![-64, 0, 107]], ![![-1, 1, 0], ![3, -9, 9], ![0, 1, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![37, 1, 0]] ![![107, 0, 0], ![-31, 1, 0]]
  ![![107, 0, 0], ![3, 48, 1]] where
 M := ![![![11449, 0, 0], ![-3317, 107, 0]], ![![3959, 107, 0], ![-1150, 4, 9]]]
 hmul := by decide  
 g := ![![![![104, -48, -1], ![107, 0, 0]], ![![-31, 1, 0], ![0, 0, 0]]], ![![![34, -47, -1], ![107, 0, 0]], ![![-11, -4, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![3, 48, 1]] ![![107, 0, 0], ![-7, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-749, 107, 0]], ![![321, 5136, 107], ![-321, -428, 428]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-7, 1, 0]]], ![![![3, 48, 1]], ![![-3, -4, 4]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [19, 3, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 36, 33], [58, 72, 76], [0, 1]]
 g := ![![[11, 59, 26], [58, 45], [53, 8, 106], [8, 32, 21], [66, 20], [1]], ![[81, 10, 18, 85], [22, 75], [20, 27, 19, 91], [60, 42, 2, 79], [72, 27], [74, 35, 79, 76]], ![[26, 52, 76, 44], [42, 34], [31, 74, 4, 85], [40, 106, 68, 85], [11, 16], [8, 41, 33, 33]]]
 h' := ![![[9, 36, 33], [10, 91, 74], [83, 12, 63], [66, 27, 18], [88, 81, 81], [90, 106, 67], [0, 1]], ![[58, 72, 76], [67, 16, 47], [102, 87, 27], [50, 17, 7], [33, 90, 3], [86, 13, 38], [9, 36, 33]], ![[0, 1], [1, 2, 97], [6, 10, 19], [72, 65, 84], [55, 47, 25], [68, 99, 4], [58, 72, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 44], []]
 b := ![[], [107, 72, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [19, 3, 42, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9076866, -31392, 156960]
  a := ![5, 3, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-83274, -288, 1440]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![23, 7, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![23, 7, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![23, 7, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![23, 7, 1], ![-177, 10, 66], ![-1179, -10, 47]]]
  hmulB := by decide  
  f := ![![![-22, -7, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -7, 113]], ![![0, 0, 1], ![-15, -4, 66], ![-20, -3, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [89, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 112], [0, 1]]
 g := ![![[62, 13], [2], [49], [104], [5, 82], [19, 1]], ![[83, 100], [2], [49], [104], [94, 31], [38, 112]]]
 h' := ![![[19, 112], [59, 76], [24, 62], [59, 7], [7, 45], [4, 46], [0, 1]], ![[0, 1], [34, 37], [72, 51], [79, 106], [71, 68], [87, 67], [19, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67]]
 b := ![[], [49, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [89, 94, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-528671, -267734, 35961]
  a := ![-41, -21, 124]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11998, -4597, 35961]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![47, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![47, 1, 0]] 
 ![![113, 0, 0], ![47, 1, 0], ![66, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![47, 1, 0], ![-3, 45, 9], ![-156, 1, 50]]]
  hmulB := by decide  
  f := ![![![6777, -113642, -22725], ![1921, 285325, 0]], ![![2821, -47257, -9450], ![792, 118650, 0]], ![![3957, -66375, -13273], ![1125, 166650, 0]]]
  g := ![![![1, 0, 0], ![-47, 113, 0], ![-66, 0, 113]], ![![0, 1, 0], ![-24, 45, 9], ![-31, 1, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![23, 7, 1]] ![![113, 0, 0], ![47, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![5311, 113, 0]], ![![2599, 791, 113], ![904, 339, 113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![47, 1, 0]]], ![![![23, 7, 1]], ![![8, 3, 1]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [106, 101, 105, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 35, 14], [21, 91, 113], [0, 1]]
 g := ![![[121, 50, 107], [8, 25, 117], [44, 66, 64], [35, 50, 61], [50, 108, 103], [1]], ![[4, 73, 34, 106], [44, 22, 17, 53], [104, 47, 126, 27], [100, 125, 74, 24], [15, 101, 112, 65], [65, 0, 49, 77]], ![[27, 19, 8, 52], [115, 22, 4, 26], [1, 61, 106, 104], [6, 97, 120, 25], [17, 40, 12, 13], [121, 66, 125, 50]]]
 h' := ![![[1, 35, 14], [41, 53, 19], [35, 84, 102], [100, 68, 119], [34, 72, 51], [21, 26, 22], [0, 1]], ![[21, 91, 113], [119, 62, 58], [46, 12, 44], [104, 107, 97], [6, 40, 61], [96, 17, 80], [1, 35, 14]], ![[0, 1], [10, 12, 50], [29, 31, 108], [98, 79, 38], [26, 15, 15], [118, 84, 25], [21, 91, 113]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 124], []]
 b := ![[], [52, 119, 100], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [106, 101, 105, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![999871, -134620, -27305]
  a := ![-3, -1, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7873, -1060, -215]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [123, 75, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 28, 27], [28, 102, 104], [0, 1]]
 g := ![![[54, 30, 34], [74, 52, 113], [70, 125], [48, 63], [18, 28], [67, 1], []], ![[29, 22, 75, 7], [15, 53, 8, 1], [125, 41], [76, 117], [8, 52], [75, 55], [51, 74]], ![[123, 8, 9, 32], [81, 123, 103, 118], [58, 27], [117, 52], [120, 35], [53, 129], [105, 74]]]
 h' := ![![[39, 28, 27], [68, 18, 54], [49, 34, 84], [12, 113, 16], [26, 34, 60], [12, 92, 91], [0, 0, 1], [0, 1]], ![[28, 102, 104], [5, 57, 99], [54, 82, 54], [44, 4, 98], [109, 106, 95], [62, 127, 107], [95, 130, 102], [39, 28, 27]], ![[0, 1], [105, 56, 109], [129, 15, 124], [78, 14, 17], [37, 122, 107], [115, 43, 64], [52, 1, 28], [28, 102, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118, 115], []]
 b := ![[], [125, 130, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [123, 75, 64, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![35476241, -1187777, -476709]
  a := ![-8, -5, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![270811, -9067, -3639]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [12, 100, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 93, 84], [126, 43, 53], [0, 1]]
 g := ![![[35, 28, 98], [18, 119], [105, 59], [16, 36, 65], [121, 128], [117, 1], []], ![[110, 0, 2, 106], [30, 78], [42, 123], [130, 107, 27, 58], [69, 121], [78, 68], [133, 69]], ![[94, 101, 103, 48], [132, 61], [26, 34], [54, 37, 60, 55], [34, 136], [25, 18], [27, 69]]]
 h' := ![![[128, 93, 84], [40, 128, 57], [121, 15, 16], [82, 96, 123], [115, 99, 105], [103, 70, 26], [0, 0, 1], [0, 1]], ![[126, 43, 53], [76, 46, 51], [132, 95, 30], [15, 133, 64], [28, 25, 90], [87, 82, 11], [129, 90, 43], [128, 93, 84]], ![[0, 1], [76, 100, 29], [133, 27, 91], [87, 45, 87], [42, 13, 79], [83, 122, 100], [71, 47, 93], [126, 43, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 62], []]
 b := ![[], [19, 15, 133], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [12, 100, 20, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-342363, 0, 17125]
  a := ![0, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2499, 0, 125]
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



lemma PB228I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB228I2 : PrimesBelowBoundCertificateInterval O 79 137 228 where
  m := 11
  g := ![3, 2, 2, 2, 2, 3, 1, 2, 1, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB228I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0]
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
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![1295029]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![2248091]
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N0, I83N1, I83N2, I89N1, I97N1, I101N1, I103N1, I107N0, I107N1, I107N2, I113N1]
  Il := ![[I83N0, I83N1, I83N2], [I89N1], [I97N1], [I101N1], [I103N1], [I107N0, I107N1, I107N2], [], [I113N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
