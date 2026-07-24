
import IdealArithmetic.Examples.NF3_1_538412_3.RI3_1_538412_3
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [75, 51, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 49, 43], [1, 33, 40], [0, 1]]
 g := ![![[17, 19, 28], [22, 30, 70], [5, 25], [50, 81], [43, 54, 1], []], ![[4, 60, 61, 74], [44, 28, 5, 24], [29, 7], [42, 64], [14, 37, 56, 15], [61, 23]], ![[33, 71, 27, 77], [7, 66, 23, 9], [66, 38], [81, 1], [58, 44, 43, 9], [64, 23]]]
 h' := ![![[53, 49, 43], [10, 35, 51], [81, 21, 53], [46, 73, 5], [12, 65, 74], [0, 0, 1], [0, 1]], ![[1, 33, 40], [28, 53, 34], [58, 0, 79], [65, 55, 67], [12, 46, 8], [60, 26, 33], [53, 49, 43]], ![[0, 1], [63, 78, 81], [67, 62, 34], [28, 38, 11], [25, 55, 1], [15, 57, 49], [1, 33, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 16], []]
 b := ![[], [63, 72, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [75, 51, 29, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-354244, -35275, -20335]
  a := ![1, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4268, -425, -245]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-39, 43, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-39, 43, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![50, 43, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-39, 43, 1], ![62, -114, 432], ![6421, 490, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-50, -43, 89]], ![![-1, 0, 1], ![-242, -210, 432], ![39, -23, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [80, 41, 1] where
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
 g := ![![[35, 79], [21], [73], [], [28, 79], [1]], ![[0, 10], [21], [73], [], [82, 10], [1]]]
 h' := ![![[48, 88], [10, 48], [34, 33], [0, 47], [74], [9, 48], [0, 1]], ![[0, 1], [0, 41], [16, 56], [31, 42], [74], [88, 41], [48, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [84, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [80, 41, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9632, 1567, 2812]
  a := ![-3, -5, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1688, -1341, 2812]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![13, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![13, 1, 0]] 
 ![![89, 0, 0], ![13, 1, 0], ![30, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![13, 1, 0], ![-2, 11, 10], ![148, 11, 15]]]
  hmulB := by decide  
  f := ![![![7961, -44360, -40320], ![712, 358848, 0]], ![![1150, -6470, -5880], ![179, 52332, 0]], ![![2681, -14953, -13591], ![257, 120960, 0]]]
  g := ![![![1, 0, 0], ![-13, 89, 0], ![-30, 0, 89]], ![![0, 1, 0], ![-5, 11, 10], ![-5, 11, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-39, 43, 1]] ![![89, 0, 0], ![13, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![1157, 89, 0]], ![![-3471, 3827, 89], ![-445, 445, 445]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![13, 1, 0]]], ![![![-39, 43, 1]], ![![-5, 5, 5]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![80, -44, 23]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![80, -44, 23]] 
 ![![97, 0, 0], ![48, 1, 0], ![70, 0, 1]] where
  M :=![![![80, -44, 23], ![3492, 421, -394], ![-5201, -93, 268]]]
  hmulB := by decide  
  f := ![![![-76186, -9653, -7653]], ![![-49178, -6231, -4940]], ![![-74205, -9402, -7454]]]
  g := ![![![6, -44, 23], ![112, 421, -394], ![-201, -93, 268]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3482, 250, -7]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-3482, 250, -7]] 
 ![![97, 0, 0], ![55, 1, 0], ![9, 0, 1]] where
  M :=![![![-3482, 250, -7], ![-1536, -4059, 2486], ![36601, 2631, -3066]]]
  hmulB := by decide  
  f := ![![![-5904228, -748083, -593087]], ![![-4237250, -536872, -425637]], ![![-2037735, -258187, -204693]]]
  g := ![![![-177, 250, -7], ![2055, -4059, 2486], ![-830, 2631, -3066]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-156, 9, 1]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-156, 9, 1]] 
 ![![97, 0, 0], ![91, 1, 0], ![92, 0, 1]] where
  M :=![![![-156, 9, 1], ![130, -163, 92], ![1389, 116, -126]]]
  hmulB := by decide  
  f := ![![![-9866, -1250, -991]], ![![-10742, -1361, -1079]], ![![-11847, -1501, -1190]]]
  g := ![![![-11, 9, 1], ![67, -163, 92], ![25, 116, -126]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![80, -44, 23]] ![![-3482, 250, -7]]
  ![![630847, 259109, -180462]] where
 M := ![![![630847, 259109, -180462]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![630847, 259109, -180462]] ![![-156, 9, 1]]
  ![![97, 0, 0]] where
 M := ![![![-315389680, -57490736, 47207087]]]
 hmul := by decide  
 g := ![![![![-3251440, -592688, 486671]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![40, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![40, 1, 0]] 
 ![![101, 0, 0], ![40, 1, 0], ![70, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![40, 1, 0], ![-2, 38, 10], ![148, 11, 42]]]
  hmulB := by decide  
  f := ![![![4633, -94857, -24960], ![909, 252096, 0]], ![![1816, -37548, -9880], ![405, 99788, 0]], ![![3190, -65743, -17299], ![683, 174720, 0]]]
  g := ![![![1, 0, 0], ![-40, 101, 0], ![-70, 0, 101]], ![![0, 1, 0], ![-22, 38, 10], ![-32, 11, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-35, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-35, 1, 0]] 
 ![![101, 0, 0], ![66, 1, 0], ![42, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-35, 1, 0], ![-2, -37, 10], ![148, 11, -33]]]
  hmulB := by decide  
  f := ![![![5986, 116559, -31500], ![-909, 318150, 0]], ![![3942, 76151, -20580], ![-504, 207858, 0]], ![![2492, 48470, -13099], ![-370, 132300, 0]]]
  g := ![![![1, 0, 0], ![-66, 101, 0], ![-42, 0, 101]], ![![-1, 1, 0], ![20, -37, 10], ![8, 11, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-5, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-5, 1, 0]] 
 ![![101, 0, 0], ![96, 1, 0], ![67, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-5, 1, 0], ![-2, -7, 10], ![148, 11, -3]]]
  hmulB := by decide  
  f := ![![![-1954, -6861, 9800], ![101, -98980, 0]], ![![-1856, -6518, 9310], ![102, -94031, 0]], ![![-1298, -4551, 6501], ![31, -65660, 0]]]
  g := ![![![1, 0, 0], ![-96, 101, 0], ![-67, 0, 101]], ![![-1, 1, 0], ![0, -7, 10], ![-7, 11, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![40, 1, 0]] ![![101, 0, 0], ![-35, 1, 0]]
  ![![101, 0, 0], ![-19, -30, 1]] where
 M := ![![![10201, 0, 0], ![-3535, 101, 0]], ![![4040, 101, 0], ![-1402, 3, 10]]]
 hmul := by decide  
 g := ![![![![101, 0, 0], ![0, 0, 0]], ![![-16, 31, -1], ![101, 0, 0]]], ![![![40, 1, 0], ![0, 0, 0]], ![![-12, 3, 0], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-19, -30, 1]] ![![101, 0, 0], ![-5, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-505, 101, 0]], ![![-1919, -3030, 101], ![303, 202, -303]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-5, 1, 0]]], ![![![-19, -30, 1]], ![![3, 2, -3]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [54, 54, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 99, 71], [95, 3, 32], [0, 1]]
 g := ![![[33, 42, 72], [74, 74, 76], [74, 26, 30], [88, 46], [101, 79], [1]], ![[15, 23, 25, 45], [101, 85, 43, 71], [92, 56, 85, 99], [38, 56], [80, 30], [65, 87, 0, 89]], ![[61, 62, 82, 17], [81, 33, 7, 58], [59, 18, 101, 98], [42, 100], [55, 8], [14, 65, 18, 14]]]
 h' := ![![[72, 99, 71], [21, 71, 81], [21, 6, 30], [16, 44, 37], [37, 26, 56], [49, 49, 64], [0, 1]], ![[95, 3, 32], [23, 74, 31], [52, 59, 1], [8, 74, 42], [0, 99, 57], [71, 36, 66], [72, 99, 71]], ![[0, 1], [51, 61, 94], [19, 38, 72], [16, 88, 24], [11, 81, 93], [71, 18, 76], [95, 3, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 17], []]
 b := ![[], [10, 48, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [54, 54, 39, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-991999798, -120869161, -69383478]
  a := ![1, 2, -69]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9631066, -1173487, -673626]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [57, 0, 99, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 56, 16], [68, 50, 91], [0, 1]]
 g := ![![[63, 67, 89], [57, 30, 102], [92, 42], [8, 43, 34], [84, 64], [1]], ![[58, 101, 55, 39], [105, 106, 92, 105], [1, 12], [49, 103, 9, 99], [18, 35], [93, 69, 20, 30]], ![[7, 7, 38, 71], [6, 57, 40, 6], [27, 29], [70, 71, 83, 50], [78, 79], [5, 71, 68, 77]]]
 h' := ![![[47, 56, 16], [68, 88, 93], [34, 66, 67], [79, 86, 16], [66, 97, 81], [50, 0, 8], [0, 1]], ![[68, 50, 91], [82, 58, 66], [87, 69, 19], [12, 18, 36], [27, 41, 38], [82, 62, 79], [47, 56, 16]], ![[0, 1], [76, 68, 55], [89, 79, 21], [39, 3, 55], [73, 76, 95], [102, 45, 20], [68, 50, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 91], []]
 b := ![[], [13, 52, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [57, 0, 99, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5358881, -574804, -26750]
  a := ![3, 4, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50083, -5372, -250]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![21, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![21, 1, 0]] 
 ![![109, 0, 0], ![21, 1, 0], ![58, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![21, 1, 0], ![-2, 19, 10], ![148, 11, 23]]]
  hmulB := by decide  
  f := ![![![-2193, 21244, 11180], ![-218, -121862, 0]], ![![-430, 4085, 2150], ![1, -23435, 0]], ![![-1170, 11304, 5949], ![-100, -64844, 0]]]
  g := ![![![1, 0, 0], ![-21, 109, 0], ![-58, 0, 109]], ![![0, 1, 0], ![-9, 19, 10], ![-13, 11, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![35, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![35, 1, 0]] 
 ![![109, 0, 0], ![35, 1, 0], ![26, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![35, 1, 0], ![-2, 33, 10], ![148, 11, 37]]]
  hmulB := by decide  
  f := ![![![2904, -50792, -15390], ![545, 167751, 0]], ![![918, -16304, -4940], ![219, 53846, 0]], ![![676, -12116, -3671], ![182, 40014, 0]]]
  g := ![![![1, 0, 0], ![-35, 109, 0], ![-26, 0, 109]], ![![0, 1, 0], ![-13, 33, 10], ![-11, 11, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![53, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![53, 1, 0]] 
 ![![109, 0, 0], ![53, 1, 0], ![2, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![53, 1, 0], ![-2, 51, 10], ![148, 11, 55]]]
  hmulB := by decide  
  f := ![![![2419, -69774, -13680], ![654, 149112, 0]], ![![1171, -33918, -6650], ![328, 72485, 0]], ![![5, -1281, -251], ![93, 2736, 0]]]
  g := ![![![1, 0, 0], ![-53, 109, 0], ![-2, 0, 109]], ![![0, 1, 0], ![-25, 51, 10], ![-5, 11, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![21, 1, 0]] ![![109, 0, 0], ![35, 1, 0]]
  ![![109, 0, 0], ![-3, 49, 1]] where
 M := ![![![11881, 0, 0], ![3815, 109, 0]], ![![2289, 109, 0], ![733, 54, 10]]]
 hmul := by decide  
 g := ![![![![109, 0, 0], ![0, 0, 0]], ![![35, 1, 0], ![0, 0, 0]]], ![![![21, 1, 0], ![0, 0, 0]], ![![7, -4, 0], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-3, 49, 1]] ![![109, 0, 0], ![53, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![5777, 109, 0]], ![![-327, 5341, 109], ![-109, 2507, 545]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![53, 1, 0]]], ![![![-3, 49, 1]], ![![-1, 23, 5]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15490999, 1962755, 1556090]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![15490999, 1962755, 1556090]] 
 ![![113, 0, 0], ![0, 113, 0], ![36, 77, 1]] where
  M :=![![![15490999, 1962755, 1556090], ![226375810, 28682479, 22739730], ![379184870, 48043835, 38089589]]]
  hmulB := by decide  
  f := ![![![4837, -465, 80]], ![![12770, 6647, -4490]], ![![9674, 4348, -2991]]]
  g := ![![![-358657, -1042975, 1556090], ![-5241190, -15241387, 22739730], ![-8779118, -25529686, 38089589]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [63, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 112], [0, 1]]
 g := ![![[88, 61], [16], [31], [72], [66, 83], [106, 1]], ![[0, 52], [16], [31], [72], [50, 30], [99, 112]]]
 h' := ![![[106, 112], [27, 20], [73, 4], [61, 12], [23, 80], [102, 99], [0, 1]], ![[0, 1], [0, 93], [45, 109], [90, 101], [28, 33], [87, 14], [106, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [39, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [63, 7, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1496, 425, 255]
  a := ![1, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-68, -170, 255]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4837, 465, -80]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-4837, 465, -80]] 
 ![![113, 0, 0], ![19, 1, 0], ![24, 0, 1]] where
  M :=![![![-4837, 465, -80], ![-12770, -6647, 4490], ![64260, 3755, -4867]]]
  hmulB := by decide  
  f := ![![![-15490999, -1962755, -1556090]], ![![-4608007, -583848, -462880]], ![![-6645742, -842035, -667573]]]
  g := ![![![-104, 465, -80], ![51, -6647, 4490], ![971, 3755, -4867]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![15490999, 1962755, 1556090]] ![![-4837, 465, -80]]
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
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22170, 2809, 2227]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![22170, 2809, 2227]] 
 ![![127, 0, 0], ![63, 1, 0], ![60, 0, 1]] where
  M :=![![![22170, 2809, 2227], ![323978, 41049, 32544], ![542671, 68758, 54512]]]
  hmulB := by decide  
  f := ![![![2736, -142, -27]], ![![1328, -49, -25]], ![![1115, -83, 4]]]
  g := ![![![-2271, 2809, 2227], ![-33187, 41049, 32544], ![-55589, 68758, 54512]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![34, -4, 1]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![34, -4, 1]] 
 ![![127, 0, 0], ![88, 1, 0], ![5, 0, 1]] where
  M :=![![![34, -4, 1], ![156, 53, -38], ![-535, -27, 38]]]
  hmulB := by decide  
  f := ![![![988, 125, 99]], ![![798, 101, 80]], ![![229, 29, 23]]]
  g := ![![![3, -4, 1], ![-34, 53, -38], ![13, -27, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49, 0, -2]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![49, 0, -2]] 
 ![![127, 0, 0], ![103, 1, 0], ![39, 0, 1]] where
  M :=![![![49, 0, -2], ![-296, 27, -4], ![-114, -34, 25]]]
  hmulB := by decide  
  f := ![![![539, 68, 54]], ![![499, 63, 50]], ![![269, 34, 27]]]
  g := ![![![1, 0, -2], ![-23, 27, -4], ![19, -34, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![22170, 2809, 2227]] ![![34, -4, 1]]
  ![![539, 68, 54]] where
 M := ![![![539, 68, 54]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![539, 68, 54]] ![![49, 0, -2]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [111, 27, 127, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 54, 26], [51, 76, 105], [0, 1]]
 g := ![![[109, 43, 105], [113, 8, 62], [81, 102], [109, 77], [62, 121], [4, 1], []], ![[82, 14, 4, 98], [99, 29, 83, 79], [104, 5], [126, 3], [74, 7], [92, 12], [10, 21]], ![[61, 99, 17, 28], [103, 120, 119, 20], [21, 35], [5, 60], [110, 81], [22, 34], [62, 21]]]
 h' := ![![[84, 54, 26], [33, 53, 57], [113, 94, 113], [14, 32, 87], [42, 28, 83], [80, 43, 120], [0, 0, 1], [0, 1]], ![[51, 76, 105], [56, 62, 77], [17, 79, 28], [65, 95, 108], [77, 64, 93], [118, 47, 20], [51, 52, 76], [84, 54, 26]], ![[0, 1], [21, 16, 128], [90, 89, 121], [60, 4, 67], [109, 39, 86], [108, 41, 122], [42, 79, 54], [51, 76, 105]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89, 82], []]
 b := ![[], [29, 35, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [111, 27, 127, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18468642, 2188224, 1600296]
  a := ![-1, 18, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![140982, 16704, 12216]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [76, 74, 135, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 132, 19], [45, 4, 118], [0, 1]]
 g := ![![[24, 66, 121], [86, 118], [39, 15], [80, 74, 63], [60, 105], [2, 1], []], ![[15, 91, 73, 87], [85, 63], [86, 103], [104, 126, 125, 37], [48, 88], [52, 16], [121, 87]], ![[6, 25, 106, 14], [97, 56], [16, 135], [62, 8, 10, 16], [110, 101], [75, 25], [22, 87]]]
 h' := ![![[94, 132, 19], [99, 8, 126], [14, 39, 114], [85, 36, 120], [49, 54, 101], [122, 50, 67], [0, 0, 1], [0, 1]], ![[45, 4, 118], [16, 1, 108], [41, 90, 101], [136, 120, 68], [1, 51, 60], [19, 123, 122], [51, 71, 4], [94, 132, 19]], ![[0, 1], [1, 128, 40], [89, 8, 59], [88, 118, 86], [46, 32, 113], [130, 101, 85], [79, 66, 132], [45, 4, 118]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 107], []]
 b := ![[], [95, 41, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [76, 74, 135, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-623898, -44388, 66582]
  a := ![1, 4, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4554, -324, 486]
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



lemma PB208I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB208I2 : PrimesBelowBoundCertificateInterval O 79 137 208 where
  m := 11
  g := ![1, 2, 3, 3, 1, 1, 3, 2, 3, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB208I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
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
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![97, 97, 97]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![109, 109, 109]
    · exact ![12769, 113]
    · exact ![127, 127, 127]
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
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I89N1, I97N0, I97N1, I97N2, I101N0, I101N1, I101N2, I109N0, I109N1, I109N2, I113N1, I127N0, I127N1, I127N2]
  Il := ![[], [I89N1], [I97N0, I97N1, I97N2], [I101N0, I101N1, I101N2], [], [], [I109N0, I109N1, I109N2], [I113N1], [I127N0, I127N1, I127N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
