
import IdealArithmetic.Examples.NF3_1_196911_1.RI3_1_196911_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [37, 53, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 50, 31], [58, 32, 52], [0, 1]]
 g := ![![[78, 47, 68], [43, 28, 23], [10, 61], [4, 28], [66, 77, 1], []], ![[58, 72, 31, 25], [75, 67, 78, 44], [33, 61], [13, 64], [4, 82, 7, 38], [73, 48]], ![[53, 78, 71, 60], [37, 64, 61, 8], [3, 78], [47, 78], [73, 31, 64, 22], [52, 48]]]
 h' := ![![[19, 50, 31], [69, 82, 63], [49, 0, 40], [81, 71, 12], [48, 44, 51], [0, 0, 1], [0, 1]], ![[58, 32, 52], [38, 67, 76], [73, 15, 35], [76, 27, 12], [68, 30, 8], [67, 73, 32], [19, 50, 31]], ![[0, 1], [12, 17, 27], [47, 68, 8], [65, 68, 59], [12, 9, 24], [29, 10, 50], [58, 32, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 34], []]
 b := ![[], [42, 76, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [37, 53, 6, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-184094, -2656, -6640]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2218, -32, -80]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-181019210, -11538011, 27460321]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-181019210, -11538011, 27460321]] 
 ![![89, 0, 0], ![0, 89, 0], ![55, 53, 1]] where
  M :=![![![-181019210, -11538011, 27460321], ![2311051263, -192557221, -85150376], ![-1914381849, 466825457, -169481199]]]
  hmulB := by decide  
  f := ![![![813316762709099, 122064055750972, 70451113196293]], ![![6232472733186849, 935380818460071, 539869165558567]], ![![4303748131438900, 645914329989036, 372799210195037]]]
  g := ![![![-19003785, -16482416, 27460321], ![78587887, 48543963, -85150376], ![83225664, 106172236, -169481199]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [23, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 88], [0, 1]]
 g := ![![[51, 18], [55], [55], [10, 47], [22, 78], [1]], ![[30, 71], [55], [55], [59, 42], [20, 11], [1]]]
 h' := ![![[73, 88], [28, 14], [15, 12], [37, 77], [28, 74], [66, 73], [0, 1]], ![[0, 1], [71, 75], [1, 77], [51, 12], [1, 15], [55, 16], [73, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [52, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [23, 16, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5618, 2873, 338]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-272, -169, 338]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![813316762709099, 122064055750972, 70451113196293]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![813316762709099, 122064055750972, 70451113196293]] 
 ![![89, 0, 0], ![3, 1, 0], ![87, 0, 1]] where
  M :=![![![813316762709099, 122064055750972, 70451113196293], ![6232472733186849, 935380818460071, 539869165558567], ![7980106890158658, 1197668924336981, 691252706958127]]]
  hmulB := by decide  
  f := ![![![-181019210, -11538011, 27460321]], ![![19865097, -2552486, -31117]], ![![-198461271, -6033500, 24938952]]]
  g := ![![![-63844070254172, 122064055750972, 70451113196293], ![-489239181188637, 935380818460071, 539869165558567], ![-626425678519206, 1197668924336981, 691252706958127]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-181019210, -11538011, 27460321]] ![![813316762709099, 122064055750972, 70451113196293]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [23, 52, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 64, 65], [10, 32, 32], [0, 1]]
 g := ![![[47, 54, 65], [8, 95], [23, 79], [14, 88], [61, 16], [1]], ![[89, 41, 51, 89], [84, 86], [57, 43], [2, 73], [90, 62], [77, 60, 14, 18]], ![[54, 82, 53, 9], [96, 53], [15, 53], [62, 95], [78, 12], [61, 5, 18, 79]]]
 h' := ![![[83, 64, 65], [8, 18, 68], [80, 0, 80], [67, 29, 51], [96, 16, 66], [74, 45, 93], [0, 1]], ![[10, 32, 32], [32, 88, 48], [11, 72, 38], [62, 88, 25], [60, 94, 48], [44, 44, 81], [83, 64, 65]], ![[0, 1], [39, 88, 78], [93, 25, 76], [27, 77, 21], [80, 84, 80], [82, 8, 20], [10, 32, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 60], []]
 b := ![[], [16, 84, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [23, 52, 4, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3653965750, -141904210, -172679497]
  a := ![-66, -64, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37669750, -1462930, -1780201]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![74444147963088, 11172712827204, 6448499939285]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![74444147963088, 11172712827204, 6448499939285]] 
 ![![101, 0, 0], ![0, 101, 0], ![36, 16, 1]] where
  M :=![![![74444147963088, 11172712827204, 6448499939285], ![570467920493633, 85616860790292, 49415064196735], ![730431592376650, 109624498967845, 63271435135884]]]
  hmulB := by decide  
  f := ![![![-8623247, 1143589, -14280]], ![![1073378, -7479658, 5732225]], ![![-1936359, -779684, 806284]]]
  g := ![![![-1561404453972, -910923625756, 6448499939285], ![-11965092976127, -6980437290668, 49415064196735], ![-15320198737774, -8937806566399, 63271435135884]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [79, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 100], [0, 1]]
 g := ![![[93, 78], [17], [17, 19], [81], [81], [26, 1]], ![[0, 23], [17], [6, 82], [81], [81], [52, 100]]]
 h' := ![![[26, 100], [62, 52], [71, 57], [45, 25], [9, 92], [67, 92], [0, 1]], ![[0, 1], [0, 49], [38, 44], [89, 76], [78, 9], [35, 9], [26, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [4, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [79, 75, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3805, 2809, -866]
  a := ![-5, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![271, 165, -866]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8623247, 1143589, -14280]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-8623247, 1143589, -14280]] 
 ![![101, 0, 0], ![22, 1, 0], ![81, 0, 1]] where
  M :=![![![-8623247, 1143589, -14280], ![1073378, -7479658, 5732225], ![97690585, -242760, -9766836]]]
  hmulB := by decide  
  f := ![![![74444147963088, 11172712827204, 6448499939285]], ![![21863754214669, 3281351910780, 1893881810505]], ![![66934728488978, 10045685524469, 5798019111069]]]
  g := ![![![-323025, 1143589, -14280], ![-2957271, -7479658, 5732225], ![8852921, -242760, -9766836]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![74444147963088, 11172712827204, 6448499939285]] ![![-8623247, 1143589, -14280]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [92, 64, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 98, 12], [50, 4, 91], [0, 1]]
 g := ![![[23, 85, 13], [91, 29, 92], [33], [61, 16], [37, 36], [1]], ![[54, 44], [72, 102, 43, 71], [34, 85, 18, 65], [67, 36], [73, 97], [82, 97, 38, 80]], ![[97, 31, 88, 50], [10, 14, 63, 59], [24, 49, 43, 38], [9, 4], [17, 58], [9, 21, 45, 23]]]
 h' := ![![[47, 98, 12], [74, 89, 42], [54, 101, 35], [16, 62], [13, 19, 99], [11, 39, 97], [0, 1]], ![[50, 4, 91], [43, 48], [19, 26, 13], [46, 102, 23], [37, 15, 6], [77, 73, 32], [47, 98, 12]], ![[0, 1], [33, 69, 61], [74, 79, 55], [26, 42, 80], [37, 69, 101], [57, 94, 77], [50, 4, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 20], []]
 b := ![[], [53, 14, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [92, 64, 6, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-184061, -2678, -6695]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1787, -26, -65]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-80, 13, -2]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-80, 13, -2]] 
 ![![107, 0, 0], ![7, 1, 0], ![32, 0, 1]] where
  M :=![![![-80, 13, -2], ![-144, -67, 67], ![1173, -34, -93]]]
  hmulB := by decide  
  f := ![![![-8509, -1277, -737]], ![![-1166, -175, -101]], ![![-3325, -499, -288]]]
  g := ![![![-1, 13, -2], ![-17, -67, 67], ![41, -34, -93]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![142043471243, 21318141944, 12304087571]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![142043471243, 21318141944, 12304087571]] 
 ![![107, 0, 0], ![40, 1, 0], ![79, 0, 1]] where
  M :=![![![142043471243, 21318141944, 12304087571], ![1088483727423, 163361613187, 94286622149], ![1393703087826, 209169488707, 120725329299]]]
  hmulB := by decide  
  f := ![![![4294570, -456559, -81121]], ![![1532471, -134807, -50902]], ![![2833847, -349974, -15490]]]
  g := ![![![-15726216118, 21318141944, 12304087571], ![-120510504204, 163361613187, 94286622149], ![-154302593225, 209169488707, 120725329299]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25766, -799, -2002]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![25766, -799, -2002]] 
 ![![107, 0, 0], ![60, 1, 0], ![103, 0, 1]] where
  M :=![![![25766, -799, -2002], ![-171768, 24967, -1993], ![153, -34034, 26565]]]
  hmulB := by decide  
  f := ![![![595418593, 89361503, 51576341]], ![![376521753, 56509068, 32615062]], ![![627759320, 94215258, 54377759]]]
  g := ![![![2616, -799, -2002], ![-13687, 24967, -1993], ![-6486, -34034, 26565]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-80, 13, -2]] ![![142043471243, 21318141944, 12304087571]]
  ![![-595418593, -89361503, -51576341]] where
 M := ![![![-595418593, -89361503, -51576341]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-595418593, -89361503, -51576341]] ![![25766, -799, -2002]]
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
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36624914, 7012005, -1743645]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-36624914, 7012005, -1743645]] 
 ![![109, 0, 0], ![0, 109, 0], ![53, 83, 1]] where
  M :=![![![-36624914, 7012005, -1743645], ![-134185815, -29612909, 36803670], ![655304355, -29641965, -43636919]]]
  hmulB := by decide  
  f := ![![![21863754214669, 3281351910780, 1893881810505]], ![![167542657714485, 25145106125449, 14512877743395]], ![![140177454078338, 21038086701488, 12142449458371]]]
  g := ![![![511819, 1392060, -1743645], ![-19126425, -28296491, 36803670], ![27229918, 32956168, -43636919]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [48, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 108], [0, 1]]
 g := ![![[54, 25], [82], [84, 83], [107, 9], [71], [24, 1]], ![[0, 84], [82], [5, 26], [105, 100], [71], [48, 108]]]
 h' := ![![[24, 108], [98, 5], [1, 54], [96, 65], [0, 106], [47, 92], [0, 1]], ![[0, 1], [0, 104], [98, 55], [21, 44], [37, 3], [75, 17], [24, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [75, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [48, 85, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24518, 3185, 2548]
  a := ![3, 21, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1014, -1911, 2548]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21863754214669, -3281351910780, -1893881810505]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-21863754214669, -3281351910780, -1893881810505]] 
 ![![109, 0, 0], ![22, 1, 0], ![30, 0, 1]] where
  M :=![![![-21863754214669, -3281351910780, -1893881810505], ![-167542657714485, -25145106125449, -14512877743395], ![-214522930859130, -32195990778585, -18582402303889]]]
  hmulB := by decide  
  f := ![![![36624914, -7012005, 1743645]], ![![8623247, -1143589, 14280]], ![![4068285, -1657965, 880241]]]
  g := ![![![982958184749, -3281351910780, -1893881810505], ![7532440452727, -25145106125449, -14512877743395], ![9644595737490, -32195990778585, -18582402303889]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-36624914, 7012005, -1743645]] ![![-21863754214669, -3281351910780, -1893881810505]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1105, 1359, -1174]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![1105, 1359, -1174]] 
 ![![113, 0, 0], ![0, 113, 0], ![111, 59, 1]] where
  M :=![![![1105, 1359, -1174], ![-97072, 2464, 7969], ![155431, -19958, -254]]]
  hmulB := by decide  
  f := ![![![-1401942, -210406, -121439]], ![![-10743127, -1612348, -930591]], ![![-7108103, -1066797, -615718]]]
  g := ![![![1163, 625, -1174], ![-8687, -4139, 7969], ![1625, -44, -254]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [53, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 112], [0, 1]]
 g := ![![[99, 32], [31], [100], [104], [98, 60], [64, 1]], ![[0, 81], [31], [100], [104], [96, 53], [15, 112]]]
 h' := ![![[64, 112], [61, 22], [110, 101], [41, 10], [4, 45], [111, 88], [0, 1]], ![[0, 1], [0, 91], [20, 12], [3, 103], [59, 68], [93, 25], [64, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [93, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [53, 49, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2939, 877, -282]
  a := ![-3, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![251, 155, -282]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1401942, -210406, -121439]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-1401942, -210406, -121439]] 
 ![![113, 0, 0], ![45, 1, 0], ![61, 0, 1]] where
  M :=![![![-1401942, -210406, -121439], ![-10743127, -1612348, -930591], ![-13755584, -2064463, -1191536]]]
  hmulB := by decide  
  f := ![![![1105, 1359, -1174]], ![![-419, 563, -397]], ![![1972, 557, -636]]]
  g := ![![![136939, -210406, -121439], ![1049368, -1612348, -930591], ![1343619, -2064463, -1191536]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![1105, 1359, -1174]] ![![-1401942, -210406, -121439]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB126I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 125 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 125 (by omega)

def PB126I2 : PrimesBelowBoundCertificateInterval O 79 125 126 where
  m := 8
  g := ![1, 2, 1, 2, 1, 3, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB126I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
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
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
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
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
  β := ![I89N1, I101N1, I107N0, I107N1, I107N2, I109N1, I113N1]
  Il := ![[], [I89N1], [], [I101N1], [], [I107N0, I107N1, I107N2], [I109N1], [I113N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
