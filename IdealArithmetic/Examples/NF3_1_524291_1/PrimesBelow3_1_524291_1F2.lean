
import IdealArithmetic.Examples.NF3_1_524291_1.RI3_1_524291_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![2, -5, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![2, -5, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![2, 78, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![2, -5, 1], ![130, 7, -18], ![-595, 35, -7]]]
  hmulB := by decide  
  f := ![![![-1, 5, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -78, 83]], ![![0, -1, 1], ![2, 17, -18], ![-7, 7, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [2, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 82], [0, 1]]
 g := ![![[59, 30], [45, 63], [77], [12], [10, 63], [1]], ![[5, 53], [81, 20], [77], [12], [46, 20], [1]]]
 h' := ![![[48, 82], [76, 69], [39, 48], [44, 34], [63, 26], [81, 48], [0, 1]], ![[0, 1], [68, 14], [19, 35], [16, 49], [66, 57], [61, 35], [48, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [22, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [2, 35, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2008, 1288, -158]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![28, 164, -158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![18, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![18, 1, 0]] 
 ![![83, 0, 0], ![18, 1, 0], ![7, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![18, 1, 0], ![2, 17, 4], ![140, 0, 20]]]
  hmulB := by decide  
  f := ![![![3247, 29567, 6960], ![1079, -144420, 0]], ![![700, 6406, 1508], ![250, -31291, 0]], ![![263, 2493, 587], ![141, -12180, 0]]]
  g := ![![![1, 0, 0], ![-18, 83, 0], ![-7, 0, 83]], ![![0, 1, 0], ![-4, 17, 4], ![0, 0, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![2, -5, 1]] ![![83, 0, 0], ![18, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![1494, 83, 0]], ![![166, -415, 83], ![166, -83, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![18, 1, 0]]], ![![![2, -5, 1]], ![![2, -1, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [55, 14, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 77, 32], [7, 11, 57], [0, 1]]
 g := ![![[63, 12, 42], [57, 1], [47, 42], [10, 22, 4], [66, 13, 1], []], ![[5, 34, 4, 21], [60, 9], [23, 8], [64, 16, 23, 25], [66, 31, 34, 45], [84, 45]], ![[23, 76, 48, 39], [41, 16], [6, 47], [69, 78, 20, 72], [84, 49, 52, 20], [59, 45]]]
 h' := ![![[6, 77, 32], [27, 0, 24], [74, 22, 1], [73, 79, 65], [19, 52, 87], [0, 0, 1], [0, 1]], ![[7, 11, 57], [15, 56, 86], [72, 35, 3], [25, 64, 39], [65, 24, 40], [44, 32, 11], [6, 77, 32]], ![[0, 1], [41, 33, 68], [58, 32, 85], [78, 35, 74], [11, 13, 51], [8, 57, 77], [7, 11, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 62], []]
 b := ![[], [51, 50, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [55, 14, 76, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1601822, 151033, 1958]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17998, 1697, 22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [7, 42, 66, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 19, 2], [58, 77, 95], [0, 1]]
 g := ![![[87, 3, 18], [41, 95], [54, 64], [1, 44], [27, 88], [1]], ![[95, 71, 9, 2], [16, 9], [45, 24], [61, 65], [15, 43], [68, 63, 88, 8]], ![[24, 46, 25, 33], [58, 2], [23, 70], [35, 85], [1, 36], [96, 91, 94, 89]]]
 h' := ![![[70, 19, 2], [28, 17, 55], [11, 74, 80], [96, 60, 89], [54, 2, 23], [90, 55, 31], [0, 1]], ![[58, 77, 95], [9, 79, 1], [11, 37, 3], [61, 45, 86], [87, 70, 29], [17, 38, 72], [70, 19, 2]], ![[0, 1], [18, 1, 41], [6, 83, 14], [19, 89, 19], [78, 25, 45], [52, 4, 91], [58, 77, 95]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 32], []]
 b := ![[], [88, 6, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [7, 42, 66, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1492844938, -28838391, -49545854]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15390154, -297303, -510782]
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


def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![10, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![10, 1, 0]] 
 ![![101, 0, 0], ![10, 1, 0], ![79, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![10, 1, 0], ![2, 9, 4], ![140, 0, 12]]]
  hmulB := by decide  
  f := ![![![1255, 5731, 2548], ![202, -64337, 0]], ![![116, 566, 252], ![102, -6363, 0]], ![![975, 4482, 1993], ![225, -50323, 0]]]
  g := ![![![1, 0, 0], ![-10, 101, 0], ![-79, 0, 101]], ![![0, 1, 0], ![-4, 9, 4], ![-8, 0, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![45, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![45, 1, 0]] 
 ![![101, 0, 0], ![45, 1, 0], ![61, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![45, 1, 0], ![2, 44, 4], ![140, 0, 47]]]
  hmulB := by decide  
  f := ![![![451, 13856, 1260], ![404, -31815, 0]], ![![190, 6158, 560], ![203, -14140, 0]], ![![251, 8368, 761], ![292, -19215, 0]]]
  g := ![![![1, 0, 0], ![-45, 101, 0], ![-61, 0, 101]], ![![0, 1, 0], ![-22, 44, 4], ![-27, 0, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![10, 1, 0]] ![![101, 0, 0], ![45, 1, 0]]
  ![![101, 0, 0], ![12, -37, 1]] where
 M := ![![![10201, 0, 0], ![4545, 101, 0]], ![![1010, 101, 0], ![452, 54, 4]]]
 hmul := by decide  
 g := ![![![![89, 37, -1], ![101, 0, 0]], ![![33, 38, -1], ![101, 0, 0]]], ![![![-2, 38, -1], ![101, 0, 0]], ![![4, 2, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![12, -37, 1]] ![![101, 0, 0], ![45, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![4545, 101, 0]], ![![1212, -3737, 101], ![606, -1616, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![45, 1, 0]]], ![![![12, -37, 1]], ![![6, -16, -1]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N1
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [77, 33, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 67, 53], [24, 35, 50], [0, 1]]
 g := ![![[38, 62, 8], [44, 21, 68], [30, 78, 49], [38, 58], [94, 15], [1]], ![[14, 11, 93, 74], [13, 99, 101, 62], [51, 16, 46, 85], [45, 60], [61, 100], [93, 51, 31, 42]], ![[64, 6, 76, 1], [78, 48, 80, 66], [54, 42, 84, 4], [77, 33], [95, 63], [19, 11, 91, 61]]]
 h' := ![![[61, 67, 53], [11, 0, 27], [59, 31, 45], [34, 5, 96], [30, 1, 26], [26, 70, 85], [0, 1]], ![[24, 35, 50], [42, 65, 18], [79, 91, 25], [83, 74, 20], [56, 80, 36], [18, 46, 93], [61, 67, 53]], ![[0, 1], [45, 38, 58], [70, 84, 33], [46, 24, 90], [102, 22, 41], [1, 90, 28], [24, 35, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 54], []]
 b := ![[], [87, 5, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [77, 33, 18, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3542582, 8343, -25029]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34394, 81, -243]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![935, 96, 57]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![935, 96, 57]] 
 ![![107, 0, 0], ![33, 1, 0], ![4, 0, 1]] where
  M :=![![![935, 96, 57], ![8172, 839, 498], ![19425, 1995, 1184]]]
  hmulB := by decide  
  f := ![![![-134, 51, -15]], ![![-60, 14, -3]], ![![47, -3, -1]]]
  g := ![![![-23, 96, 57], ![-201, 839, 498], ![-478, 1995, 1184]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![36, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![36, 1, 0]] 
 ![![107, 0, 0], ![36, 1, 0], ![60, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![36, 1, 0], ![2, 35, 4], ![140, 0, 38]]]
  hmulB := by decide  
  f := ![![![217, 5038, 576], ![214, -15408, 0]], ![![60, 1679, 192], ![108, -5136, 0]], ![![120, 2825, 323], ![125, -8640, 0]]]
  g := ![![![1, 0, 0], ![-36, 107, 0], ![-60, 0, 107]], ![![0, 1, 0], ![-14, 35, 4], ![-20, 0, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![37, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![37, 1, 0]] 
 ![![107, 0, 0], ![37, 1, 0], ![42, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![37, 1, 0], ![2, 36, 4], ![140, 0, 39]]]
  hmulB := by decide  
  f := ![![![6107, 131188, 14580], ![3424, -390015, 0]], ![![2113, 45349, 5040], ![1178, -134820, 0]], ![![2384, 51494, 5723], ![1382, -153090, 0]]]
  g := ![![![1, 0, 0], ![-37, 107, 0], ![-42, 0, 107]], ![![0, 1, 0], ![-14, 36, 4], ![-14, 0, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![935, 96, 57]] ![![107, 0, 0], ![36, 1, 0]]
  ![![107, 0, 0], ![30, 17, 1]] where
 M := ![![![100045, 10272, 6099], ![41832, 4295, 2550]]]
 hmul := by decide  
 g := ![![![![845, 45, 54], ![321, 0, 0]], ![![336, 9, 22], ![196, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![30, 17, 1]] ![![107, 0, 0], ![37, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![3959, 107, 0]], ![![3210, 1819, 107], ![1284, 642, 107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![37, 1, 0]]], ![![![30, 17, 1]], ![![12, 6, 1]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [51, 94, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 39, 80], [22, 69, 29], [0, 1]]
 g := ![![[52, 16, 4], [100, 73], [94, 6, 64], [27, 100, 88], [106, 87], [1]], ![[11, 32, 36, 64], [86, 75], [63, 91, 101, 1], [81, 35, 85, 7], [72, 38], [13, 90, 28, 27]], ![[57, 54, 30, 89], [90, 29], [103, 21, 94, 38], [72, 33, 88, 16], [25, 4], [48, 25, 65, 82]]]
 h' := ![![[73, 39, 80], [27, 91, 107], [2, 88, 20], [40, 70, 8], [29, 92, 57], [58, 15, 95], [0, 1]], ![[22, 69, 29], [88, 21, 57], [88, 17, 27], [86, 56, 48], [94, 41, 66], [96, 87, 16], [73, 39, 80]], ![[0, 1], [93, 106, 54], [43, 4, 62], [59, 92, 53], [4, 85, 95], [25, 7, 107], [22, 69, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 108], []]
 b := ![[], [102, 5, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [51, 94, 14, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1052504, 3815, -22890]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9656, 35, -210]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![50, 47, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![50, 47, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![50, 47, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![50, 47, 1], ![234, 3, 190], ![6685, 35, 145]]]
  hmulB := by decide  
  f := ![![![-49, -47, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-50, -47, 113]], ![![0, 0, 1], ![-82, -79, 190], ![-5, -60, 145]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [19, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 112], [0, 1]]
 g := ![![[46, 102], [83], [1], [15], [54, 77], [30, 1]], ![[55, 11], [83], [1], [15], [104, 36], [60, 112]]]
 h' := ![![[30, 112], [61, 92], [13, 99], [22, 112], [104, 69], [108, 90], [0, 1]], ![[0, 1], [109, 21], [45, 14], [105, 1], [27, 44], [96, 23], [30, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [42, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [19, 83, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![184436, 64587, 7142]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1528, -2399, 7142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![36, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![36, 1, 0]] 
 ![![113, 0, 0], ![36, 1, 0], ![81, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![36, 1, 0], ![2, 35, 4], ![140, 0, 38]]]
  hmulB := by decide  
  f := ![![![-3367, -67746, -7744], ![-1582, 218768, 0]], ![![-1088, -21556, -2464], ![-451, 69608, 0]], ![![-2403, -48561, -5551], ![-1167, 156816, 0]]]
  g := ![![![1, 0, 0], ![-36, 113, 0], ![-81, 0, 113]], ![![0, 1, 0], ![-14, 35, 4], ![-26, 0, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![50, 47, 1]] ![![113, 0, 0], ![36, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![4068, 113, 0]], ![![5650, 5311, 113], ![2034, 1695, 226]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![36, 1, 0]]], ![![![50, 47, 1]], ![![18, 15, 2]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![56, 15, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![56, 15, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![56, 15, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![56, 15, 1], ![170, 41, 62], ![2205, 35, 87]]]
  hmulB := by decide  
  f := ![![![-55, -15, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -15, 127]], ![![0, 0, 1], ![-26, -7, 62], ![-21, -10, 87]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [94, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 126], [0, 1]]
 g := ![![[111, 50], [117, 34], [94, 9], [82, 38], [89, 37], [107, 1]], ![[0, 77], [72, 93], [41, 118], [84, 89], [111, 90], [87, 126]]]
 h' := ![![[107, 126], [51, 47], [54, 65], [39, 124], [16, 66], [102, 52], [0, 1]], ![[0, 1], [0, 80], [24, 62], [99, 3], [93, 61], [78, 75], [107, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [105, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [94, 20, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![481, 54, 29]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9, -3, 29]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-62, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-62, 1, 0]] 
 ![![127, 0, 0], ![65, 1, 0], ![40, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-62, 1, 0], ![2, -63, 4], ![140, 0, -60]]]
  hmulB := by decide  
  f := ![![![4591, -203145, 12900], ![-3810, -409575, 0]], ![![2371, -103935, 6600], ![-1904, -209550, 0]], ![![1466, -63983, 4063], ![-1159, -129000, 0]]]
  g := ![![![1, 0, 0], ![-65, 127, 0], ![-40, 0, 127]], ![![-1, 1, 0], ![31, -63, 4], ![20, 0, -60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![56, 15, 1]] ![![127, 0, 0], ![-62, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-7874, 127, 0]], ![![7112, 1905, 127], ![-3302, -889, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-62, 1, 0]]], ![![![56, 15, 1]], ![![-26, -7, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![50, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![50, 1, 0]] 
 ![![131, 0, 0], ![50, 1, 0], ![43, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![50, 1, 0], ![2, 49, 4], ![140, 0, 52]]]
  hmulB := by decide  
  f := ![![![-1727, -52128, -4256], ![-1048, 139384, 0]], ![![-662, -19891, -1624], ![-392, 53186, 0]], ![![-581, -17111, -1397], ![-307, 45752, 0]]]
  g := ![![![1, 0, 0], ![-50, 131, 0], ![-43, 0, 131]], ![![0, 1, 0], ![-20, 49, 4], ![-16, 0, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-47, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-47, 1, 0]] 
 ![![131, 0, 0], ![84, 1, 0], ![26, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-47, 1, 0], ![2, -48, 4], ![140, 0, -45]]]
  hmulB := by decide  
  f := ![![![-1651, 48664, -4056], ![1048, 132834, 0]], ![![-1064, 31195, -2600], ![656, 85150, 0]], ![![-304, 9658, -805], ![274, 26364, 0]]]
  g := ![![![1, 0, 0], ![-84, 131, 0], ![-26, 0, 131]], ![![-1, 1, 0], ![30, -48, 4], ![10, 0, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-4, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-4, 1, 0]] 
 ![![131, 0, 0], ![127, 1, 0], ![61, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-4, 1, 0], ![2, -5, 4], ![140, 0, -2]]]
  hmulB := by decide  
  f := ![![![11353, -28416, 22736], ![-524, -744604, 0]], ![![11005, -27546, 22040], ![-523, -721810, 0]], ![![5287, -13232, 10587], ![-228, -346724, 0]]]
  g := ![![![1, 0, 0], ![-127, 131, 0], ![-61, 0, 131]], ![![-1, 1, 0], ![3, -5, 4], ![2, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![50, 1, 0]] ![![131, 0, 0], ![-47, 1, 0]]
  ![![131, 0, 0], ![-63, -65, 1]] where
 M := ![![![17161, 0, 0], ![-6157, 131, 0]], ![![6550, 131, 0], ![-2348, 2, 4]]]
 hmul := by decide  
 g := ![![![![131, 0, 0], ![0, 0, 0]], ![![16, 66, -1], ![131, 0, 0]]], ![![![50, 1, 0], ![0, 0, 0]], ![![47, 67, -1], ![135, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-63, -65, 1]] ![![131, 0, 0], ![-4, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-524, 131, 0]], ![![-8253, -8515, 131], ![262, 262, -262]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-4, 1, 0]]], ![![![-63, -65, 1]], ![![2, 2, -2]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [53, 101, 114, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [112, 124, 23], [48, 12, 114], [0, 1]]
 g := ![![[47, 80, 78], [47, 9], [58, 103], [72, 98, 77], [117, 15], [23, 1], []], ![[21, 55, 59, 116], [129, 8], [133, 81], [78, 102, 57, 24], [30, 11], [21, 7], [61, 118]], ![[68, 71, 132, 10], [48, 115], [17, 56], [54, 113, 81, 86], [31, 74], [82, 32], [107, 118]]]
 h' := ![![[112, 124, 23], [84, 24, 107], [66, 19, 3], [20, 119, 68], [23, 46, 25], [14, 90, 17], [0, 0, 1], [0, 1]], ![[48, 12, 114], [45, 0, 55], [124, 78, 62], [130, 20, 128], [118, 101, 125], [8, 78, 82], [132, 17, 12], [112, 124, 23]], ![[0, 1], [44, 113, 112], [56, 40, 72], [86, 135, 78], [119, 127, 124], [114, 106, 38], [58, 120, 124], [48, 12, 114]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 58], []]
 b := ![[], [87, 45, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [53, 101, 114, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5544801, 458128, 109052]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![40473, 3344, 796]
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



lemma PB205I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB205I2 : PrimesBelowBoundCertificateInterval O 79 137 205 where
  m := 11
  g := ![2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB205I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
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
    · exact ![6889, 83]
    · exact ![704969]
    · exact ![912673]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![1295029]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![131, 131, 131]
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
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I101N0, I101N1, I107N0, I107N1, I107N2, I113N1, I127N1, I131N0, I131N1, I131N2]
  Il := ![[I83N1], [], [], [I101N0, I101N1, I101N1], [], [I107N0, I107N1, I107N2], [], [I113N1], [I127N1], [I131N0, I131N1, I131N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
