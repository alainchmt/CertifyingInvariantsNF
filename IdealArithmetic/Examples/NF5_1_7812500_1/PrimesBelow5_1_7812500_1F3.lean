
import IdealArithmetic.Examples.NF5_1_7812500_1.RI5_1_7812500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-541, -31, 153, 104, -398]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-541, -31, 153, 104, -398]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![8, 31, 89, 1, 0], ![22, 52, 14, 0, 1]] where
  M :=![![![-541, -31, 153, 104, -398], ![-208, -39, 37, 31, -118], ![-62, -59, -20, 0, -32], ![0, -30, 5, 12, -160], ![-74, -23, 20, 19, -127]]]
  hmulB := by decide  
  f := ![![![-13, 22, -17, -17, 46]], ![![34, -76, 49, 22, -76]], ![![-44, 132, -78, 15, 16]], ![![-28, 89, -52, 16, -2]], ![![8, -15, 10, 9, -25]]]
  g := ![![![69, 163, -33, 104, -398], ![20, 48, -10, 31, -118], ![6, 15, 4, 0, -32], ![32, 74, 11, 12, -160], ![24, 56, 1, 19, -127]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [97, 55, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 53, 49], [42, 53, 58], [0, 1]]
 g := ![![[26, 97, 81], [7, 91, 56], [104, 99], [3, 21, 1], [46, 40], [1]], ![[100, 15, 66, 57], [43, 18, 102, 40], [104, 37], [27, 104, 45, 99], [96, 30], [40, 94, 96, 56]], ![[97, 15, 19, 91], [2, 67, 55, 31], [105, 39], [59, 20, 61, 54], [103, 41], [38, 13, 84, 51]]]
 h' := ![![[46, 53, 49], [70, 79, 9], [14, 53, 22], [30, 28, 45], [25, 87, 106], [10, 52, 88], [0, 1]], ![[42, 53, 58], [28, 69, 68], [17, 102, 18], [58, 47, 12], [96, 99, 37], [45, 60, 43], [46, 53, 49]], ![[0, 1], [14, 66, 30], [32, 59, 67], [65, 32, 50], [83, 28, 71], [103, 102, 83], [42, 53, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 30], []]
 b := ![[], [20, 45, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [97, 55, 19, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![33128, -23193, 67317, 49594, -221589]
  a := ![5, -3, 16, 11, -45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![42162, 93103, -11629, 49594, -221589]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -22, 17, 17, -46]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![13, -22, 17, 17, -46]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![79, 18, 1, 0, 0], ![76, 76, 0, 1, 0], ![57, 105, 0, 0, 1]] where
  M :=![![![13, -22, 17, 17, -46], ![-34, 76, -49, -22, 76], ![44, -132, 78, -15, -16], ![30, 45, 5, 169, -350], ![10, -15, 12, 17, -41]]]
  hmulB := by decide  
  f := ![![![541, 31, -153, -104, 398]], ![![208, 39, -37, -31, 118]], ![![435, 30, -119, -82, 314]], ![![532, 50, -135, -96, 368]], ![![493, 55, -118, -86, 329]]]
  g := ![![![0, 30, 17, 17, -46], ![11, -50, -49, -22, 76], ![-38, 12, 78, -15, -16], ![63, 223, 5, 169, -350], ![1, 26, 12, 17, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P1 : CertificateIrreducibleZModOfList' 107 2 2 6 [29, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 106], [0, 1]]
 g := ![![[47, 48], [40, 75], [25], [47, 53], [36], [28, 1]], ![[0, 59], [0, 32], [25], [33, 54], [36], [56, 106]]]
 h' := ![![[28, 106], [17, 72], [59, 17], [28, 5], [36, 38], [44, 6], [0, 1]], ![[0, 1], [0, 35], [0, 90], [61, 102], [30, 69], [105, 101], [28, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [34, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N1 : CertifiedPrimeIdeal' SI107N1 107 where
  n := 2
  hpos := by decide
  P := [29, 79, 1]
  hirr := P107P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![77753, -86003, 99758, 68743, -380958]
  a := ![59, -60, 177, 116, -528]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![81187, 307425, 99758, 68743, -380958]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N1 B_one_repr
lemma NI107N1 : Nat.card (O ⧸ I107N1) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-541, -31, 153, 104, -398]] ![![13, -22, 17, 17, -46]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![-107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![45, -150, 99, 25, -116]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![45, -150, 99, 25, -116]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![24, 86, 83, 1, 0], ![17, 95, 2, 0, 1]] where
  M :=![![![45, -150, 99, 25, -116], ![-50, 186, -93, 90, -130], ![-180, 170, -184, -413, 970], ![826, -1563, 1121, 911, -2584], ![66, -155, 102, 43, -153]]]
  hmulB := by decide  
  f := ![![![15, -61, -53, -22, 76]], ![![44, -83, -59, -19, -16]], ![![38, 41, 82, 52, -422]], ![![66, -43, 9, 22, -328]], ![![41, -79, -56, -18, -15]]]
  g := ![![![13, 80, -16, 25, -116], ![0, 44, -67, 90, -130], ![-62, -518, 295, -413, 970], ![210, 1519, -636, 911, -2584], ![15, 98, -29, 43, -153]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [39, 84, 105, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 20, 18], [62, 88, 91], [0, 1]]
 g := ![![[49, 54, 74], [96, 27], [31, 34, 29], [51, 79, 80], [46, 16], [1]], ![[11, 49, 50, 79], [108, 89], [100, 51, 59, 42], [63, 9, 57, 53], [0, 104], [74, 4, 40, 55]], ![[31, 56, 76, 70], [32, 74], [64, 28, 67, 77], [81, 93, 91, 58], [4, 105], [29, 71, 78, 54]]]
 h' := ![![[51, 20, 18], [62, 76, 40], [99, 69, 71], [82, 20, 47], [54, 102, 25], [70, 25, 4], [0, 1]], ![[62, 88, 91], [85, 100, 92], [68, 4, 78], [60, 94, 27], [82, 8, 3], [55, 31, 39], [51, 20, 18]], ![[0, 1], [40, 42, 86], [78, 36, 69], [16, 104, 35], [13, 108, 81], [13, 53, 66], [62, 88, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 34], []]
 b := ![[], [45, 2, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [39, 84, 105, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39263, -32898, 84458, 47508, -250426]
  a := ![4, -3, 13, 8, -35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![28957, 180476, -30806, 47508, -250426]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 2, -14, -10, 38]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![47, 2, -14, -10, 38]] 
 ![![109, 0, 0, 0, 0], ![61, 1, 0, 0, 0], ![94, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![87, 0, 0, 0, 1]] where
  M :=![![![47, 2, -14, -10, 38], ![20, -1, -4, -2, 10], ![4, 8, -7, -4, 14], ![8, -14, 8, -1, -2], ![8, 0, -2, -2, 7]]]
  hmulB := by decide  
  f := ![![![-29, 106, 94, 42, -170]], ![![-17, 61, 54, 24, -96]], ![![-26, 92, 81, 36, -142]], ![![-11, 36, 30, 13, -48]], ![![-23, 82, 72, 32, -127]]]
  g := ![![![-15, 2, -14, -10, 38], ![-3, -1, -4, -2, 10], ![-8, 8, -7, -4, 14], ![3, -14, 8, -1, -2], ![-3, 0, -2, -2, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4349, -201, 1292, 869, -3400]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-4349, -201, 1292, 869, -3400]] 
 ![![109, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![83, 0, 1, 0, 0], ![71, 0, 0, 1, 0], ![95, 0, 0, 0, 1]] where
  M :=![![![-4349, -201, 1292, 869, -3400], ![-1738, -80, 516, 347, -1358], ![-694, -33, 207, 139, -544], ![-278, -11, 82, 56, -218], ![-740, -34, 220, 148, -579]]]
  hmulB := by decide  
  f := ![![![-29, 33, 58, 17, 32]], ![![-20, 22, 38, 11, 26]], ![![-21, 20, 39, 10, 36]], ![![-13, 8, 30, 9, 26]], ![![-23, 23, 46, 13, 33]]]
  g := ![![![1510, -201, 1292, 869, -3400], ![603, -80, 516, 347, -1358], ![242, -33, 207, 139, -544], ![96, -11, 82, 56, -218], ![257, -34, 220, 148, -579]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![45, -150, 99, 25, -116]] ![![47, 2, -14, -10, 38]]
  ![![-1217, 682, -291, -339, 734]] where
 M := ![![![-1217, 682, -291, -339, 734]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-1217, 682, -291, -339, 734]] ![![-4349, -201, 1292, 869, -3400]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![3860453, 178433, -1147007, -771720, 3018864]]]
 hmul := by decide  
 g := ![![![![35417, 1637, -10523, -7080, 27696]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1235, 49, -371, -248, 974]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![1235, 49, -371, -248, 974]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![58, 12, 6, 103, 1]] where
  M :=![![![1235, 49, -371, -248, 974], ![496, 13, -163, -105, 406], ![210, -15, -64, -44, 140], ![88, 26, 13, 16, -92], ![214, 17, -48, -33, 105]]]
  hmulB := by decide  
  f := ![![![1, -2, 1, 1, -2]], ![![-2, 4, -5, -2, 8]], ![![4, -12, 2, -3, 4]], ![![6, -3, 1, 13, -34]], ![![6, -4, 1, 12, -31]]]
  g := ![![![-489, -103, -55, -890, 974], ![-204, -43, -23, -371, 406], ![-70, -15, -8, -128, 140], ![48, 10, 5, 84, -92], ![-52, -11, -6, -96, 105]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 4 2 6 [112, 71, 41, 40, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 102, 46, 92], [83, 75, 43, 41], [110, 48, 24, 93], [0, 1]]
 g := ![![[106, 26, 28, 44], [99, 26, 36], [27, 91, 97], [65, 31, 44], [3, 90, 73, 1], []], ![[57, 19, 101, 39, 12, 65], [60, 53, 106], [79, 112, 95], [101, 20, 32], [50, 28, 102, 50, 99, 5], [33, 65, 104, 93, 90, 5]], ![[46, 5, 55, 19, 98, 13], [79, 103, 99], [30, 27, 15], [40, 28, 85], [46, 63, 62, 6, 89, 72], [74, 10, 92, 99, 23, 104]], ![[6, 23, 20, 110, 73, 24], [21, 81, 14], [34, 16, 111], [24, 7, 57], [31, 79, 82, 49, 50, 79], [62, 37, 3, 59, 82, 23]]]
 h' := ![![[106, 102, 46, 92], [12, 61, 52, 65], [79, 49, 28, 6], [74, 102, 30, 53], [3, 103, 1, 48], [0, 0, 0, 1], [0, 1]], ![[83, 75, 43, 41], [90, 101, 77, 14], [97, 49, 111, 85], [40, 10, 112, 78], [39, 44, 104, 91], [29, 60, 52, 21], [106, 102, 46, 92]], ![[110, 48, 24, 93], [49, 17, 7, 99], [99, 57, 29, 72], [42, 58, 7, 69], [62, 76, 75, 56], [81, 71, 3, 15], [83, 75, 43, 41]], ![[0, 1], [51, 47, 90, 48], [97, 71, 58, 63], [17, 56, 77, 26], [85, 3, 46, 31], [35, 95, 58, 76], [110, 48, 24, 93]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [47, 72, 63], []]
 b := ![[], [], [21, 74, 12, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 4
  hpos := by decide
  P := [112, 71, 41, 40, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1658286750, -2447096941, 494985870, 804346142, -4765205293]
  a := ![-26, 23, -80, -56, 235]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2460532688, 484383775, 257400156, 4350623817, -4765205293]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 163047361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, -1, -1, 2]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-1, 2, -1, -1, 2]] 
 ![![113, 0, 0, 0, 0], ![62, 1, 0, 0, 0], ![111, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![-1, 2, -1, -1, 2], ![2, -4, 5, 2, -8], ![-4, 12, -2, 3, -4], ![-6, 3, -1, -13, 34], ![-2, 3, 0, -1, 5]]]
  hmulB := by decide  
  f := ![![![-1235, -49, 371, 248, -974]], ![![-682, -27, 205, 137, -538]], ![![-1215, -48, 365, 244, -958]], ![![-121, -5, 36, 24, -94]], ![![-603, -24, 181, 121, -475]]]
  g := ![![![-1, 2, -1, -1, 2], ![1, -4, 5, 2, -8], ![-3, 12, -2, 3, -4], ![-16, 3, -1, -13, 34], ![-4, 3, 0, -1, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![1235, 49, -371, -248, 974]] ![![-1, 2, -1, -1, 2]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![-113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 25, -3, -6, 78]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-21, 25, -3, -6, 78]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![73, 28, 83, 39, 1]] where
  M :=![![![-21, 25, -3, -6, 78], ![12, -105, -89, -51, 282], ![102, -321, -312, -116, 492], ![232, -506, -493, -224, 372], ![126, -277, -236, -91, 167]]]
  hmulB := by decide  
  f := ![![![83, 4, -25, -17, 66]], ![![34, 0, -9, -6, 24]], ![![12, 4, -6, -3, 12]], ![![6, -3, 1, -3, 6]], ![![65, 4, -20, -14, 53]]]
  g := ![![![-45, -17, -51, -24, 78], ![-162, -63, -185, -87, 282], ![-282, -111, -324, -152, 492], ![-212, -86, -247, -116, 372], ![-95, -39, -111, -52, 167]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 4 2 6 [25, 38, 83, 106, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 84, 39, 48], [97, 16, 103, 84], [19, 26, 112, 122], [0, 1]]
 g := ![![[80, 79, 5, 13], [50, 34, 96, 26], [97, 80, 89, 37], [110, 60, 1, 68], [22, 104, 21, 1], []], ![[123, 82, 115, 121, 112, 91], [5, 122, 68, 62, 95, 6], [58, 76, 97, 14, 74, 125], [116, 109, 115, 110, 77, 6], [16, 103, 122, 6, 44, 56], [56, 92, 77, 10, 57, 102]], ![[61, 8, 66, 64, 93, 49], [125, 52, 7, 68, 70, 31], [68, 70, 83, 4, 93, 52], [65, 24, 122, 65, 121, 21], [108, 57, 110, 50, 103, 11], [41, 57, 114, 48, 117, 122]], ![[76, 72, 100, 89, 10, 41], [2, 40, 123, 53, 32, 32], [91, 96, 24, 76, 71, 117], [58, 97, 44, 68, 81, 124], [95, 49, 44, 120, 107, 32], [38, 56, 29, 50, 60, 2]]]
 h' := ![![[32, 84, 39, 48], [20, 61, 116, 93], [115, 60, 89, 36], [44, 21, 75, 75], [85, 120, 47, 24], [0, 0, 0, 1], [0, 1]], ![[97, 16, 103, 84], [49, 13, 95, 83], [76, 41, 49, 123], [95, 29, 21, 75], [13, 12, 72, 4], [126, 1, 96, 108], [32, 84, 39, 48]], ![[19, 26, 112, 122], [46, 110, 46, 102], [65, 90, 13, 115], [89, 23, 87, 120], [6, 11, 37, 63], [42, 85, 7, 38], [97, 16, 103, 84]], ![[0, 1], [10, 70, 124, 103], [109, 63, 103, 107], [31, 54, 71, 111], [112, 111, 98, 36], [67, 41, 24, 107], [19, 26, 112, 122]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [112, 34, 72], []]
 b := ![[], [], [106, 20, 118, 108], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 4
  hpos := by decide
  P := [25, 38, 83, 106, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54331259, -21480609, 151423192, 180655493, -478720094]
  a := ![11, -6, 39, 29, -100]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![275597623, 105375449, 314056622, 148431017, -478720094]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 260144641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 4, -25, -17, 66]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![83, 4, -25, -17, 66]] 
 ![![127, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![83, 4, -25, -17, 66], ![34, 0, -9, -6, 24], ![12, 4, -6, -3, 12], ![6, -3, 1, -3, 6], ![14, 1, -4, -3, 11]]]
  hmulB := by decide  
  f := ![![![-21, 25, -3, -6, 78]], ![![-9, 10, -2, -3, 36]], ![![-3, 2, -3, -2, 18]], ![![1, -3, -4, -2, 6]], ![![0, -1, -2, -1, 5]]]
  g := ![![![1, 4, -25, -17, 66], ![1, 0, -9, -6, 24], ![-1, 4, -6, -3, 12], ![1, -3, 1, -3, 6], ![0, 1, -4, -3, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-21, 25, -3, -6, 78]] ![![83, 4, -25, -17, 66]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -5, -2, -1, 2]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![3, -5, -2, -1, 2]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![25, 14, 1, 0, 0], ![43, 91, 0, 1, 0], ![48, 57, 0, 0, 1]] where
  M :=![![![3, -5, -2, -1, 2], ![2, 0, -2, 1, -8], ![-2, 11, 9, 1, -22], ![-2, 21, 48, 26, -92], ![-4, 16, 18, 8, -33]]]
  hmulB := by decide  
  f := ![![![125, 7, -36, -23, 94]], ![![46, 8, -20, -15, 56]], ![![29, 2, -9, -6, 24]], ![![73, 8, -26, -18, 70]], ![![66, 6, -22, -15, 59]]]
  g := ![![![0, 0, -2, -1, 2], ![3, 3, -2, 1, -8], ![6, 8, 9, 1, -22], ![16, 17, 48, 26, -92], ![6, 7, 18, 8, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [17, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [117, 130], [0, 1]]
 g := ![![[101, 9], [78, 63], [114], [27], [109], [65], [1]], ![[106, 122], [113, 68], [114], [27], [109], [65], [1]]]
 h' := ![![[117, 130], [115, 128], [8, 60], [51, 101], [95, 17], [101, 90], [114, 117], [0, 1]], ![[0, 1], [26, 3], [85, 71], [78, 30], [119, 114], [20, 41], [48, 14], [117, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [92, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [17, 14, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-247, 2012, -2596, 1240, -1224]
  a := ![-4, 2, -12, -20, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![535, -36, -2596, 1240, -1224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 31, -39, -52, 140]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![21, 31, -39, -52, 140]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![103, 44, 1, 0, 0], ![53, 1, 0, 1, 0], ![129, 98, 0, 0, 1]] where
  M :=![![![21, 31, -39, -52, 140], ![104, -171, 115, 81, -236], ![-162, 421, -266, -54, 278], ![108, -494, 243, -274, 418], ![-6, 7, -14, -41, 95]]]
  hmulB := by decide  
  f := ![![![-39, -176, -245, -137, 940]], ![![274, -1116, -1097, -500, 2234]], ![![69, -532, -577, -282, 1506]], ![![-1, -95, -115, -60, 366]], ![![173, -1017, -1067, -510, 2585]]]
  g := ![![![-86, -91, -39, -52, 140], ![110, 136, 115, 81, -236], ![-44, -115, -266, -54, 278], ![-491, -396, 243, -274, 418], ![-66, -66, -14, -41, 95]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [33, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 130], [0, 1]]
 g := ![![[73, 4], [15, 60], [53], [61], [13], [112], [1]], ![[0, 127], [99, 71], [53], [61], [13], [112], [1]]]
 h' := ![![[80, 130], [29, 129], [56, 45], [87, 70], [2, 42], [13, 12], [98, 80], [0, 1]], ![[0, 1], [0, 2], [119, 86], [54, 61], [87, 89], [56, 119], [79, 51], [80, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [127, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [33, 51, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2517, -4829, -4732, -1765, 3938]
  a := ![-4, 8, -7, -3, 49]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![576, -1380, -4732, -1765, 3938]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, -29, -25, -10, 24]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![15, -29, -25, -10, 24]] 
 ![![131, 0, 0, 0, 0], ![73, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![78, 0, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![15, -29, -25, -10, 24], ![20, -19, -7, 1, -60], ![-2, 81, 94, 48, -282], ![-96, 328, 309, 136, -546], ![-42, 153, 146, 65, -271]]]
  hmulB := by decide  
  f := ![![![-253, 614, -431, -261, 816]], ![![-137, 332, -234, -145, 450]], ![![-82, 206, -142, -75, 246]], ![![-168, 389, -277, -187, 564]], ![![-89, 215, -151, -92, 287]]]
  g := ![![![22, -29, -25, -10, 24], ![33, -19, -7, 1, -60], ![-7, 81, 94, 48, -282], ![-176, 328, 309, 136, -546], ![-78, 153, 146, 65, -271]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![3, -5, -2, -1, 2]] ![![21, 31, -39, -52, 140]]
  ![![-253, 614, -431, -261, 816]] where
 M := ![![![-253, 614, -431, -261, 816]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![-253, 614, -431, -261, 816]] ![![15, -29, -25, -10, 24]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, -64, -40, -6, 10]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![31, -64, -40, -6, 10]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![99, 21, 133, 109, 1]] where
  M :=![![![31, -64, -40, -6, 10], ![12, 15, -42, -20, -58], ![40, 50, 271, 116, -650], ![-232, 806, 538, 341, -1162], ![-84, 306, 294, 140, -553]]]
  hmulB := by decide  
  f := ![![![351, 16, -104, -70, 274]], ![![140, 7, -42, -28, 110]], ![![56, 2, -17, -12, 46]], ![![24, -2, -6, -3, 14]], ![![349, 13, -103, -69, 271]]]
  g := ![![![-7, -2, -10, -8, 10], ![42, 9, 56, 46, -58], ![470, 100, 633, 518, -650], ![838, 184, 1132, 927, -1162], ![399, 87, 539, 441, -553]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 4 2 7 [102, 30, 46, 55, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 39, 114, 131], [13, 115, 95, 23], [116, 119, 65, 120], [0, 1]]
 g := ![![[120, 31, 2, 130], [63, 121, 22], [5, 46, 36], [93, 135, 73, 107], [46, 71, 11], [1], []], ![[79, 47, 69, 95, 126, 5], [87, 49, 16], [85, 88, 4], [9, 30, 120, 36, 6, 84], [2, 92, 18], [104, 133, 99], [61, 77, 36]], ![[94, 16, 72, 136, 131, 96], [99, 104, 99], [42, 127, 77], [29, 6, 124, 68, 112, 80], [15, 33, 93], [14, 123, 30], [132, 72, 118]], ![[78, 106, 43, 20, 131, 28], [110, 3, 136], [98, 97, 30], [117, 114, 125, 126, 71, 76], [53, 128, 135], [121, 45, 72], [96, 116, 15]]]
 h' := ![![[90, 39, 114, 131], [15, 116, 71, 33], [31, 90, 107, 76], [104, 0, 128, 131], [95, 101, 121, 45], [35, 107, 91, 82], [0, 0, 1], [0, 1]], ![[13, 115, 95, 23], [3, 93, 39, 61], [66, 49, 38, 133], [67, 69, 77, 2], [130, 21, 37, 73], [34, 113, 59, 44], [97, 76, 101, 109], [90, 39, 114, 131]], ![[116, 119, 65, 120], [49, 100, 87, 24], [134, 95, 126, 28], [87, 72, 16, 25], [50, 18, 117, 53], [115, 81, 11, 97], [131, 43, 85, 116], [13, 115, 95, 23]], ![[0, 1], [33, 102, 77, 19], [108, 40, 3, 37], [69, 133, 53, 116], [63, 134, 136, 103], [117, 110, 113, 51], [102, 18, 87, 49], [116, 119, 65, 120]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [113, 76, 34], []]
 b := ![[], [], [83, 38, 73, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 4
  hpos := by decide
  P := [102, 30, 46, 55, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1299220, -3183853, -2963824, -1148233, 3053516]
  a := ![2, -3, 6, 2, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2197072, -491297, -2985996, -2437821, 3053516]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 352275361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-351, -16, 104, 70, -274]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-351, -16, 104, 70, -274]] 
 ![![137, 0, 0, 0, 0], ![88, 1, 0, 0, 0], ![65, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![69, 0, 0, 0, 1]] where
  M :=![![![-351, -16, 104, 70, -274], ![-140, -7, 42, 28, -110], ![-56, -2, 17, 12, -46], ![-24, 2, 6, 3, -14], ![-60, -2, 18, 12, -47]]]
  hmulB := by decide  
  f := ![![![-31, 64, 40, 6, -10]], ![![-20, 41, 26, 4, -6]], ![![-15, 30, 17, 2, 0]], ![![-6, 10, 6, -1, 6]], ![![-15, 30, 18, 2, -1]]]
  g := ![![![79, -16, 104, 70, -274], ![32, -7, 42, 28, -110], ![13, -2, 17, 12, -46], ![2, 2, 6, 3, -14], ![13, -2, 18, 12, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![31, -64, -40, -6, 10]] ![![-351, -16, 104, 70, -274]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0, 0, 0]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]] where
  M :=![![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 5 2 7 [91, 92, 19, 50, 26, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 88, 110, 124, 6], [76, 118, 17, 59, 27], [66, 120, 47, 15, 135], [65, 90, 104, 80, 110], [0, 1]]
 g := ![![[27, 19, 4, 36, 89], [79, 35, 31], [110, 76, 15, 64], [17, 106, 88, 76, 55], [17, 70, 113, 1], [], []], ![[18, 59, 70, 105, 81, 22, 36, 137], [72, 16, 19, 59, 90, 64, 80, 25], [70, 16, 108, 41], [34, 57, 104, 5, 28, 76, 24, 131], [10, 61, 119, 47], [44, 44, 47, 86], [86, 127, 135, 36]], ![[81, 61, 133, 68, 131, 77, 38, 75], [122, 136, 129, 126, 17, 27, 124, 115], [99, 119, 23, 55], [4, 2, 23, 128, 7, 129, 126, 48], [18, 5, 37, 49], [86, 106, 127, 113], [8, 115, 78, 34]], ![[7, 47, 107, 107, 34, 131, 28, 90], [17, 30, 110, 44, 66, 39, 3, 2], [65, 39, 55, 29], [75, 129, 82, 61, 94, 95, 80, 27], [67, 7, 95, 67], [3, 7, 88, 29], [1, 58, 20, 16]], ![[45, 128, 125, 45, 85, 74, 135, 8], [110, 43, 138, 55, 27, 84, 133, 15], [15, 99, 62, 124], [121, 66, 16, 84, 12, 19, 94, 82], [73, 43, 19, 63], [8, 135, 28, 45], [68, 12, 43, 7]]]
 h' := ![![[45, 88, 110, 124, 6], [39, 101, 25, 102, 111], [44, 116, 80, 93], [121, 95, 105, 8, 131], [121, 128, 51, 121, 74], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[76, 118, 17, 59, 27], [70, 115, 54, 25, 18], [78, 60, 100, 9, 26], [101, 27, 89, 71, 67], [99, 90, 118, 42, 36], [6, 95, 134, 7, 66], [37, 127, 103, 49, 124], [45, 88, 110, 124, 6]], ![[66, 120, 47, 15, 135], [78, 124, 55, 18, 91], [57, 56, 130, 53, 13], [46, 104, 40, 7, 74], [93, 98, 6, 103, 94], [87, 79, 76, 44, 7], [44, 63, 68, 125, 104], [76, 118, 17, 59, 27]], ![[65, 90, 104, 80, 110], [89, 71, 26, 25, 73], [86, 14, 137, 9, 114], [21, 118, 101, 85, 53], [44, 90, 65, 13, 58], [134, 131, 14, 132, 117], [95, 45, 85, 55, 86], [66, 120, 47, 15, 135]], ![[0, 1], [52, 6, 118, 108, 124], [31, 32, 109, 114, 125], [59, 73, 82, 107, 92], [96, 11, 38, 138, 16], [117, 112, 54, 95, 87], [122, 43, 21, 49, 103], [65, 90, 104, 80, 110]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 7, 55, 9], [], [], []]
 b := ![[], [60, 115, 6, 6, 68], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 5
  hpos := by decide
  P := [91, 92, 19, 50, 26, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-140132433, 610236271, -332422670, 295869145, -408529062]
  a := ![-3, 3, -2, -10, 30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1008147, 4390189, -2391530, 2128555, -2939058]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 51888844699 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0, 0, 0]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![0, 0, 0, 0, 149]] where
  M :=![![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![0, 0, 0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 5 2 7 [23, 84, 62, 96, 107, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 95, 54, 25, 94], [110, 119, 33, 73, 8], [132, 41, 36, 0, 105], [37, 42, 26, 51, 91], [0, 1]]
 g := ![![[101, 97, 111, 23, 76], [41, 28, 27, 112], [85, 125, 112, 1, 69], [143, 141, 87, 76], [88, 104, 29, 42, 1], [], []], ![[101, 71, 124, 35, 89, 120, 76, 101], [76, 100, 19, 22], [119, 16, 136, 7, 41, 33, 25, 34], [52, 66, 49, 132], [34, 27, 146, 75, 115, 130, 63, 87], [33, 92, 53, 112], [145, 137, 34, 45]], ![[82, 95, 66, 59, 121, 104, 28, 147], [21, 28, 146, 4], [54, 47, 35, 55, 32, 39, 65, 99], [127, 87, 18, 25], [55, 43, 88, 85, 99, 35, 75, 126], [7, 139, 64, 118], [12, 0, 131, 64]], ![[130, 40, 84, 11, 52, 27, 132, 117], [140, 147, 95, 132], [107, 67, 86, 144, 57, 51], [132, 28, 84, 125], [121, 107, 61, 116, 31, 96, 98, 122], [30, 9, 21, 142], [14, 81, 107, 148]], ![[141, 29, 78, 144, 26, 139, 117, 43], [21, 102, 112, 86], [13, 55, 110, 51, 17, 71, 102, 70], [118, 135, 51, 123], [25, 104, 74, 114, 69, 65, 89, 138], [127, 9, 62, 35], [106, 53, 80, 86]]]
 h' := ![![[61, 95, 54, 25, 94], [126, 22, 128, 98, 15], [131, 10, 24, 91, 75], [108, 34, 71, 10, 101], [62, 50, 41, 29, 134], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[110, 119, 33, 73, 8], [66, 84, 87, 63, 146], [18, 78, 127, 13, 97], [50, 147, 46, 98, 78], [59, 113, 72, 147, 70], [131, 44, 5, 84, 69], [88, 133, 144, 117, 75], [61, 95, 54, 25, 94]], ![[132, 41, 36, 0, 105], [78, 120, 59, 10, 22], [73, 101, 50, 80, 147], [10, 100, 112, 78, 110], [139, 114, 73, 16, 5], [115, 29, 108, 1, 84], [53, 140, 82, 5, 77], [110, 119, 33, 73, 8]], ![[37, 42, 26, 51, 91], [119, 116, 34, 19, 23], [43, 44, 104, 26, 70], [112, 127, 92, 146], [67, 14, 30, 13, 42], [101, 46, 60, 142, 2], [116, 37, 9, 137, 80], [132, 41, 36, 0, 105]], ![[0, 1], [17, 105, 139, 108, 92], [84, 65, 142, 88, 58], [133, 39, 126, 115, 9], [145, 7, 82, 93, 47], [139, 30, 125, 71, 142], [123, 137, 62, 39, 66], [37, 42, 26, 51, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 80, 63, 39], [], [], []]
 b := ![[], [27, 34, 107, 133, 147], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 5
  hpos := by decide
  P := [23, 84, 62, 96, 107, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24694813, -46005091, 242520148, -59578991, -242344328]
  a := ![-8, 5, -28, -20, 73]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![165737, -308759, 1627652, -399859, -1626472]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 73439775749 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, -33, 18, -3, -4]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![17, -33, 18, -3, -4]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![67, 70, 1, 0, 0], ![142, 150, 0, 1, 0], ![2, 22, 0, 0, 1]] where
  M :=![![![17, -33, 18, -3, -4], ![6, 18, -4, 37, -74], ![-74, 117, -93, -115, 296], ![230, -485, 330, 186, -590], ![16, -38, 24, 4, -23]]]
  hmulB := by decide  
  f := ![![![-13, 87, 64, 23, -44]], ![![-46, 54, 14, -7, 194]], ![![-27, 62, 33, 6, 76]], ![![-56, 129, 68, 12, 162]], ![![-6, 6, 0, -2, 33]]]
  g := ![![![-5, -5, 18, -3, -4], ![-32, -24, -4, 37, -74], ![145, 115, -93, -115, 296], ![-312, -255, 330, 186, -590], ![-14, -12, 24, 4, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [127, 140, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 150], [0, 1]]
 g := ![![[120, 44], [149, 110], [114, 72], [44], [42, 95], [121], [1]], ![[0, 107], [0, 41], [0, 79], [44], [30, 56], [121], [1]]]
 h' := ![![[11, 150], [103, 73], [18, 67], [135, 125], [102, 73], [7, 47], [24, 11], [0, 1]], ![[0, 1], [0, 78], [0, 84], [0, 26], [150, 78], [71, 104], [145, 140], [11, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [126, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [127, 140, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![57, 21, -1636, -873, 3794]
  a := ![-4, 4, -13, -7, 40]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1497, 1073, -1636, -873, 3794]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -24, -21, -9, 38]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![7, -24, -21, -9, 38]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![123, 95, 1, 0, 0], ![93, 7, 0, 1, 0], ![118, 133, 0, 0, 1]] where
  M :=![![![7, -24, -21, -9, 38], ![18, -40, -37, -14, 28], ![28, -24, 2, 5, -112], ![-10, 145, 165, 89, -470], ![-2, 61, 72, 37, -213]]]
  hmulB := by decide  
  f := ![![![-2657, -127, 793, 534, -2086]], ![![-1068, -37, 307, 209, -818]], ![![-2839, -127, 840, 567, -2216]], ![![-1687, -80, 503, 339, -1324]], ![![-3020, -132, 891, 602, -2353]]]
  g := ![![![-7, -20, -21, -9, 38], ![17, -1, -37, -14, 28], ![83, 97, 2, 5, -112], ![178, 307, 165, 89, -470], ![85, 141, 72, 37, -213]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [7, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 150], [0, 1]]
 g := ![![[36, 11], [113, 95], [12, 74], [16], [96, 125], [84], [1]], ![[133, 140], [31, 56], [88, 77], [16], [4, 26], [84], [1]]]
 h' := ![![[50, 150], [115, 112], [67, 104], [133, 136], [83, 147], [65, 27], [144, 50], [0, 1]], ![[0, 1], [128, 39], [133, 47], [138, 15], [34, 4], [56, 124], [77, 101], [50, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [71, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [7, 101, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1933, 3367, 2407, -1566, 1908]
  a := ![-11, 10, -59, -23, 106]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2500, -3100, 2407, -1566, 1908]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -5, -4, -1, 10]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![1, -5, -4, -1, 10]] 
 ![![151, 0, 0, 0, 0], ![137, 1, 0, 0, 0], ![106, 0, 1, 0, 0], ![125, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![1, -5, -4, -1, 10], ![2, -10, -18, -9, 32], ![18, -39, -11, -5, -2], ![10, 15, 0, 16, -100], ![8, -4, 2, 4, -41]]]
  hmulB := by decide  
  f := ![![![137539, 6351, -40858, -27479, 107518]], ![![125151, 5779, -37178, -25004, 97834]], ![![96696, 4465, -28725, -19319, 75590]], ![![113915, 5260, -33840, -22759, 89050]], ![![43876, 2026, -13034, -8766, 34299]]]
  g := ![![![5, -5, -4, -1, 10], ![19, -10, -18, -9, 32], ![48, -39, -11, -5, -2], ![5, 15, 0, 16, -100], ![12, -4, 2, 4, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![17, -33, 18, -3, -4]] ![![7, -24, -21, -9, 38]]
  ![![67, -199, 117, -16, -32]] where
 M := ![![![67, -199, 117, -16, -32]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![67, -199, 117, -16, -32]] ![![1, -5, -4, -1, 10]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![1359, -3020, 1963, 755, -3020]]]
 hmul := by decide  
 g := ![![![![9, -20, 13, 5, -20]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)


lemma PB175I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB175I3 : PrimesBelowBoundCertificateInterval O 103 151 175 where
  m := 9
  g := ![2, 3, 2, 2, 3, 2, 1, 1, 3]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB175I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0, I137N1]
    · exact ![I139N0]
    · exact ![I149N0]
    · exact ![I151N0, I151N1, I151N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
    · exact PBC139
    · exact PBC149
    · exact PBC151
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1225043, 11449]
    · exact ![1295029, 109, 109]
    · exact ![163047361, 113]
    · exact ![260144641, 127]
    · exact ![17161, 17161, 131]
    · exact ![352275361, 137]
    · exact ![51888844699]
    · exact ![73439775749]
    · exact ![22801, 22801, 151]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
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
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
  β := ![I109N1, I109N2, I113N1, I127N1, I131N2, I137N1, I151N2]
  Il := ![[], [I109N1, I109N2], [I113N1], [I127N1], [I131N2], [I137N1], [], [], [I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
