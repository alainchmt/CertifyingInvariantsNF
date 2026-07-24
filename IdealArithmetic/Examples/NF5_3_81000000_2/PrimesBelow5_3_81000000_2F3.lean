
import IdealArithmetic.Examples.NF5_3_81000000_2.RI5_3_81000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -93, -139, -88, -42]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-19, -93, -139, -88, -42]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![31, 92, 87, 1, 0], ![96, 26, 7, 0, 1]] where
  M :=![![![-19, -93, -139, -88, -42], ![-252, -649, -811, -433, -176], ![-1056, -2892, -3722, -2043, -866], ![-5196, -14046, -17925, -9784, -4086], ![-11730, -31797, -40699, -22242, -9351]]]
  hmulB := by decide  
  f := ![![![259, 381, 57, -22, -4]], ![![-24, 199, 299, 29, -44]], ![![-264, -684, -432, -9, 58]], ![![-157, -269, -76, 11, 8]], ![![210, 349, 99, -13, -11]]]
  g := ![![![63, 85, 73, -88, -42], ![281, 409, 356, -433, -176], ![1359, 1940, 1683, -2043, -866], ![6452, 9274, 8055, -9784, -4086], ![14724, 21099, 18316, -22242, -9351]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [78, 85, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 77, 28], [47, 29, 79], [0, 1]]
 g := ![![[20, 35, 49], [62, 24, 40], [34, 41], [104, 90, 19], [31, 11], [1]], ![[71, 26, 51, 51], [91, 25, 88, 31], [32, 102], [1, 74, 70, 70], [44, 19], [60, 57, 19, 17]], ![[31, 91, 11, 14], [36, 55, 80, 3], [90, 42], [63, 47, 13, 36], [99, 57], [2, 84, 90, 90]]]
 h' := ![![[45, 77, 28], [86, 52, 100], [102, 23, 88], [20, 11, 83], [28, 30, 33], [29, 22, 92], [0, 1]], ![[47, 29, 79], [55, 22, 76], [82, 73, 93], [44, 65, 40], [6, 95, 85], [96, 55, 74], [45, 77, 28]], ![[0, 1], [22, 33, 38], [16, 11, 33], [9, 31, 91], [24, 89, 96], [91, 30, 48], [47, 29, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 15], []]
 b := ![[], [16, 11, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [78, 85, 15, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5594592, -15209650, -19558851, -10703804, -4552667]
  a := ![0, -1, -3, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7133452, 10167380, 8818138, -10703804, -4552667]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-259, -381, -57, 22, 4]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-259, -381, -57, 22, 4]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![79, 20, 1, 0, 0], ![25, 0, 0, 1, 0], ![14, 56, 0, 0, 1]] where
  M :=![![![-259, -381, -57, 22, 4], ![24, -199, -299, -29, 44], ![264, 684, 432, 9, -58], ![-348, -606, -177, 26, 18], ![-78, -381, -371, -30, 55]]]
  hmulB := by decide  
  f := ![![![19, 93, 139, 88, 42]], ![![252, 649, 811, 433, 176]], ![![71, 217, 289, 165, 72]], ![![53, 153, 200, 112, 48]], ![![244, 649, 823, 446, 185]]]
  g := ![![![34, 5, -57, 22, 4], ![222, 31, -299, -29, 44], ![-311, -44, 432, 9, -58], ![119, 18, -177, 26, 18], ![273, 37, -371, -30, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P1 : CertificateIrreducibleZModOfList' 107 2 2 6 [55, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 106], [0, 1]]
 g := ![![[98, 23], [48, 37], [13], [56, 81], [69], [67, 1]], ![[34, 84], [66, 70], [13], [26, 26], [69], [27, 106]]]
 h' := ![![[67, 106], [35, 39], [28, 12], [23, 86], [19, 98], [60, 47], [0, 1]], ![[0, 1], [80, 68], [83, 95], [7, 21], [58, 9], [106, 60], [67, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [62, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N1 : CertifiedPrimeIdeal' SI107N1 107 where
  n := 2
  hpos := by decide
  P := [55, 40, 1]
  hirr := P107P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1862, -7624, 774, -1643, 1437]
  a := ![3, -64, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-393, -968, 774, -1643, 1437]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N1 B_one_repr
lemma NI107N1 : Nat.card (O ⧸ I107N1) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-19, -93, -139, -88, -42]] ![![-259, -381, -57, 22, 4]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1763, -2157, -1542, -93, 228]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-1763, -2157, -1542, -93, 228]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![12, 75, 78, 1, 0], ![77, 24, 48, 0, 1]] where
  M :=![![![-1763, -2157, -1542, -93, 228], ![1368, 1657, 1170, 54, -186], ![-1116, -1422, -1079, -132, 108], ![648, 504, 66, -323, -264], ![-234, -945, -1350, -825, -377]]]
  hmulB := by decide  
  f := ![![![37, 51, -6, -15, 6]], ![![36, 127, 126, 36, -30]], ![![-180, -414, -287, -84, 72]], ![![-96, -195, -114, -35, 30]], ![![-49, -126, -108, -42, 31]]]
  g := ![![![-167, -6, -48, -93, 228], ![138, 19, 54, 54, -186], ![-72, 54, 37, -132, 108], ![228, 285, 348, -323, -264], ![355, 642, 744, -825, -377]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [57, 24, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 14, 77], [46, 94, 32], [0, 1]]
 g := ![![[66, 33, 3], [14, 29], [47, 40, 9], [67, 87, 29], [25, 100], [1]], ![[95, 41, 20, 76], [36, 27], [87, 94, 50, 65], [50, 53, 50, 17], [95, 45], [38, 0, 88, 41]], ![[65, 72, 51, 99], [6, 31], [47, 22, 61, 54], [41, 105, 12, 24], [27, 97], [47, 59, 1, 68]]]
 h' := ![![[53, 14, 77], [10, 85, 60], [46, 96, 47], [105, 51, 106], [80, 33, 47], [52, 85, 99], [0, 1]], ![[46, 94, 32], [47, 46, 86], [79, 70, 38], [23, 30, 48], [44, 60, 92], [106, 0, 46], [53, 14, 77]], ![[0, 1], [63, 87, 72], [80, 52, 24], [66, 28, 64], [50, 16, 79], [45, 24, 73], [46, 94, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 43], []]
 b := ![[], [83, 90, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [57, 24, 10, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-516688, -1400871, -1792397, -979739, -411628]
  a := ![1, -3, -1, -1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![393904, 751914, 865921, -979739, -411628]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -5, -4, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-1, -5, -4, 1, 0]] 
 ![![109, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![93, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![98, 0, 0, 0, 1]] where
  M :=![![![-1, -5, -4, 1, 0], ![0, -1, -4, -4, 2], ![12, 30, 25, 10, -8], ![-48, -108, -80, -31, 20], ![54, 111, 68, 25, -27]]]
  hmulB := by decide  
  f := ![![![-11929, -14605, -10432, -609, 1558]], ![![-352, -431, -308, -18, 46]], ![![-10245, -12543, -8959, -523, 1338]], ![![-6952, -8512, -6080, -355, 908]], ![![-10712, -13115, -9368, -547, 1399]]]
  g := ![![![3, -5, -4, 1, 0], ![4, -1, -4, -4, 2], ![-21, 30, 25, 10, -8], ![72, -108, -80, -31, 20], ![-52, 111, 68, 25, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 32, 14, 0, -2]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![23, 32, 14, 0, -2]] 
 ![![109, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![63, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![23, 32, 14, 0, -2], ![-12, -7, 2, 0, 0], ![0, -12, -7, 2, 0], ![0, 0, -10, -7, 4], ![12, 36, 30, 8, -7]]]
  hmulB := by decide  
  f := ![![![35, 64, 74, 28, 6]], ![![9, 17, 20, 8, 2]], ![![14, 28, 33, 14, 4]], ![![33, 72, 88, 41, 14]], ![![49, 116, 144, 72, 27]]]
  g := ![![![-11, 32, 14, 0, -2], ![1, -7, 2, 0, 0], ![4, -12, -7, 2, 0], ![5, 0, -10, -7, 4], ![-19, 36, 30, 8, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-1763, -2157, -1542, -93, 228]] ![![-1, -5, -4, 1, 0]]
  ![![35, 64, 74, 28, 6]] where
 M := ![![![35, 64, 74, 28, 6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![35, 64, 74, 28, 6]] ![![23, 32, 14, 0, -2]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0, 0, 0]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]] where
  M :=![![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 5 2 6 [66, 102, 85, 55, 109, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 44, 3, 107, 101], [85, 1, 65, 102, 53], [111, 77, 34, 35, 30], [59, 103, 11, 95, 42], [0, 1]]
 g := ![![[74, 92, 39, 1, 106], [23, 14, 27, 83], [108, 17, 27, 2], [110, 109, 67, 81], [74, 4, 1], []], ![[2, 106, 107, 77, 83, 15, 92, 68], [104, 11, 12, 44], [83, 68, 38, 82], [112, 77, 12, 105], [54, 50, 25, 23, 80, 78, 30, 17], [50, 16, 23, 38, 111, 72, 101, 80]], ![[69, 94, 104, 108, 109, 6, 19, 102], [3, 36, 49, 112], [12, 92, 39, 7], [102, 17, 27, 77], [35, 72, 47, 9, 42, 54, 92, 105], [110, 78, 59, 25, 64, 1, 74, 56]], ![[89, 104, 92, 32, 46, 40, 99, 32], [47, 81, 51, 72], [26, 20, 64, 57], [38, 46, 100, 44], [45, 47, 43, 63, 82, 40, 98, 87], [96, 82, 31, 0, 62, 68, 4, 106]], ![[95, 73, 105, 68, 12, 76, 25, 59], [18, 24, 27, 30], [42, 17, 32, 63], [55, 42, 41, 53], [46, 111, 22, 32, 56, 64, 86, 73], [106, 40, 92, 22, 41, 38, 69, 73]]]
 h' := ![![[88, 44, 3, 107, 101], [68, 32, 83, 55, 28], [111, 22, 52, 90, 14], [32, 77, 73, 101, 51], [88, 98, 16, 8, 104], [0, 0, 0, 1], [0, 1]], ![[85, 1, 65, 102, 53], [22, 1, 32, 95, 22], [85, 70, 20, 110, 65], [79, 81, 43, 73, 46], [37, 18, 5, 30, 61], [59, 69, 38, 83, 11], [88, 44, 3, 107, 101]], ![[111, 77, 34, 35, 30], [69, 63, 94, 98, 10], [43, 49, 109, 2, 98], [48, 0, 81, 104, 81], [0, 17, 112, 97, 90], [55, 109, 64, 39, 14], [85, 1, 65, 102, 53]], ![[59, 103, 11, 95, 42], [64, 38, 40, 4, 41], [51, 102, 15, 94, 33], [80, 41, 3, 1, 31], [21, 66, 78, 51, 48], [97, 71, 52, 48, 46], [111, 77, 34, 35, 30]], ![[0, 1], [19, 92, 90, 87, 12], [23, 96, 30, 43, 16], [14, 27, 26, 60, 17], [49, 27, 15, 40, 36], [68, 90, 72, 55, 42], [59, 103, 11, 95, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 112, 15, 3], [], [], []]
 b := ![[], [39, 73, 84, 99, 85], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 5
  hpos := by decide
  P := [66, 102, 85, 55, 109, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![40782195915190, 110517815903780, 141363311597726, 77244538414158, 32417013072214]
  a := ![1, 19, 4, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![360904388630, 978033769060, 1251002757502, 683579985966, 286876221878]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 18424351793 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 45, 20, 1, -2]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![41, 45, 20, 1, -2]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![113, 8, 114, 1, 0], ![36, 45, 47, 0, 1]] where
  M :=![![![41, 45, 20, 1, -2], ![-12, 11, 16, 6, 2], ![12, 18, 47, 30, 12], ![72, 192, 228, 131, 60], ![174, 477, 588, 309, 125]]]
  hmulB := by decide  
  f := ![![![11, 15, 16, 5, -4]], ![![-24, -49, -40, -12, 10]], ![![60, 126, 89, 30, -24]], ![![61, 121, 90, 30, -24]], ![![18, 36, 25, 9, -7]]]
  g := ![![![0, 1, 0, 1, -2], ![-6, -1, -6, 6, 2], ![-30, -6, -31, 30, 12], ![-133, -28, -138, 131, 60], ![-309, -60, -319, 309, 125]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [66, 48, 100, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 77, 21], [62, 49, 106], [0, 1]]
 g := ![![[14, 59, 38], [68, 66, 60], [112, 108, 9], [67, 30, 84], [9, 73, 94], [1]], ![[125, 81, 15, 72], [20, 38, 101, 84], [101, 6, 66, 74], [21, 33, 75, 68], [17, 122, 106, 36], [58, 69, 1, 117]], ![[80, 85, 55, 28], [95, 67, 54, 39], [34, 11, 11, 110], [93, 117, 12, 89], [88, 91, 43, 63], [103, 72, 73, 10]]]
 h' := ![![[92, 77, 21], [84, 41, 61], [101, 90, 21], [23, 41, 3], [41, 122, 46], [61, 79, 27], [0, 1]], ![[62, 49, 106], [16, 47, 40], [124, 34, 125], [21, 31, 119], [6, 70, 117], [33, 47, 61], [92, 77, 21]], ![[0, 1], [121, 39, 26], [53, 3, 108], [110, 55, 5], [103, 62, 91], [9, 1, 39], [62, 49, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 13], []]
 b := ![[], [34, 100, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [66, 48, 100, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16880367, -46256052, -60260985, -33099613, -14528509]
  a := ![-1, 0, -4, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![33436238, 6868691, 34613660, -33099613, -14528509]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -15, -16, -5, 4]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-11, -15, -16, -5, 4]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![19, 13, 1, 0, 0], ![7, 104, 0, 1, 0], ![82, 83, 0, 0, 1]] where
  M :=![![![-11, -15, -16, -5, 4], ![24, 49, 40, 12, -10], ![-60, -126, -89, -30, 24], ![144, 300, 204, 79, -60], ![-150, -315, -216, -93, 67]]]
  hmulB := by decide  
  f := ![![![-41, -45, -20, -1, 2]], ![![12, -11, -16, -6, -2]], ![![-5, -8, -5, -1, 0]], ![![7, -13, -16, -6, -2]], ![![-20, -40, -28, -7, -1]]]
  g := ![![![0, 3, -16, -5, 4], ![0, -7, 40, 12, -10], ![-1, 17, -89, -30, 24], ![5, -44, 204, 79, -60], ![-7, 52, -216, -93, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [87, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 126], [0, 1]]
 g := ![![[0, 73], [0, 4], [0, 19], [0, 64], [0, 76], [0, 1]], ![[0, 54], [0, 123], [0, 108], [0, 63], [0, 51], [0, 126]]]
 h' := ![![[0, 126], [0, 33], [0, 125], [0, 20], [0, 119], [0, 40], [0, 1]], ![[0, 1], [0, 94], [0, 2], [0, 107], [0, 8], [0, 87], [0, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [0, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [87, 0, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7713, -16608, -10904, -4212, 4172]
  a := ![0, 0, 4, -10, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-891, 1708, -10904, -4212, 4172]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![41, 45, 20, 1, -2]] ![![-11, -15, -16, -5, 4]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![-127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53, -62, -53, -13, 12]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-53, -62, -53, -13, 12]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![8, 113, 89, 1, 0], ![37, 19, 92, 0, 1]] where
  M :=![![![-53, -62, -53, -13, 12], ![72, 127, 105, 31, -26], ![-156, -318, -232, -77, 62], ![372, 774, 535, 202, -154], ![-384, -810, -551, -233, 171]]]
  hmulB := by decide  
  f := ![![![-7, -2, 3, 1, 0]], ![![0, -7, -1, 3, 2]], ![![12, 30, 26, 13, 6]], ![![8, 15, 18, 12, 6]], ![![7, 21, 21, 11, 5]]]
  g := ![![![-3, 9, 0, -13, 12], ![6, -22, -2, 31, -26], ![-14, 55, 7, -77, 62], ![34, -146, -25, 202, -154], ![-37, 170, 34, -233, 171]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [69, 115, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 85, 74], [89, 45, 57], [0, 1]]
 g := ![![[49, 37, 49], [43, 100, 123], [125, 16], [26, 3], [25, 15], [114, 1], []], ![[66, 76, 40, 105], [58, 75, 67, 27], [22, 60], [31, 62], [20, 99], [23, 60], [53, 105]], ![[90, 50, 39, 6], [98, 115, 60, 116], [83, 109], [75, 7], [50, 45], [77, 20], [70, 105]]]
 h' := ![![[25, 85, 74], [46, 6, 7], [42, 5, 75], [105, 65, 127], [14, 51, 38], [125, 52, 43], [0, 0, 1], [0, 1]], ![[89, 45, 57], [63, 22, 104], [52, 6, 77], [103, 96, 45], [43, 39, 113], [84, 0, 19], [112, 80, 45], [25, 85, 74]], ![[0, 1], [78, 103, 20], [49, 120, 110], [76, 101, 90], [50, 41, 111], [116, 79, 69], [78, 51, 85], [89, 45, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 31], []]
 b := ![[], [76, 11, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [69, 115, 17, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9106034, -24910415, -32327304, -17734270, -7720311]
  a := ![13, -1, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3194043, 16227084, 17223598, -17734270, -7720311]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -2, 3, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-7, -2, 3, 1, 0]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![64, 42, 1, 0, 0], ![63, 3, 0, 1, 0], ![3, 13, 0, 0, 1]] where
  M :=![![![-7, -2, 3, 1, 0], ![0, -7, -1, 3, 2], ![12, 30, 26, 13, 6], ![36, 102, 133, 68, 26], ![72, 198, 267, 151, 65]]]
  hmulB := by decide  
  f := ![![![-53, -62, -53, -13, 12]], ![![72, 127, 105, 31, -26]], ![![-4, 8, 6, 3, -2]], ![![-21, -21, -19, -4, 4]], ![![3, 5, 5, 1, -1]]]
  g := ![![![-2, -1, 3, 1, 0], ![-1, 0, -1, 3, 2], ![-19, -9, 26, 13, 6], ![-98, -46, 133, 68, 26], ![-204, -94, 267, 151, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [75, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 130], [0, 1]]
 g := ![![[127, 7], [51, 9], [63], [34], [113], [3], [1]], ![[0, 124], [0, 122], [63], [34], [113], [3], [1]]]
 h' := ![![[38, 130], [105, 111], [114, 128], [56, 71], [95, 77], [29, 47], [56, 38], [0, 1]], ![[0, 1], [0, 20], [0, 3], [3, 60], [8, 54], [112, 84], [59, 93], [38, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [85, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [75, 93, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![133, 537, 2145, 1118, 1328]
  a := ![-1, -3, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1615, -841, 2145, 1118, 1328]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-53, -62, -53, -13, 12]] ![![-7, -2, 3, 1, 0]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-119, -192, -141, -11, 22]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-119, -192, -141, -11, 22]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![75, 78, 130, 1, 0], ![57, 105, 15, 0, 1]] where
  M :=![![![-119, -192, -141, -11, 22], ![132, 211, 127, 13, -22], ![-132, -198, -106, -27, 26], ![156, 258, 165, 76, -54], ![-96, -228, -185, -93, 63]]]
  hmulB := by decide  
  f := ![![![-7, -12, -7, 1, 2]], ![![12, 23, 19, 7, 2]], ![![12, 42, 60, 33, 14]], ![![15, 48, 66, 37, 16]], ![![9, 21, 23, 12, 5]]]
  g := ![![![-4, -12, 7, -11, 22], ![3, 11, -9, 13, -22], ![3, -6, 22, -27, 26], ![-18, 0, -65, 76, -54], ![24, 3, 80, -93, 63]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [26, 1, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [111, 129, 23], [121, 7, 114], [0, 1]]
 g := ![![[1, 8, 64], [44, 16], [0, 4], [41, 27, 81], [64, 50], [95, 1], []], ![[13, 101, 122, 53], [133, 136], [14, 30], [32, 107, 78, 102], [10, 65], [4, 49], [19, 118]], ![[40, 12, 62, 47], [0, 130], [61, 118], [111, 62, 46, 114], [123, 34], [60, 64], [65, 118]]]
 h' := ![![[111, 129, 23], [8, 100, 8], [78, 116, 133], [30, 95, 135], [133, 15, 128], [133, 16, 119], [0, 0, 1], [0, 1]], ![[121, 7, 114], [97, 26, 27], [33, 29, 37], [73, 61, 116], [23, 81, 8], [3, 0, 105], [45, 69, 7], [111, 129, 23]], ![[0, 1], [88, 11, 102], [122, 129, 104], [8, 118, 23], [58, 41, 1], [70, 121, 50], [73, 68, 129], [121, 7, 114]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 5], []]
 b := ![[], [50, 34, 107], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [26, 1, 42, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4583522, 13481430, 19540684, 11036864, 5959720]
  a := ![3, 0, 7, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8488214, -10753026, -10982828, 11036864, 5959720]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![581, 710, 508, 30, -76]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![581, 710, 508, 30, -76]] 
 ![![137, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![98, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![581, 710, 508, 30, -76], ![-456, -559, -400, -24, 60], ![360, 444, 317, 20, -48], ![-288, -360, -256, -19, 40], ![-60, -66, -48, 2, 5]]]
  hmulB := by decide  
  f := ![![![85, 74, -60, -22, 4]], ![![7, 7, -4, -2, 0]], ![![8, 4, -11, -4, 0]], ![![58, 44, -56, -23, 0]], ![![-7, -20, -28, -16, -7]]]
  g := ![![![-133, 710, 508, 30, -76], ![105, -559, -400, -24, 60], ![-84, 444, 317, 20, -48], ![70, -360, -256, -19, 40], ![9, -66, -48, 2, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -9, -8, -7, 4]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![-5, -9, -8, -7, 4]] 
 ![![137, 0, 0, 0, 0], ![133, 1, 0, 0, 0], ![121, 0, 1, 0, 0], ![73, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-5, -9, -8, -7, 4], ![24, 55, 44, 20, -14], ![-84, -186, -135, -54, 40], ![240, 516, 360, 145, -108], ![-282, -597, -412, -171, 125]]]
  hmulB := by decide  
  f := ![![![10079, 12339, 8820, 515, -1318]], ![![9727, 11908, 8512, 497, -1272]], ![![8947, 10953, 7829, 457, -1170]], ![![5335, 6531, 4668, 272, -698]], ![![1241, 1518, 1084, 62, -163]]]
  g := ![![![19, -9, -8, -7, 4], ![-101, 55, 44, 20, -14], ![323, -186, -135, -54, 40], ![-881, 516, 360, 145, -108], ![1017, -597, -412, -171, 125]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-119, -192, -141, -11, 22]] ![![581, 710, 508, 30, -76]]
  ![![-30499, -37258, -26589, -1529, 3962]] where
 M := ![![![-30499, -37258, -26589, -1529, 3962]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![-30499, -37258, -26589, -1529, 3962]] ![![-5, -9, -8, -7, 4]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![7535, 16577, 11371, 4932, -3562]]]
 hmul := by decide  
 g := ![![![![55, 121, 83, 36, -26]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 444, 444, 46, -70]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![89, 444, 444, 46, -70]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![62, 128, 28, 1, 0], ![105, 46, 20, 0, 1]] where
  M :=![![![89, 444, 444, 46, -70], ![-420, -961, -560, -46, 92], ![552, 960, 373, 84, -92], ![-552, -828, -336, -271, 168], ![228, 504, 524, 378, -225]]]
  hmulB := by decide  
  f := ![![![-853, -1044, -748, -46, 110]], ![![660, 797, 560, 22, -92]], ![![-552, -720, -561, -84, 44]], ![![118, 124, 68, -19, -28]], ![![-507, -634, -468, -44, 57]]]
  g := ![![![33, -16, 4, 46, -70], ![-52, 5, -8, -46, 92], ![36, -40, -1, 84, -92], ![-10, 188, 28, -271, 168], ![3, -270, -40, 378, -225]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [38, 137, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 25, 97], [19, 113, 42], [0, 1]]
 g := ![![[39, 73, 67], [28, 38, 63], [18, 99], [129, 38, 127], [44, 38], [66, 1], []], ![[97, 20, 103, 10], [93, 18, 61, 10], [60, 52], [32, 71, 15, 84], [113, 125], [25, 120], [66, 96]], ![[43, 23, 88, 11], [111, 75, 51, 78], [61, 127], [108, 6, 24, 11], [74, 66], [26, 69], [121, 96]]]
 h' := ![![[47, 25, 97], [48, 102, 117], [129, 61, 87], [102, 116, 51], [32, 18, 108], [133, 94, 49], [0, 0, 1], [0, 1]], ![[19, 113, 42], [22, 124, 41], [57, 24, 41], [35, 7, 57], [0, 39, 50], [47, 121, 60], [118, 85, 113], [47, 25, 97]], ![[0, 1], [124, 52, 120], [46, 54, 11], [1, 16, 31], [88, 82, 120], [26, 63, 30], [72, 54, 25], [19, 113, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 115], []]
 b := ![[], [115, 13, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [38, 137, 73, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3196329, 8840575, 11691776, 6448391, 2927097]
  a := ![1, 1, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5064382, -6843165, -1636008, 6448391, 2927097]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![853, 1044, 748, 46, -110]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![853, 1044, 748, 46, -110]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![85, 111, 1, 0, 0], ![17, 135, 0, 1, 0], ![58, 36, 0, 0, 1]] where
  M :=![![![853, 1044, 748, 46, -110], ![-660, -797, -560, -22, 92], ![552, 720, 561, 84, -44], ![-264, -108, 144, 253, 168], ![228, 768, 1052, 618, 275]]]
  hmulB := by decide  
  f := ![![![-89, -444, -444, -46, 70]], ![![420, 961, 560, 46, -92]], ![![277, 489, 173, 8, -30]], ![![401, 885, 492, 41, -82]], ![![70, 60, -44, -10, 7]]]
  g := ![![![-411, -606, 748, 46, -110], ![302, 439, -560, -22, 92], ![-331, -513, 561, 84, -44], ![-191, -405, 144, 253, 168], ![-832, -1506, 1052, 618, 275]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P1 : CertificateIrreducibleZModOfList' 139 2 2 7 [123, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 138], [0, 1]]
 g := ![![[72, 25], [22, 96], [63], [133, 4], [137], [71], [1]], ![[99, 114], [109, 43], [63], [15, 135], [137], [71], [1]]]
 h' := ![![[40, 138], [74, 5], [77, 42], [43, 52], [111, 137], [2, 89], [16, 40], [0, 1]], ![[0, 1], [135, 134], [89, 97], [38, 87], [31, 2], [87, 50], [87, 99], [40, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [129, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N1 : CertifiedPrimeIdeal' SI139N1 139 where
  n := 2
  hpos := by decide
  P := [123, 99, 1]
  hirr := P139P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![433, -192, -160, 110, 6]
  a := ![4, 0, -1, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![85, 18, -160, 110, 6]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N1 B_one_repr
lemma NI139N1 : Nat.card (O ⧸ I139N1) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![89, 444, 444, 46, -70]] ![![853, 1044, 748, 46, -110]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![-139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2561, -3220, -2297, -187, 366]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-2561, -3220, -2297, -187, 366]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![94, 13, 1, 0, 0], ![119, 74, 0, 1, 0], ![51, 19, 0, 0, 1]] where
  M :=![![![-2561, -3220, -2297, -187, 366], ![2196, 2929, 2083, 265, -374], ![-2244, -3414, -2416, -535, 530], ![3180, 5706, 4001, 1294, -1070], ![-2088, -4728, -3317, -1477, 1029]]]
  hmulB := by decide  
  f := ![![![8483, 16760, 7181, -267, -902]], ![![-5412, -5047, 2963, 867, -534]], ![![4858, 10043, 4707, -98, -604]], ![![4157, 11032, 7286, 217, -996]], ![![2193, 5095, 2875, 25, -383]]]
  g := ![![![1456, 225, -2297, -187, 366], ![-1383, -246, 2083, 265, -374], ![1755, 386, -2416, -535, 530], ![-3170, -817, 4001, 1294, -1070], ![2906, 860, -3317, -1477, 1029]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [81, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 148], [0, 1]]
 g := ![![[78, 46], [54], [142, 4], [4], [48, 73], [24], [1]], ![[0, 103], [54], [51, 145], [4], [138, 76], [24], [1]]]
 h' := ![![[89, 148], [43, 33], [120, 90], [21, 2], [135, 2], [147, 85], [68, 89], [0, 1]], ![[0, 1], [0, 116], [84, 59], [50, 147], [15, 147], [113, 64], [92, 60], [89, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [30, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [81, 60, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![47608, 145048, 222203, 128497, 74683]
  a := ![7, 2, -24, 0, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-268050, -91754, 222203, 128497, 74683]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -2, -1, -5, 2]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![5, -2, -1, -5, 2]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![60, 0, 1, 0, 0], ![0, 60, 0, 1, 0], ![107, 0, 0, 0, 1]] where
  M :=![![![5, -2, -1, -5, 2], ![12, 35, 23, 13, -10], ![-60, -138, -102, -47, 26], ![156, 330, 205, 80, -94], ![-252, -558, -449, -203, 67]]]
  hmulB := by decide  
  f := ![![![361, 622, 217, -17, -26]], ![![-156, -29, 215, 35, -34]], ![![144, 246, 84, -7, -10]], ![![-60, -6, 89, 14, -14]], ![![259, 448, 158, -12, -19]]]
  g := ![![![-1, 2, -1, -5, 2], ![-2, -5, 23, 13, -10], ![22, 18, -102, -47, 26], ![-14, -30, 205, 80, -94], ![131, 78, -449, -203, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P1 : CertificateIrreducibleZModOfList' 149 2 2 7 [111, 128, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 148], [0, 1]]
 g := ![![[28, 47], [30], [59, 35], [132], [139, 102], [143], [1]], ![[121, 102], [30], [49, 114], [132], [46, 47], [143], [1]]]
 h' := ![![[21, 148], [146, 135], [7, 103], [118, 83], [67, 70], [24, 129], [38, 21], [0, 1]], ![[0, 1], [1, 14], [84, 46], [73, 66], [47, 79], [51, 20], [32, 128], [21, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [142, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N1 : CertifiedPrimeIdeal' SI149N1 149 where
  n := 2
  hpos := by decide
  P := [111, 128, 1]
  hirr := P149P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7224, 21030, 29303, 16964, 8356]
  a := ![1, 3, -7, -1, -8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17752, -6690, 29303, 16964, 8356]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N1 B_one_repr
lemma NI149N1 : Nat.card (O ⧸ I149N1) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -8, -2, 0, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![-5, -8, -2, 0, 0]] 
 ![![149, 0, 0, 0, 0], ![136, 1, 0, 0, 0], ![129, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![108, 0, 0, 0, 1]] where
  M :=![![![-5, -8, -2, 0, 0], ![0, -5, -8, -2, 0], ![0, 0, -7, -8, -4], ![-24, -60, -68, -35, -16], ![-48, -132, -164, -86, -33]]]
  hmulB := by decide  
  f := ![![![7343, 8968, 6382, 368, -952]], ![![6664, 8139, 5792, 334, -864]], ![![6387, 7800, 5551, 320, -828]], ![![1850, 2260, 1608, 93, -240]], ![![5316, 6492, 4620, 266, -689]]]
  g := ![![![9, -8, -2, 0, 0], ![12, -5, -8, -2, 0], ![11, 0, -7, -8, -4], ![134, -60, -68, -35, -16], ![308, -132, -164, -86, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-2561, -3220, -2297, -187, 366]] ![![5, -2, -1, -5, 2]]
  ![![-35029, -56530, -39874, -10354, 9456]] where
 M := ![![![-35029, -56530, -39874, -10354, 9456]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![-35029, -56530, -39874, -10354, 9456]] ![![-5, -8, -2, 0, 0]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![-30247, -64070, -45296, -18774, 13112]]]
 hmul := by decide  
 g := ![![![![-203, -430, -304, -126, 88]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-203, -234, -163, 1, 26]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-203, -234, -163, 1, 26]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![6, 36, 144, 1, 0], ![21, 129, 145, 0, 1]] where
  M :=![![![-203, -234, -163, 1, 26], ![156, 187, 157, 19, 2], ![12, 186, 236, 171, 38], ![228, 582, 927, 502, 342], ![1020, 2586, 2989, 1575, 483]]]
  hmulB := by decide  
  f := ![![![19, 426, 533, 47, -78]], ![![-468, -1151, -697, -13, 94]], ![![564, 942, 246, -39, -26]], ![![426, 642, 93, -38, -6]], ![![141, -27, -289, -42, 45]]]
  g := ![![![-5, -24, -27, 1, 26], ![0, -5, -19, 19, 2], ![-12, -72, -198, 171, 38], ![-66, -408, -801, 502, 342], ![-123, -771, -1946, 1575, 483]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [108, 144, 68, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [114, 77, 109], [120, 73, 42], [0, 1]]
 g := ![![[108, 63, 86], [36, 32, 62], [94, 23, 76], [148, 10], [139, 140, 84], [83, 1], []], ![[95, 30, 96, 126], [84, 21, 108, 83], [105, 39, 16, 131], [31, 19], [28, 140, 64, 146], [129, 44], [118, 103]], ![[62, 42, 57, 72], [28, 101, 24, 125], [47, 7, 72, 105], [7, 84], [10, 101, 40, 123], [119, 40], [34, 103]]]
 h' := ![![[114, 77, 109], [38, 135, 122], [116, 134, 106], [65, 48, 128], [88, 52, 37], [96, 20, 101], [0, 0, 1], [0, 1]], ![[120, 73, 42], [117, 139, 65], [126, 53, 147], [43, 144, 80], [89, 146, 64], [44, 134, 40], [101, 10, 73], [114, 77, 109]], ![[0, 1], [29, 28, 115], [26, 115, 49], [77, 110, 94], [94, 104, 50], [32, 148, 10], [7, 141, 77], [120, 73, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 72], []]
 b := ![[], [20, 29, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [108, 144, 68, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5013615, 13580340, 17369042, 9493395, 3984313]
  a := ![3, 0, 2, 5, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-898128, -5577207, -12764273, 9493395, 3984313]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 426, 533, 47, -78]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![19, 426, 533, 47, -78]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![149, 7, 1, 0, 0], ![14, 100, 0, 1, 0], ![101, 31, 0, 0, 1]] where
  M :=![![![19, 426, 533, 47, -78], ![-468, -1151, -697, -13, 94], ![564, 942, 246, -39, -26], ![-156, 174, 513, 64, -78], ![-516, -1134, -589, 3, 77]]]
  hmulB := by decide  
  f := ![![![-203, -234, -163, 1, 26]], ![![156, 187, 157, 19, 2]], ![![-193, -221, -152, 3, 26]], ![![86, 106, 95, 16, 6]], ![![-97, -101, -57, 15, 21]]]
  g := ![![![-478, -37, 533, 47, -78], ![623, 14, -697, -13, 94], ![-218, 26, 246, -39, -26], ![-461, -49, 513, 64, -78], ![526, 2, -589, 3, 77]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [23, 136, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 150], [0, 1]]
 g := ![![[65, 29], [52, 95], [6, 118], [94], [133, 32], [74], [1]], ![[47, 122], [118, 56], [115, 33], [94], [9, 119], [74], [1]]]
 h' := ![![[15, 150], [12, 123], [13, 104], [114, 32], [112, 68], [35, 118], [128, 15], [0, 1]], ![[0, 1], [45, 28], [63, 47], [141, 119], [75, 83], [144, 33], [51, 136], [15, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [125, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [23, 136, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24266, 80516, 135026, 80811, 50305]
  a := ![3, 2, -13, 4, -21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-174217, -69571, 135026, 80811, 50305]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-203, -234, -163, 1, 26]] ![![19, 426, 533, 47, -78]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)


lemma PB441I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB441I3 : PrimesBelowBoundCertificateInterval O 103 151 441 where
  m := 9
  g := ![2, 3, 1, 2, 2, 3, 2, 3, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB441I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2]
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1]
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
    · exact ![18424351793]
    · exact ![2048383, 16129]
    · exact ![2248091, 17161]
    · exact ![2571353, 137, 137]
    · exact ![2685619, 19321]
    · exact ![22201, 22201, 149]
    · exact ![3442951, 22801]
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
      exact NI137N2
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I109N1, I109N2, I137N1, I137N2, I149N2]
  Il := ![[], [I109N1, I109N2], [], [], [], [I137N1, I137N2], [], [I149N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
