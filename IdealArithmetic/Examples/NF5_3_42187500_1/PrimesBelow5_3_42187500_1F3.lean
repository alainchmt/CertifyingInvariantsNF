
import IdealArithmetic.Examples.NF5_3_42187500_1.RI5_3_42187500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1163, -144, 45, 134, 242]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-1163, -144, 45, 134, 242]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![55, 56, 32, 1, 0], ![43, 2, 51, 0, 1]] where
  M :=![![![-1163, -144, 45, 134, 242], ![-3764, -447, 151, 440, 778], ![-4173, -495, 180, 489, 880], ![-8931, -1017, 385, 1060, 1858], ![-8815, -1007, 394, 1045, 1855]]]
  hmulB := by decide  
  f := ![![![4, -17, 16, 11, -12]], ![![169, -38, -74, -3, 32]], ![![-323, 131, 68, -39, -6]], ![![-7, 10, -9, -7, 8]], ![![-147, 54, 37, -14, -7]]]
  g := ![![![-177, -76, -155, 134, 242], ![-574, -249, -501, 440, 778], ![-644, -277, -564, 489, 880], ![-1375, -599, -1199, 1060, 1858], ![-1365, -591, -1193, 1045, 1855]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [20, 104, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 59, 105], [9, 47, 2], [0, 1]]
 g := ![![[2, 10, 79], [51, 102, 101], [20, 53], [69, 39, 47], [90, 105], [1]], ![[17, 101, 36, 49], [43, 40, 7, 14], [66, 37], [12, 98, 67, 86], [52, 48], [68, 13, 100, 99]], ![[94, 38, 38, 96], [54, 13, 23, 38], [34, 34], [42, 73, 0, 78], [25, 16], [2, 59, 102, 8]]]
 h' := ![![[67, 59, 105], [50, 91, 87], [42, 53, 84], [11, 43, 38], [98, 83, 58], [87, 3, 76], [0, 1]], ![[9, 47, 2], [63, 26, 55], [106, 16, 97], [28, 52, 95], [105, 51, 99], [17, 22, 35], [67, 59, 105]], ![[0, 1], [25, 97, 72], [62, 38, 33], [97, 12, 81], [104, 80, 57], [47, 82, 103], [9, 47, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80, 65], []]
 b := ![[], [48, 64, 86], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [20, 104, 31, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38496410, 11576188, -4611176, -4183780, -15181452]
  a := ![15, -20, -8, 12, -60]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8611278, 2581596, 8444148, -4183780, -15181452]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 17, -16, -11, 12]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-4, 17, -16, -11, 12]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![91, 22, 1, 0, 0], ![23, 65, 0, 1, 0], ![44, 19, 0, 0, 1]] where
  M :=![![![-4, 17, -16, -11, 12], ![-169, 38, 74, 3, -32], ![323, -131, -68, 39, 6], ![97, 59, -125, -62, 84], ![-234, 96, 49, -24, -9]]]
  hmulB := by decide  
  f := ![![![1163, 144, -45, -134, -242]], ![![3764, 447, -151, -440, -778]], ![![1802, 219, -71, -209, -374]], ![![2620, 312, -105, -306, -542]], ![![1229, 148, -49, -143, -255]]]
  g := ![![![11, 8, -16, -11, 12], ![-52, -11, 74, 3, -32], ![50, -12, -68, 39, 6], ![86, 49, -125, -62, 84], ![-35, 7, 49, -24, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P1 : CertificateIrreducibleZModOfList' 107 2 2 6 [80, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [102, 106], [0, 1]]
 g := ![![[87, 62], [13, 14], [13], [48, 83], [29], [102, 1]], ![[98, 45], [50, 93], [13], [61, 24], [29], [97, 106]]]
 h' := ![![[102, 106], [30, 94], [67, 11], [12, 21], [69, 46], [79, 52], [0, 1]], ![[0, 1], [95, 13], [12, 96], [14, 86], [53, 61], [33, 55], [102, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [78, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N1 : CertifiedPrimeIdeal' SI107N1 107 where
  n := 2
  hpos := by decide
  P := [80, 5, 1]
  hirr := P107P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7197968, -356330, 1198709, 586500, 1986400]
  a := ![120, -180, -58, 54, -477]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2029641, -958804, 1198709, 586500, 1986400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N1 B_one_repr
lemma NI107N1 : Nat.card (O ⧸ I107N1) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-1163, -144, 45, 134, 242]] ![![-4, 17, -16, -11, 12]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-235, -58, -9, 18, 40]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-235, -58, -9, 18, 40]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![21, 84, 65, 1, 0], ![31, 97, 55, 0, 1]] where
  M :=![![![-235, -58, -9, 18, 40], ![-618, -155, -27, 44, 112], ![-553, -119, -16, 41, 88], ![-957, -243, -31, 72, 170], ![-799, -191, -32, 63, 139]]]
  hmulB := by decide  
  f := ![![![-4, -1, -2, 1, 2]], ![![-31, 2, 4, -1, 6]], ![![-29, -7, 4, 11, -2]], ![![-42, -3, 5, 6, 4]], ![![-44, -2, 5, 5, 5]]]
  g := ![![![-17, -50, -31, 18, 40], ![-46, -135, -83, 44, 112], ![-38, -111, -69, 41, 88], ![-71, -209, -129, 72, 170], ![-59, -174, -108, 63, 139]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [45, 9, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 21, 41], [11, 87, 68], [0, 1]]
 g := ![![[83, 96, 15], [95, 49], [41, 93, 5], [82, 36, 29], [51, 106], [1]], ![[6, 75, 35, 50], [2, 100], [95, 103, 36, 57], [94, 70, 88, 85], [16, 75], [67, 79, 15, 33]], ![[70, 49, 53, 76], [72, 9], [2, 91, 80, 13], [48, 94, 11, 86], [107, 81], [21, 82, 65, 76]]]
 h' := ![![[80, 21, 41], [40, 3, 61], [8, 62, 7], [16, 19, 88], [57, 50, 47], [64, 100, 91], [0, 1]], ![[11, 87, 68], [20, 76, 89], [1, 8, 99], [87, 30, 42], [106, 54, 35], [64, 102, 27], [80, 21, 41]], ![[0, 1], [33, 30, 68], [60, 39, 3], [44, 60, 88], [83, 5, 27], [59, 16, 100], [11, 87, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 52], []]
 b := ![[], [21, 43, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [45, 9, 18, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20139347, 4005144, -2066996, -2423360, -6099058]
  a := ![11, -15, -5, 6, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2386245, 7331890, 4503666, -2423360, -6099058]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, -4, -1, 2, -2]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![17, -4, -1, 2, -2]] 
 ![![109, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![65, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![17, -4, -1, 2, -2], ![28, 9, -11, -8, 6], ![-55, 19, 26, 3, -16], ![91, -31, 3, 10, -10], ![55, -1, -18, -1, 3]]]
  hmulB := by decide  
  f := ![![![36668, 3905, -1794, -4447, -7756]], ![![6827, 727, -334, -828, -1444]], ![![23137, 2464, -1132, -2806, -4894]], ![![11139, 1186, -545, -1351, -2356]], ![![22584, 2405, -1105, -2739, -4777]]]
  g := ![![![2, -4, -1, 2, -2], ![4, 9, -11, -8, 6], ![-11, 19, 26, 3, -16], ![7, -31, 3, 10, -10], ![10, -1, -18, -1, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, -22, -4, 8, -2]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![39, -22, -4, 8, -2]] 
 ![![109, 0, 0, 0, 0], ![71, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![80, 0, 0, 1, 0], ![108, 0, 0, 0, 1]] where
  M :=![![![39, -22, -4, 8, -2], ![22, 19, -44, -20, 30], ![-226, 46, 93, 6, -40], ![184, -124, 6, 53, -28], ![142, -34, -66, -4, 31]]]
  hmulB := by decide  
  f := ![![![-1253, -278, 96, 104, 406]], ![![-873, -183, 64, 76, 272]], ![![-722, -166, 57, 58, 240]], ![![-1060, -208, 74, 97, 316]], ![![-1338, -294, 102, 112, 431]]]
  g := ![![![13, -22, -4, 8, -2], ![-3, 19, -44, -20, 30], ![-48, 46, 93, 6, -40], ![68, -124, 6, 53, -28], ![32, -34, -66, -4, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-235, -58, -9, 18, 40]] ![![17, -4, -1, 2, -2]]
  ![![-1286, -351, -27, 107, 206]] where
 M := ![![![-1286, -351, -27, 107, 206]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-1286, -351, -27, 107, 206]] ![![39, -22, -4, 8, -2]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![-2834, 109, 5123, 1417, -3488]]]
 hmul := by decide  
 g := ![![![![-26, 1, 47, 13, -32]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-371, 172, 69, -52, -4]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-371, 172, 69, -52, -4]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![8, 70, 11, 13, 1]] where
  M :=![![![-371, 172, 69, -52, -4], ![112, -263, 267, 182, -212], ![1443, -171, -742, -127, 364], ![-1945, 1033, 193, -378, 110], ![-925, 127, 522, 93, -271]]]
  hmulB := by decide  
  f := ![![![-34, -1, 2, 5, 6]], ![![-95, -12, 8, 11, 26]], ![![-153, -3, 6, 23, 22]], ![![-253, -35, 19, 28, 68]], ![![-108, -12, 8, 13, 27]]]
  g := ![![![-3, 4, 1, 0, -4], ![16, 129, 23, 26, -212], ![-13, -227, -42, -43, 364], ![-25, -59, -9, -16, 110], ![11, 169, 31, 32, -271]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 4 2 6 [56, 15, 106, 13, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 86, 97, 13], [95, 84, 37, 73], [89, 55, 92, 27], [0, 1]]
 g := ![![[58, 54, 89, 18], [77, 81, 11], [66, 69, 44], [58, 38, 2], [92, 63, 100, 1], []], ![[7, 38, 96, 92, 20, 87], [69, 69, 16], [73, 109, 85], [56, 2, 53], [35, 50, 76, 112, 15, 99], [32, 41, 44, 37, 52, 50]], ![[40, 70, 97, 46, 26, 55], [61, 83, 77], [18, 4, 60], [54, 84, 85], [5, 85, 53, 57, 99, 17], [39, 60, 108, 7, 58, 71]], ![[107, 110, 109, 57, 84, 35], [96, 85, 9], [25, 18, 63], [36, 72, 69], [16, 33, 41, 0, 6, 27], [10, 8, 101, 105, 17, 21]]]
 h' := ![![[29, 86, 97, 13], [108, 73, 45, 40], [37, 84, 80, 24], [111, 65, 51, 65], [46, 64, 88, 62], [0, 0, 0, 1], [0, 1]], ![[95, 84, 37, 73], [3, 29, 51, 87], [108, 27, 36, 109], [44, 59, 29, 56], [109, 29, 30, 36], [110, 67, 86, 108], [29, 86, 97, 13]], ![[89, 55, 92, 27], [69, 19, 11, 43], [35, 41, 1, 90], [34, 76, 25, 88], [81, 8, 59, 57], [7, 72, 34, 5], [95, 84, 37, 73]], ![[0, 1], [50, 105, 6, 56], [51, 74, 109, 3], [78, 26, 8, 17], [88, 12, 49, 71], [80, 87, 106, 112], [89, 55, 92, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [72, 59, 34], []]
 b := ![[], [], [67, 44, 3, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 4
  hpos := by decide
  P := [56, 15, 106, 13, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4299198608152, -827984991125, 294297210161, 425084720343, 1371027364807]
  a := ![-52, 75, 27, -35, 209]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-135109889616, -856636287855, -130858440732, -153967000196, 1371027364807]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 163047361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![34, 1, -2, -5, -6]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![34, 1, -2, -5, -6]] 
 ![![113, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![91, 0, 1, 0, 0], ![84, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![34, 1, -2, -5, -6], ![95, 12, -8, -11, -26], ![153, 3, -6, -23, -22], ![253, 35, -19, -28, -68], ![310, 20, -15, -42, -57]]]
  hmulB := by decide  
  f := ![![![371, -172, -69, 52, 4]], ![![196, -89, -39, 26, 4]], ![![286, -137, -49, 43, 0]], ![![293, -137, -53, 42, 2]], ![![64, -27, -15, 7, 3]]]
  g := ![![![6, 1, -2, -5, -6], ![13, 12, -8, -11, -26], ![25, 3, -6, -23, -22], ![30, 35, -19, -28, -68], ![44, 20, -15, -42, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-371, 172, 69, -52, -4]] ![![34, 1, -2, -5, -6]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![912, 251, 37, -57, -174]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![912, 251, 37, -57, -174]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![52, 122, 1, 0, 0], ![32, 123, 0, 1, 0], ![80, 28, 0, 0, 1]] where
  M :=![![![912, 251, 37, -57, -174], ![2667, 584, 117, -217, -402], ![1790, 622, 65, -68, -434], ![4184, 832, 188, -369, -570], ![2837, 859, 111, -151, -597]]]
  hmulB := by decide  
  f := ![![![-292, -3, 57, 29, 18]], ![![-299, -212, -27, 121, 134]], ![![-414, -204, -3, 128, 138]], ![![-381, -206, -9, 126, 136]], ![![-261, -51, 31, 47, 43]]]
  g := ![![![116, 60, 37, -57, -174], ![281, 191, 117, -217, -402], ![278, 104, 65, -68, -434], ![408, 309, 188, -369, -570], ![391, 178, 111, -151, -597]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [1, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 126], [0, 1]]
 g := ![![[43, 1], [84, 16], [33, 76], [27, 100], [44, 74], [84, 1]], ![[0, 126], [31, 111], [67, 51], [45, 27], [37, 53], [41, 126]]]
 h' := ![![[84, 126], [43, 1], [94, 123], [100, 40], [83, 10], [43, 70], [0, 1]], ![[0, 1], [0, 126], [12, 4], [31, 87], [34, 117], [81, 57], [84, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [24, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [1, 43, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-49206, -12707, 16875, 791, 18856]
  a := ![14, -17, -7, 18, -57]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19374, -21234, 16875, 791, 18856]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 10, 4, 0, -2]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![21, 10, 4, 0, -2]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![85, 91, 1, 0, 0], ![118, 44, 0, 1, 0], ![96, 50, 0, 0, 1]] where
  M :=![![![21, 10, 4, 0, -2], ![30, 25, 12, 4, -2], ![-2, 14, 11, 6, 8], ![-64, 28, 22, 19, 20], ![-98, 14, 22, 20, 29]]]
  hmulB := by decide  
  f := ![![![-29, 6, 16, 0, -6]], ![![90, -41, -16, 20, -6]], ![![45, -25, -1, 14, -8]], ![![2, -8, 10, 7, -8]], ![![14, -12, 6, 8, -7]]]
  g := ![![![-1, -2, 4, 0, -2], ![-10, -9, 12, 4, -2], ![-19, -13, 11, 6, 8], ![-48, -30, 22, 19, 20], ![-56, -34, 22, 20, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [110, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 126], [0, 1]]
 g := ![![[57, 41], [35, 49], [92, 32], [63, 19], [86, 44], [80, 1]], ![[35, 86], [18, 78], [112, 95], [59, 108], [50, 83], [33, 126]]]
 h' := ![![[80, 126], [87, 26], [40, 7], [55, 63], [65, 107], [90, 67], [0, 1]], ![[0, 1], [8, 101], [92, 120], [15, 64], [116, 20], [116, 60], [80, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [104, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [110, 47, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-47624, -1136, 3394, 6222, 11576]
  a := ![6, -12, -2, -14, -24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17178, -9154, 3394, 6222, 11576]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, 1, 1, 1, 2]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![-8, 1, 1, 1, 2]] 
 ![![127, 0, 0, 0, 0], ![84, 1, 0, 0, 0], ![113, 0, 1, 0, 0], ![73, 0, 0, 1, 0], ![115, 0, 0, 0, 1]] where
  M :=![![![-8, 1, 1, 1, 2], ![-31, 0, 5, 5, 6], ![-32, -4, 1, 6, 10], ![-94, -2, 6, 11, 22], ![-103, -5, 9, 13, 21]]]
  hmulB := by decide  
  f := ![![![-428, 151, -27, 115, -110]], ![![-271, 96, -17, 73, -70]], ![![-406, 143, -26, 109, -104]], ![![-216, 77, -13, 58, -56]], ![![-409, 144, -26, 110, -105]]]
  g := ![![![-4, 1, 1, 1, 2], ![-13, 0, 5, 5, 6], ![-11, -4, 1, 6, 10], ![-31, -2, 6, 11, 22], ![-32, -5, 9, 13, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![912, 251, 37, -57, -174]] ![![21, 10, 4, 0, -2]]
  ![![47308, 11881, 1985, -3337, -8216]] where
 M := ![![![47308, 11881, 1985, -3337, -8216]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![47308, 11881, 1985, -3337, -8216]] ![![-8, 1, 1, 1, 2]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![349631, 87122, 14732, -24892, -60198]]]
 hmul := by decide  
 g := ![![![![2753, 686, 116, -196, -474]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![619, -188, -193, 26, 64]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![619, -188, -193, 26, 64]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![126, 20, 124, 1, 0], ![112, 79, 51, 0, 1]] where
  M :=![![![619, -188, -193, 26, 64], ![-986, 649, -55, -284, 168], ![-625, -383, 872, 397, -568], ![3749, -1349, -951, 304, 226], ![415, 299, -596, -285, 391]]]
  hmulB := by decide  
  f := ![![![338, -121, 30, -93, 94]], ![![-1317, 406, -84, 341, -278]], ![![2573, -905, 212, -703, 682]], ![![2533, -903, 215, -696, 688]], ![![512, -217, 59, -152, 183]]]
  g := ![![![-75, -44, -51, 26, 64], ![122, -53, 203, -284, 168], ![99, 279, -148, 397, -568], ![-457, -193, -383, 304, 226], ![-57, -190, 113, -285, 391]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [7, 42, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 2, 113], [103, 128, 18], [0, 1]]
 g := ![![[111, 106, 55], [47, 56, 108], [84, 114], [16, 49], [16, 105], [112, 1], []], ![[15, 111, 76, 100], [84, 21, 1, 74], [108, 48], [61, 108], [89, 1], [45, 9], [60, 62]], ![[66, 124, 62, 92], [69, 33, 90, 73], [57, 112], [6, 109], [44, 89], [68, 4], [24, 62]]]
 h' := ![![[9, 2, 113], [64, 5, 102], [119, 31, 34], [24, 28, 101], [23, 54, 124], [2, 5, 57], [0, 0, 1], [0, 1]], ![[103, 128, 18], [115, 6, 128], [7, 17, 126], [97, 88, 110], [0, 98, 97], [112, 54, 1], [54, 95, 128], [9, 2, 113]], ![[0, 1], [7, 120, 32], [21, 83, 102], [17, 15, 51], [94, 110, 41], [128, 72, 73], [92, 36, 2], [103, 128, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128, 104], []]
 b := ![[], [17, 4, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [7, 42, 19, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2692359, -218532, 238879, 353026, 666894]
  a := ![0, 10, 7, 1, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-930273, -457738, -591969, 353026, 666894]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-338, 121, -30, 93, -94]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-338, 121, -30, 93, -94]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![112, 73, 1, 0, 0], ![2, 40, 0, 1, 0], ![20, 100, 0, 0, 1]] where
  M :=![![![-338, 121, -30, 93, -94], ![1317, -406, 84, -341, 278], ![-2573, 905, -212, 703, -682], ![3477, -1053, 223, -894, 724], ![-2036, 794, -193, 582, -625]]]
  hmulB := by decide  
  f := ![![![-619, 188, 193, -26, -64]], ![![986, -649, 55, 284, -168]], ![![25, -198, 189, 133, -144]], ![![263, -185, 27, 84, -54]], ![![655, -469, 76, 215, -141]]]
  g := ![![![36, 61, -30, 93, -94], ![-99, -158, 84, -341, 278], ![255, 431, -212, 703, -682], ![-261, -412, 223, -894, 724], ![236, 413, -193, 582, -625]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [60, 91, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 130], [0, 1]]
 g := ![![[43, 107], [66, 52], [84], [129], [13], [28], [1]], ![[0, 24], [50, 79], [84], [129], [13], [28], [1]]]
 h' := ![![[40, 130], [101, 99], [29, 24], [22, 79], [66, 28], [86, 119], [71, 40], [0, 1]], ![[0, 1], [0, 32], [72, 107], [38, 52], [7, 103], [130, 12], [99, 91], [40, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [27, 110]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [60, 91, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5287, -407, 408, 443, 544]
  a := ![2, -5, -1, -3, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-479, -781, 408, 443, 544]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![619, -188, -193, 26, 64]] ![![-338, 121, -30, 93, -94]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![-131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1595, -532, 123, -428, 392]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![1595, -532, 123, -428, 392]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![17, 28, 44, 73, 1]] where
  M :=![![![1595, -532, 123, -428, 392], ![-5452, 1811, -403, 1458, -1320], ![11897, -3977, 894, -3181, 2916], ![-14331, 4755, -1061, 3810, -3446], ![10149, -3423, 786, -2725, 2515]]]
  hmulB := by decide  
  f := ![![![6, 5, 2, -1, -2]], ![![31, 4, 4, 1, -6]], ![![29, 7, -6, -3, 2]], ![![1, 23, 9, -4, -4]], ![![17, 16, 4, -3, -3]]]
  g := ![![![-37, -84, -125, -212, 392], ![124, 283, 421, 714, -1320], ![-275, -625, -930, -1577, 2916], ![323, 739, 1099, 1864, -3446], ![-238, -539, -802, -1360, 2515]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 4 2 7 [109, 84, 125, 105, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 40, 25, 27], [119, 50, 6, 100], [38, 46, 106, 10], [0, 1]]
 g := ![![[20, 22, 58, 77], [111, 88, 107], [10, 53, 60], [59, 57, 2, 107], [100, 108, 65], [1], []], ![[59, 135, 102, 4, 124, 95], [75, 65, 81], [119, 102, 98], [39, 106, 133, 32, 39, 102], [23, 122, 115], [48, 29, 120], [53, 18, 44]], ![[70, 86, 84, 21, 76, 17], [131, 82, 59], [124, 60, 115], [50, 119, 121, 130, 75, 61], [96, 13, 130], [55, 45, 22], [135, 72, 136]], ![[88, 79, 16, 79, 98, 67], [88, 118, 73], [104, 41, 128], [4, 133, 10, 77, 118, 104], [0, 91, 109], [121, 73, 87], [16, 114, 100]]]
 h' := ![![[12, 40, 25, 27], [62, 52, 56, 25], [70, 112, 101, 92], [8, 1, 35, 34], [22, 58, 32, 45], [28, 53, 12, 32], [0, 0, 1], [0, 1]], ![[119, 50, 6, 100], [89, 63, 28, 70], [27, 41, 126, 9], [42, 123, 120, 57], [114, 79, 65, 29], [93, 58, 118, 72], [121, 26, 90, 42], [12, 40, 25, 27]], ![[38, 46, 106, 10], [56, 127, 94, 9], [19, 27, 4, 14], [66, 1, 70, 72], [51, 87, 114, 105], [69, 115, 40, 104], [131, 110, 20, 76], [119, 50, 6, 100]], ![[0, 1], [85, 32, 96, 33], [19, 94, 43, 22], [126, 12, 49, 111], [61, 50, 63, 95], [91, 48, 104, 66], [111, 1, 26, 19], [38, 46, 106, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [131, 4, 118], []]
 b := ![[], [], [93, 120, 75, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 4
  hpos := by decide
  P := [109, 84, 125, 105, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-967284885, -13071552320, 3477671133, -4508409690, 14833698277]
  a := ![-16, 22, 13, -24, 67]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1847738362, -3127117548, -4738723015, -7936995503, 14833698277]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 352275361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, -5, -2, 1, 2]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-6, -5, -2, 1, 2]] 
 ![![137, 0, 0, 0, 0], ![118, 1, 0, 0, 0], ![103, 0, 1, 0, 0], ![71, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-6, -5, -2, 1, 2], ![-31, -4, -4, -1, 6], ![-29, -7, 6, 3, -2], ![-1, -23, -9, 4, 4], ![-10, -8, -9, -2, 5]]]
  hmulB := by decide  
  f := ![![![-1595, 532, -123, 428, -392]], ![![-1334, 445, -103, 358, -328]], ![![-1286, 429, -99, 345, -316]], ![![-722, 241, -56, 194, -178]], ![![-272, 91, -21, 73, -67]]]
  g := ![![![5, -5, -2, 1, 2], ![6, -4, -4, -1, 6], ![0, -7, 6, 3, -2], ![24, -23, -9, 4, 4], ![14, -8, -9, -2, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![1595, -532, 123, -428, 392]] ![![-6, -5, -2, 1, 2]]
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


def P139P0 : CertificateIrreducibleZModOfList' 139 5 2 7 [12, 36, 99, 55, 40, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [125, 105, 84, 38, 128], [132, 14, 53, 113, 129], [54, 116, 137, 51, 68], [66, 42, 4, 76, 92], [0, 1]]
 g := ![![[117, 35, 10, 69, 69], [13, 132, 23, 42, 79], [133, 37, 89, 91], [69, 57, 61, 16, 55], [71, 16, 99, 1], [], []], ![[117, 111, 97, 126, 34, 134, 64, 74], [66, 84, 8, 131, 49, 54, 10, 114], [75, 113, 45, 57], [45, 55, 63, 10, 36, 133, 70, 27], [36, 73, 111, 63], [5, 38, 87, 100], [20, 83, 23, 121]], ![[95, 11, 50, 74, 89, 101, 126, 30], [9, 9, 81, 14, 24, 62, 130, 124], [110, 122, 37, 35], [37, 34, 59, 12, 116, 64, 16, 30], [75, 99, 77, 4], [90, 135, 78, 69], [83, 15, 134, 100]], ![[96, 78, 108, 65, 92, 10, 17, 19], [130, 70, 19, 48, 10, 73, 101, 115], [26, 94, 95, 89], [57, 125, 114, 107, 108, 30, 30, 50], [18, 79, 22, 35], [19, 59, 75, 100], [14, 6, 35, 37]], ![[60, 9, 110, 35, 62, 104, 56, 10], [115, 134, 134, 120, 136, 62, 23, 33], [5, 23, 40, 137], [1, 83, 62, 115, 11, 36, 48, 19], [114, 32, 87, 83], [33, 66, 18, 25], [3, 132, 128, 124]]]
 h' := ![![[125, 105, 84, 38, 128], [122, 21, 115, 26, 25], [108, 116, 132, 54, 94], [6, 75, 75, 85, 62], [121, 32, 103, 109, 65], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[132, 14, 53, 113, 129], [25, 115, 66, 42, 61], [93, 93, 107, 71, 33], [115, 96, 136, 51, 125], [20, 37, 4, 14, 15], [69, 15, 64, 40, 52], [95, 70, 93, 114, 10], [125, 105, 84, 38, 128]], ![[54, 116, 137, 51, 68], [58, 111, 49, 39, 54], [135, 33, 6, 65, 40], [75, 117, 72, 92, 69], [103, 86, 113, 60, 85], [13, 78, 4, 45, 137], [26, 111, 70, 60, 114], [132, 14, 53, 113, 129]], ![[66, 42, 4, 76, 92], [90, 53, 31, 90, 91], [18, 90, 28, 11, 135], [82, 25, 71, 106, 111], [116, 87, 2, 42, 41], [101, 126, 86, 107, 69], [107, 137, 98, 30, 10], [54, 116, 137, 51, 68]], ![[0, 1], [23, 117, 17, 81, 47], [6, 85, 5, 77, 115], [30, 104, 63, 83, 50], [31, 36, 56, 53, 72], [3, 59, 124, 86, 19], [11, 99, 16, 74, 5], [66, 42, 4, 76, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 41, 78, 77], [], [], []]
 b := ![[], [109, 70, 109, 8, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 5
  hpos := by decide
  P := [12, 36, 99, 55, 40, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-880666464301, -414678931574, 152631519137, -18631436012, 541367592459]
  a := ![-10, 13, 5, -11, 41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6335729959, -2983301666, 1098068483, -134039108, 3894730881]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![926, 89, -43, -115, -186]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![926, 89, -43, -115, -186]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![52, 41, 120, 1, 0], ![59, 144, 47, 0, 1]] where
  M :=![![![926, 89, -43, -115, -186], ![2905, 342, -151, -343, -646], ![3564, 312, -153, -454, -686], ![7154, 838, -374, -839, -1594], ![7481, 739, -351, -927, -1521]]]
  hmulB := by decide  
  f := ![![![142, 25, 3, -7, -22]], ![![337, 94, 3, -31, -50]], ![![222, 78, 41, -16, -62]], ![![325, 98, 35, -24, -72]], ![![455, 126, 17, -38, -77]]]
  g := ![![![120, 212, 151, -115, -186], ![395, 721, 479, -343, -646], ![454, 790, 581, -454, -686], ![972, 1777, 1176, -839, -1594], ![976, 1730, 1224, -927, -1521]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [23, 111, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 129, 70], [16, 19, 79], [0, 1]]
 g := ![![[139, 17, 82], [81, 142], [119, 41, 120], [101, 140], [29, 103, 24], [97, 1], []], ![[108, 106, 103, 11], [2, 100], [86, 93, 94, 136], [101, 19], [118, 78, 147, 38], [140, 63], [21, 132]], ![[2, 70, 0, 141], [1, 132], [66, 25, 36, 8], [48, 53], [138, 22, 60, 23], [119, 102], [12, 132]]]
 h' := ![![[81, 129, 70], [119, 111, 126], [94, 107, 69], [36, 56, 92], [78, 90, 17], [4, 87, 60], [0, 0, 1], [0, 1]], ![[16, 19, 79], [138, 104, 32], [66, 126, 10], [81, 14, 6], [136, 136, 67], [125, 62, 78], [118, 35, 19], [81, 129, 70]], ![[0, 1], [120, 83, 140], [128, 65, 70], [135, 79, 51], [135, 72, 65], [47, 0, 11], [129, 114, 129], [16, 19, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 98], []]
 b := ![[], [31, 126, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [23, 111, 52, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2270386, -252211, 237745, 267417, 600924]
  a := ![-3, 7, 3, -1, 16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-346514, -656036, -403327, 267417, 600924]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![142, 25, 3, -7, -22]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![142, 25, 3, -7, -22]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![2, 104, 1, 0, 0], ![91, 17, 0, 1, 0], ![80, 116, 0, 0, 1]] where
  M :=![![![142, 25, 3, -7, -22], ![337, 94, 3, -31, -50], ![222, 78, 41, -16, -62], ![584, 88, 16, -21, -94], ![455, 97, -3, -33, -61]]]
  hmulB := by decide  
  f := ![![![926, 89, -43, -115, -186]], ![![2905, 342, -151, -343, -646]], ![![2064, 242, -107, -244, -458]], ![![945, 99, -46, -115, -198]], ![![2809, 319, -143, -335, -613]]]
  g := ![![![17, 16, 3, -7, -22], ![48, 41, 3, -31, -50], ![44, 22, 41, -16, -62], ![67, 65, 16, -21, -94], ![56, 54, -3, -33, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P1 : CertificateIrreducibleZModOfList' 149 2 2 7 [116, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [147, 148], [0, 1]]
 g := ![![[18, 9], [114], [97, 114], [28], [62, 81], [4], [1]], ![[0, 140], [114], [18, 35], [28], [49, 68], [4], [1]]]
 h' := ![![[147, 148], [6, 3], [72, 73], [140, 73], [109, 112], [29, 9], [33, 147], [0, 1]], ![[0, 1], [0, 146], [75, 76], [143, 76], [34, 37], [11, 140], [37, 2], [147, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [46, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N1 : CertifiedPrimeIdeal' SI149N1 149 where
  n := 2
  hpos := by decide
  P := [116, 2, 1]
  hirr := P149P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1022693, -197414, 287522, 34653, 403777]
  a := ![60, -75, -39, 62, -233]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-248680, -520315, 287522, 34653, 403777]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N1 B_one_repr
lemma NI149N1 : Nat.card (O ⧸ I149N1) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![926, 89, -43, -115, -186]] ![![142, 25, 3, -7, -22]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![149, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 4, 1, -2, -4]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![19, 4, 1, -2, -4]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![46, 92, 1, 0, 0], ![19, 107, 0, 1, 0], ![35, 44, 0, 0, 1]] where
  M :=![![![19, 4, 1, -2, -4], ![62, 9, -1, -4, -12], ![61, 11, -2, -9, -8], ![95, 25, 3, -10, -26], ![113, 13, 0, -11, -21]]]
  hmulB := by decide  
  f := ![![![22, 7, 0, -5, -2]], ![![35, 18, 10, 1, -22]], ![![29, 13, 6, -1, -14]], ![![28, 14, 7, 0, -16]], ![![16, 7, 3, -1, -7]]]
  g := ![![![1, 2, 1, -2, -4], ![4, 7, -1, -4, -12], ![4, 10, -2, -9, -8], ![7, 13, 3, -10, -26], ![7, 14, 0, -11, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [113, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 150], [0, 1]]
 g := ![![[67, 78], [17, 5], [117, 148], [76], [0, 74], [139], [1]], ![[90, 73], [63, 146], [29, 3], [76], [107, 77], [139], [1]]]
 h' := ![![[130, 150], [42, 94], [67, 55], [19, 65], [0, 23], [82, 15], [38, 130], [0, 1]], ![[0, 1], [31, 57], [120, 96], [13, 86], [121, 128], [69, 136], [26, 21], [130, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [98, 110]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [113, 21, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-82374, -16887, 23383, 2907, 31798]
  a := ![17, -21, -11, 18, -67]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15405, -25684, 23383, 2907, 31798]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, -5, 1, 1, -4]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![10, -5, 1, 1, -4]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![63, 72, 1, 0, 0], ![101, 129, 0, 1, 0], ![114, 127, 0, 0, 1]] where
  M :=![![![10, -5, 1, 1, -4], ![59, -6, -19, -7, 0], ![-26, 26, 13, -12, -14], ![98, -14, 12, -1, -38], ![155, -11, -21, -11, -21]]]
  hmulB := by decide  
  f := ![![![-350, 109, -27, 91, -80]], ![![1109, -390, 85, -305, 284]], ![![366, -135, 28, -103, 98]], ![![733, -267, 56, -205, 194]], ![![654, -241, 50, -184, 175]]]
  g := ![![![2, 2, 1, 1, -4], ![13, 15, -19, -7, 0], ![13, 16, 13, -12, -14], ![25, 27, 12, -1, -38], ![33, 37, -21, -11, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [84, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 150], [0, 1]]
 g := ![![[116, 9], [105, 124], [121, 94], [44], [56, 103], [58], [1]], ![[0, 142], [0, 27], [0, 57], [44], [121, 48], [58], [1]]]
 h' := ![![[71, 150], [89, 3], [104, 107], [4, 68], [128, 73], [70, 42], [67, 71], [0, 1]], ![[0, 1], [0, 148], [0, 44], [0, 83], [26, 78], [32, 109], [125, 80], [71, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [47, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [84, 80, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-212024, -11014, 37075, 16078, 67765]
  a := ![-20, 30, 12, -10, 83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-78787, -88481, 37075, 16078, 67765]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![69, -22, 5, -18, 16]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![69, -22, 5, -18, 16]] 
 ![![151, 0, 0, 0, 0], ![127, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![74, 0, 0, 0, 1]] where
  M :=![![![69, -22, 5, -18, 16], ![-222, 77, -17, 60, -56], ![501, -165, 38, -133, 120], ![-583, 199, -45, 158, -146], ![435, -141, 32, -115, 103]]]
  hmulB := by decide  
  f := ![![![416, 21, -16, -25, -70]], ![![357, 19, -14, -22, -60]], ![![77, 5, -2, -5, -14]], ![![81, 4, -3, -5, -14]], ![![220, 12, -9, -14, -37]]]
  g := ![![![13, -22, 5, -18, 16], ![-45, 77, -17, 60, -56], ![97, -165, 38, -133, 120], ![-116, 199, -45, 158, -146], ![83, -141, 32, -115, 103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![19, 4, 1, -2, -4]] ![![10, -5, 1, 1, -4]]
  ![![-416, -21, 16, 25, 70]] where
 M := ![![![-416, -21, 16, 25, 70]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![-416, -21, 16, 25, 70]] ![![69, -22, 5, -18, 16]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB318I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB318I3 : PrimesBelowBoundCertificateInterval O 103 151 318 where
  m := 9
  g := ![2, 3, 2, 3, 2, 2, 1, 2, 3]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB318I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
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
    · exact ![16129, 16129, 127]
    · exact ![2248091, 17161]
    · exact ![352275361, 137]
    · exact ![51888844699]
    · exact ![3307949, 22201]
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
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
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
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
  β := ![I109N1, I109N2, I113N1, I127N2, I137N1, I151N2]
  Il := ![[], [I109N1, I109N2], [I113N1], [I127N2], [], [I137N1], [], [], [I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
