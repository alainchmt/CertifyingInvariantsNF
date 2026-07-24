
import IdealArithmetic.Examples.NF5_3_364500000_2.RI5_3_364500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1541, 13, -428, -2, 148]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![1541, 13, -428, -2, 148]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![51, 49, 102, 1, 0], ![74, 81, 65, 0, 1]] where
  M :=![![![1541, 13, -428, -2, 148], ![-3552, -519, 622, 328, -8], ![96, -1093, -863, 590, 656], ![-6096, -3142, -682, 1597, 1184], ![-5280, -4439, -1928, 2158, 1929]]]
  hmulB := by decide  
  f := ![![![-977, -485, 430, 226, -212]], ![![5088, 2237, -2270, -836, 904]], ![![-10848, -4399, 4881, 1346, -1672]], ![![-8313, -3340, 3744, 995, -1260]], ![![-3614, -1387, 1635, 356, -503]]]
  g := ![![![-87, -111, -92, -2, 148], ![-184, -149, -302, 328, -8], ![-734, -777, -969, 590, 656], ![-1637, -1657, -2248, 1597, 1184], ![-2412, -2490, -3247, 2158, 1929]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [45, 61, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 81, 68], [34, 25, 39], [0, 1]]
 g := ![![[29, 7, 36], [12, 64, 81], [46, 75], [46, 64, 92], [76, 62], [1]], ![[55, 75, 46, 2], [97, 80, 21, 18], [53, 52], [92, 84, 88, 60], [54, 92], [73, 100, 27, 66]], ![[93, 103, 69, 29], [77, 28, 88, 12], [18, 90], [7, 85, 52, 100], [93, 52], [30, 32, 11, 41]]]
 h' := ![![[86, 81, 68], [102, 83, 101], [48, 58, 9], [70, 1, 17], [103, 97, 78], [62, 46, 13], [0, 1]], ![[34, 25, 39], [86, 30, 37], [38, 25, 103], [60, 52, 65], [11, 64, 93], [80, 91, 29], [86, 81, 68]], ![[0, 1], [59, 101, 76], [58, 24, 102], [36, 54, 25], [93, 53, 43], [76, 77, 65], [34, 25, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 82], []]
 b := ![[], [102, 93, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [45, 61, 94, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9897321, 5711138, 1506958, -2607228, -2007556]
  a := ![0, -7, 2, -4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2723599, 2767078, 3719022, -2607228, -2007556]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3853, 178, -964, -116, 260]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![3853, 178, -964, -116, 260]] 
 ![![107, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![91, 0, 0, 0, 1]] where
  M :=![![![3853, 178, -964, -116, 260], ![-6240, -203, 1628, 152, -464], ![5568, 398, -1283, -228, 304], ![-528, 344, 420, -143, -224], ![7248, 818, -1436, -428, 241]]]
  hmulB := by decide  
  f := ![![![-2665, -198, 1300, -708, 196]], ![![-567, -85, 272, -100, 12]], ![![-853, 84, 433, -400, 164]], ![![-1685, -462, 784, -51, -108]], ![![-1097, 344, 584, -792, 373]]]
  g := ![![![237, 178, -964, -116, 260], ![-383, -203, 1628, 152, -464], ![345, 398, -1283, -228, 304], ![-25, 344, 420, -143, -224], ![457, 818, -1436, -428, 241]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3749, -2622, -974, 1181, 1008]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![-3749, -2622, -974, 1181, 1008]] 
 ![![107, 0, 0, 0, 0], ![96, 1, 0, 0, 0], ![100, 0, 1, 0, 0], ![74, 0, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![-3749, -2622, -974, 1181, 1008], ![-24192, -13449, -3574, 6116, 4724], ![-56688, -33749, -10117, 15322, 12232], ![-134688, -78632, -22820, 35753, 28282], ![-185940, -109426, -32182, 49757, 39507]]]
  hmulB := by decide  
  f := ![![![-204151, -96372, 90370, 41357, -40854]], ![![-174000, -82555, 76978, 35740, -35108]], ![![-209348, -97405, 92825, 40734, -40912]], ![![-113002, -56596, 49668, 26729, -24862]], ![![-120069, -52580, 53596, 19486, -21193]]]
  g := ![![![1987, -2622, -974, 1181, 1008], ![8964, -13449, -3574, 6116, 4724], ![23464, -33749, -10117, 15322, 12232], ![53996, -78632, -22820, 35753, 28282], ![75489, -109426, -32182, 49757, 39507]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![1541, 13, -428, -2, 148]] ![![3853, 178, -964, -116, 260]]
  ![![4547009, 221691, -1128604, -142254, 300632]] where
 M := ![![![4547009, 221691, -1128604, -142254, 300632]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![4547009, 221691, -1128604, -142254, 300632]] ![![-3749, -2622, -974, 1181, 1008]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![4828810811, 1474235835, -231726476, -694051541, -320589976]]]
 hmul := by decide  
 g := ![![![![45129073, 13777905, -2165668, -6486463, -2996168]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6899, 5418, 2504, -848, -990]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![6899, 5418, 2504, -848, -990]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![66, 55, 59, 1, 0], ![15, 17, 85, 0, 1]] where
  M :=![![![6899, 5418, 2504, -848, -990], ![23760, 18597, 8572, -2912, -3392], ![40704, 31910, 14725, -4996, -5824], ![58008, 45452, 20972, -7115, -8296], ![58248, 45658, 21064, -7148, -8331]]]
  hmulB := by decide  
  f := ![![![-49, -18, 16, 8, -6]], ![![144, 49, -76, -16, 32]], ![![-384, -158, 129, 52, -32]], ![![-162, -71, 39, 25, -4]], ![![-291, -121, 93, 40, -21]]]
  g := ![![![713, 632, 1254, -848, -990], ![2448, 2169, 4300, -2912, -3392], ![4200, 3722, 7381, -4996, -5824], ![5982, 5301, 10513, -7115, -8296], ![6009, 5325, 10559, -7148, -8331]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [107, 75, 88, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 22, 94], [21, 86, 15], [0, 1]]
 g := ![![[0, 97, 1], [62, 66], [37, 48, 83], [82, 62, 89], [7, 5], [1]], ![[65, 70, 67, 102], [55, 93], [35, 59, 24, 87], [91, 53, 22, 27], [61, 35], [19, 68, 1, 4]], ![[56, 88, 64, 108], [78, 88], [62, 23, 66, 7], [2, 88, 90, 71], [39, 81], [73, 104, 87, 105]]]
 h' := ![![[0, 22, 94], [41, 38, 1], [74, 19, 34], [55, 75, 65], [18, 57, 31], [2, 34, 21], [0, 1]], ![[21, 86, 15], [105, 85, 61], [70, 63, 23], [73, 32, 105], [40, 100, 67], [38, 19, 97], [0, 22, 94]], ![[0, 1], [85, 95, 47], [16, 27, 52], [35, 2, 48], [77, 61, 11], [33, 56, 100], [21, 86, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 12], []]
 b := ![[], [73, 1, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [107, 75, 88, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1231271387, 590222281, -142533872, -248409461, -78277268]
  a := ![3, -62, -1, -65, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![172481237, 142967488, 194194423, -248409461, -78277268]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49, 18, -16, -8, 6]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![49, 18, -16, -8, 6]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![80, 50, 1, 0, 0], ![33, 102, 0, 1, 0], ![102, 18, 0, 0, 1]] where
  M :=![![![49, 18, -16, -8, 6], ![-144, -49, 76, 16, -32], ![384, 158, -129, -52, 32], ![-312, -76, 236, -9, -88], ![792, 322, -224, -92, 23]]]
  hmulB := by decide  
  f := ![![![-6899, -5418, -2504, 848, 990]], ![![-23760, -18597, -8572, 2912, 3392]], ![![-16336, -12800, -5905, 2004, 2336]], ![![-24855, -19460, -8972, 3047, 3550]], ![![-10914, -8560, -3952, 1340, 1563]]]
  g := ![![![9, 14, -16, -8, 6], ![-32, -45, 76, 16, -32], ![84, 104, -129, -52, 32], ![-91, -86, 236, -9, -88], ![178, 188, -224, -92, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [85, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 108], [0, 1]]
 g := ![![[84, 48], [83], [62, 83], [65, 60], [9], [54, 1]], ![[60, 61], [83], [75, 26], [35, 49], [9], [108, 108]]]
 h' := ![![[54, 108], [57, 87], [71, 65], [34, 44], [33, 13], [97, 106], [0, 1]], ![[0, 1], [68, 22], [93, 44], [12, 65], [81, 96], [44, 3], [54, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [15, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where
  n := 2
  hpos := by decide
  P := [85, 55, 1]
  hirr := P109P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8307, -4760, -776, 2209, 1642]
  a := ![1, -6, 1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1712, -2026, -776, 2209, 1642]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![6899, 5418, 2504, -848, -990]] ![![49, 18, -16, -8, 6]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![-109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0, 0, 0]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]] where
  M :=![![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 5 2 6 [73, 97, 1, 56, 8, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 92, 42, 1, 52], [11, 15, 98, 34, 84], [71, 89, 18, 27, 103], [6, 29, 68, 51, 100], [0, 1]]
 g := ![![[88, 36, 54, 35, 36], [40, 84, 31, 112], [15, 52, 75, 111], [87, 90, 84, 15], [8, 105, 1], []], ![[86, 64, 48, 89, 33, 62, 111, 69], [101, 104, 68, 50], [40, 76, 71, 41], [109, 2, 63, 50], [86, 60, 39, 72, 102, 84, 99, 83], [6, 101, 51, 48, 8, 80, 27, 36]], ![[92, 19, 0, 53, 105, 11, 31, 86], [69, 17, 53, 102], [98, 97, 88, 41], [71, 56, 8, 85], [54, 5, 57, 35, 53, 56, 97, 59], [28, 21, 22, 32, 106, 40, 89, 19]], ![[83, 110, 69, 101, 53, 47, 3, 94], [68, 102, 76, 32], [92, 111, 68, 102], [3, 91, 55, 111], [49, 39, 97, 42, 30, 6, 45, 6], [56, 74, 18, 92, 57, 0, 54, 17]], ![[1, 71, 22, 62, 35, 66, 25, 62], [13, 13, 39, 50], [48, 11, 88, 62], [34, 84, 100, 82], [66, 83, 24, 13, 99, 3, 28, 97], [14, 20, 64, 17, 4, 32, 41, 63]]]
 h' := ![![[17, 92, 42, 1, 52], [71, 66, 91, 39, 107], [36, 5, 88, 110, 15], [112, 84, 25, 12, 26], [94, 34, 17, 28, 44], [0, 0, 0, 1], [0, 1]], ![[11, 15, 98, 34, 84], [89, 12, 1, 75, 88], [2, 28, 33, 27, 84], [53, 102, 102, 48, 43], [10, 106, 50, 68, 84], [68, 54, 66, 104, 67], [17, 92, 42, 1, 52]], ![[71, 89, 18, 27, 103], [74, 47, 83, 31, 6], [79, 97, 50, 18, 21], [1, 93, 50, 74, 70], [41, 33, 34, 10, 57], [78, 66, 4, 6, 33], [11, 15, 98, 34, 84]], ![[6, 29, 68, 51, 100], [39, 69, 80, 18, 9], [12, 103, 71, 100, 22], [20, 61, 19, 91, 21], [76, 20, 82, 84, 87], [20, 18, 7, 26, 19], [71, 89, 18, 27, 103]], ![[0, 1], [12, 32, 84, 63, 16], [82, 106, 97, 84, 84], [99, 112, 30, 1, 66], [35, 33, 43, 36, 67], [98, 88, 36, 89, 107], [6, 29, 68, 51, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 14, 82, 10], [], [], []]
 b := ![[], [7, 82, 103, 63, 65], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 5
  hpos := by decide
  P := [73, 97, 1, 56, 8, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-202873108285432, -118357558456168, -34248074417879, 54139747545820, 42790757098115]
  a := ![1, 25, -3, 18, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1795337241464, -1047412021736, -303080304583, 479112810140, 378679266355]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1439, 834, 240, -380, -300]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![1439, 834, 240, -380, -300]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![2, 121, 34, 1, 0], ![93, 48, 117, 0, 1]] where
  M :=![![![1439, 834, 240, -380, -300], ![7200, 4219, 1228, -1920, -1520], ![18240, 10654, 3099, -4852, -3840], ![42480, 24828, 7212, -11301, -8944], ![59184, 34586, 10056, -15748, -12461]]]
  hmulB := by decide  
  f := ![![![-31, -30, -8, 4, 4]], ![![-96, -75, -52, 16, 16]], ![![-192, -146, -59, 12, 32]], ![![-146, -113, -66, 19, 24]], ![![-237, -186, -81, 20, 39]]]
  g := ![![![237, 482, 380, -380, -300], ![1200, 2437, 1924, -1920, -1520], ![3032, 6158, 4861, -4852, -3840], ![7062, 14343, 11322, -11301, -8944], ![9839, 19986, 15775, -15748, -12461]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [13, 27, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 75, 46], [52, 51, 81], [0, 1]]
 g := ![![[48, 34, 94], [99, 120, 38], [14, 70, 81], [2, 105, 60], [63, 11, 32], [1]], ![[15, 29, 10, 83], [79, 109, 122, 39], [83, 61, 79, 102], [92, 14, 3, 56], [8, 52, 122, 97], [126, 95, 77, 54]], ![[124, 29, 108, 115], [123, 44, 39, 11], [102, 32, 2, 30], [39, 125, 75, 107], [77, 109, 67, 70], [61, 22, 52, 73]]]
 h' := ![![[11, 75, 46], [110, 62, 100], [72, 23, 61], [101, 52, 9], [70, 103, 21], [114, 100, 63], [0, 1]], ![[52, 51, 81], [65, 125, 78], [86, 76, 105], [111, 32, 57], [61, 12, 94], [74, 109, 66], [11, 75, 46]], ![[0, 1], [83, 67, 76], [38, 28, 88], [121, 43, 61], [10, 12, 12], [115, 45, 125], [52, 51, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [119, 56], []]
 b := ![[], [125, 117, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [13, 27, 64, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17886685, 11594681, 3962186, -6082453, -3635344]
  a := ![-1, -7, 5, 5, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2898729, 7260378, 5008668, -6082453, -3635344]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 30, 8, -4, -4]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![31, 30, 8, -4, -4]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![24, 93, 1, 0, 0], ![54, 63, 0, 1, 0], ![18, 52, 0, 0, 1]] where
  M :=![![![31, 30, 8, -4, -4], ![96, 75, 52, -16, -16], ![192, 146, 59, -12, -32], ![336, 252, 68, -61, -16], ![144, 150, 144, 4, -69]]]
  hmulB := by decide  
  f := ![![![-1439, -834, -240, 380, 300]], ![![-7200, -4219, -1228, 1920, 1520]], ![![-5688, -3331, -969, 1516, 1200]], ![![-4518, -2643, -768, 1203, 952]], ![![-3618, -2118, -616, 964, 763]]]
  g := ![![![1, -2, 8, -4, -4], ![0, -23, 52, -16, -16], ![0, -23, 59, -12, -32], ![18, -11, 68, -61, -16], ![-18, -78, 144, 4, -69]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [100, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 126], [0, 1]]
 g := ![![[82, 47], [68, 8], [43, 17], [117, 84], [60, 16], [55, 1]], ![[0, 80], [0, 119], [89, 110], [38, 43], [51, 111], [110, 126]]]
 h' := ![![[55, 126], [58, 89], [18, 32], [111, 12], [96, 46], [88, 4], [0, 1]], ![[0, 1], [0, 38], [0, 95], [9, 115], [86, 81], [54, 123], [55, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115]]
 b := ![[], [38, 121]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [100, 72, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![59764, 25464, -26348, -9976, 11116]
  a := ![0, -4, -2, -18, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8116, 19892, -26348, -9976, 11116]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![1439, 834, 240, -380, -300]] ![![31, 30, 8, -4, -4]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0, 0, 0]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]] where
  M :=![![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 5 2 7 [17, 119, 120, 125, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 21, 74, 69, 129], [110, 24, 41, 2, 65], [25, 9, 119, 20, 94], [57, 76, 28, 40, 105], [0, 1]]
 g := ![![[19, 9, 110, 122, 125], [28, 56, 18, 90, 48], [23, 87, 50, 75], [125, 120, 36, 77], [11, 6, 0, 1], [], []], ![[60, 79, 1, 70, 42, 62, 31, 55], [83, 21, 45, 6, 22, 60, 111, 36], [66, 94, 22, 101], [98, 62, 120, 4], [83, 69, 51, 105], [44, 53, 82, 12], [1, 35, 117, 4]], ![[4, 29, 28, 25, 36, 107, 97, 9], [111, 6, 106, 126, 71, 27, 52, 114], [77, 2, 104, 113], [16, 81], [76, 1, 29, 77], [10, 72, 120, 36], [98, 30, 129, 33]], ![[117, 98, 86, 67, 34, 63, 20, 27], [78, 87, 100, 120, 106, 45, 31, 39], [130, 67, 80, 75], [82, 35, 89, 129], [107, 79, 111, 4], [59, 8, 58, 64], [55, 70, 92, 59]], ![[121, 80, 31, 16, 47, 37, 28, 62], [43, 96, 61, 64, 109, 45, 109, 35], [36, 125, 118, 75], [63, 35, 5, 62], [98, 4, 4, 36], [96, 17, 17, 58], [56, 8, 16, 21]]]
 h' := ![![[70, 21, 74, 69, 129], [48, 92, 41, 12, 16], [61, 114, 1, 54, 110], [94, 30, 89, 24, 72], [75, 30, 62, 115, 48], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[110, 24, 41, 2, 65], [109, 13, 74, 124, 118], [38, 88, 101, 72, 84], [80, 76, 74, 31, 106], [82, 78, 19, 101, 129], [24, 79, 5, 3, 74], [36, 130, 73, 85, 76], [70, 21, 74, 69, 129]], ![[25, 9, 119, 20, 94], [66, 66, 66, 78, 47], [13, 11, 3, 121, 77], [55, 98, 9, 63, 84], [117, 15, 30, 9], [112, 99, 101, 89, 48], [85, 51, 64, 121, 125], [110, 24, 41, 2, 65]], ![[57, 76, 28, 40, 105], [28, 68, 98, 5, 60], [20, 65, 93, 53, 22], [93, 115, 105, 14, 59], [96, 90, 104, 99, 103], [122, 130, 73, 126, 2], [83, 51, 17, 20, 8], [25, 9, 119, 20, 94]], ![[0, 1], [46, 23, 114, 43, 21], [102, 115, 64, 93, 100], [37, 74, 116, 130, 72], [86, 49, 47, 69, 113], [124, 85, 83, 44, 6], [70, 30, 107, 36, 53], [57, 76, 28, 40, 105]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 24, 92, 42], [], [], []]
 b := ![[], [87, 101, 30, 50, 21], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 5
  hpos := by decide
  P := [17, 119, 120, 125, 0, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4131008812234, 2399087655737, 686396200936, -1083346239482, -869569873415]
  a := ![13, -7, 4, 2, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![31534418414, 18313646227, 5239665656, -8269818622, -6637937965]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 38579489651 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 98, 44, -16, -18]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![127, 98, 44, -16, -18]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![34, 117, 1, 0, 0], ![132, 97, 0, 1, 0], ![12, 103, 0, 0, 1]] where
  M :=![![![127, 98, 44, -16, -18], ![432, 337, 156, -56, -64], ![768, 590, 265, -100, -112], ![1128, 864, 388, -155, -168], ![1176, 890, 396, -164, -179]]]
  hmulB := by decide  
  f := ![![![743, 46, -196, -24, 54]], ![![-1296, -95, 356, 40, -96]], ![![-914, -69, 253, 28, -68]], ![![-204, -23, 64, 5, -16]], ![![-900, -67, 248, 28, -67]]]
  g := ![![![7, -12, 44, -16, -18], ![24, -43, 156, -56, -64], ![46, -67, 265, -100, -112], ![76, -89, 388, -155, -168], ![84, -81, 396, -164, -179]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [18, 123, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 136], [0, 1]]
 g := ![![[121, 99], [107], [119], [66, 120], [112], [59], [1]], ![[0, 38], [107], [119], [102, 17], [112], [59], [1]]]
 h' := ![![[14, 136], [118, 109], [20, 92], [45, 16], [108, 42], [84, 48], [119, 14], [0, 1]], ![[0, 1], [0, 28], [75, 45], [132, 121], [11, 95], [71, 89], [41, 123], [14, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [20, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [18, 123, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6052, 2369, -3142, -1318, 1802]
  a := ![-1, -1, -1, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1936, 2279, -3142, -1318, 1802]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -1, -6, 0, 4]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![5, -1, -6, 0, 4]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![84, 81, 1, 0, 0], ![46, 126, 0, 1, 0], ![93, 87, 0, 0, 1]] where
  M :=![![![5, -1, -6, 0, 4], ![-96, -45, 14, 20, 0], ![0, -21, -65, 14, 40], ![-432, -216, 38, 85, 28], ![-120, -121, -162, 72, 105]]]
  hmulB := by decide  
  f := ![![![-587, -489, -236, 76, 92]], ![![-2208, -1683, -762, 264, 304]], ![![-1692, -1316, -605, 206, 240]], ![![-2266, -1742, -794, 273, 316]], ![![-1839, -1431, -658, 224, 261]]]
  g := ![![![1, 1, -6, 0, 4], ![-16, -27, 14, 20, 0], ![8, 0, -65, 14, 40], ![-74, -120, 38, 85, 28], ![3, -38, -162, 72, 105]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P1 : CertificateIrreducibleZModOfList' 137 2 2 7 [91, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 136], [0, 1]]
 g := ![![[56, 122], [88], [99], [68, 30], [44], [44], [1]], ![[50, 15], [88], [99], [80, 107], [44], [44], [1]]]
 h' := ![![[110, 136], [134, 81], [14, 122], [114, 109], [47, 21], [30, 27], [46, 110], [0, 1]], ![[0, 1], [2, 56], [8, 15], [48, 28], [28, 116], [123, 110], [90, 27], [110, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [81, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N1 : CertifiedPrimeIdeal' SI137N1 137 where
  n := 2
  hpos := by decide
  P := [91, 27, 1]
  hirr := P137P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-71, -913, -3506, 1013, 2522]
  a := ![3, 3, 0, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![97, -467, -3506, 1013, 2522]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N1 B_one_repr
lemma NI137N1 : Nat.card (O ⧸ I137N1) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-139, -5, 36, 4, -10]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![-139, -5, 36, 4, -10]] 
 ![![137, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![93, 0, 1, 0, 0], ![117, 0, 0, 1, 0], ![114, 0, 0, 0, 1]] where
  M :=![![![-139, -5, 36, 4, -10], ![240, 15, -58, -8, 16], ![-192, -5, 55, 6, -16], ![72, 18, -14, -5, 4], ![-240, -9, 72, 8, -21]]]
  hmulB := by decide  
  f := ![![![-299, -173, -58, 80, 70]], ![![-45, -26, -8, 12, 10]], ![![-231, -134, -45, 62, 54]], ![![-327, -189, -60, 87, 74]], ![![-342, -199, -66, 92, 79]]]
  g := ![![![-20, -5, 36, 4, -10], ![33, 15, -58, -8, 16], ![-30, -5, 55, 6, -16], ![9, 18, -14, -5, 4], ![-39, -9, 72, 8, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![127, 98, 44, -16, -18]] ![![5, -1, -6, 0, 4]]
  ![![299, 173, 58, -80, -70]] where
 M := ![![![299, 173, 58, -80, -70]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![299, 173, 58, -80, -70]] ![![-139, -5, 36, 4, -10]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27107, -516, 7388, 693, -2062]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-27107, -516, 7388, 693, -2062]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![116, 71, 19, 1, 0], ![10, 20, 63, 0, 1]] where
  M :=![![![-27107, -516, 7388, 693, -2062], ![49488, 4349, -10666, -1720, 2772], ![-33264, 2445, 11613, 422, -3440], ![16536, 6342, 476, -1287, -542], ![-38124, 4148, 14412, 225, -4393]]]
  hmulB := by decide  
  f := ![![![-3569, -1022, 1652, -59, -256]], ![![6144, 781, -2950, 1256, -236]], ![![2832, 4151, -947, -3894, 2512]], ![![308, -10, -153, 121, -46]], ![![2230, 2081, -875, -1665, 1157]]]
  g := ![![![-625, -61, 893, 693, -2062], ![1592, 511, -1098, -1720, 2772], ![-344, 297, 1585, 422, -3440], ![1232, 781, 425, -1287, -542], ![-146, 547, 2064, 225, -4393]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [3, 4, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [138, 5, 129], [103, 133, 10], [0, 1]]
 g := ![![[93, 120, 42], [107, 9, 35], [135, 28], [86, 21, 127], [66, 69], [102, 1], []], ![[64, 117, 62, 69], [43, 19, 7, 131], [50, 16], [87, 19, 18, 52], [52, 38], [132, 36], [92, 100]], ![[124, 8, 14, 132], [9, 117, 19, 32], [23, 91], [19, 124, 65, 61], [76, 55], [17, 25], [72, 100]]]
 h' := ![![[138, 5, 129], [96, 126, 96], [134, 53, 70], [20, 76, 58], [30, 27, 108], [111, 6, 114], [0, 0, 1], [0, 1]], ![[103, 133, 10], [119, 38, 110], [13, 65, 23], [118, 115, 4], [49, 25, 55], [30, 22, 90], [3, 17, 133], [138, 5, 129]], ![[0, 1], [133, 114, 72], [17, 21, 46], [15, 87, 77], [50, 87, 115], [0, 111, 74], [107, 122, 5], [103, 133, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 33], []]
 b := ![[], [18, 11, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [3, 4, 37, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4785159, -3081933, -1381524, 1612602, 1261770]
  a := ![1, 5, -3, -2, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1470969, -1027425, -802248, 1612602, 1261770]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 25, 12, -3, -4]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![31, 25, 12, -3, -4]] 
 ![![139, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![81, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![101, 0, 0, 0, 1]] where
  M :=![![![31, 25, 12, -3, -4], ![96, 81, 40, -8, -12], ![144, 126, 65, -8, -16], ![144, 144, 82, 5, -10], ![84, 109, 72, 21, 3]]]
  hmulB := by decide  
  f := ![![![157, -111, 34, 13, -10]], ![![39, -24, 6, 3, -2]], ![![87, -67, 23, 7, -6]], ![![43, -31, 8, 6, -4]], ![![119, -78, 24, 6, -5]]]
  g := ![![![-9, 25, 12, -3, -4], ![-31, 81, 40, -8, -12], ![-53, 126, 65, -8, -16], ![-75, 144, 82, 5, -10], ![-75, 109, 72, 21, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-121, -59, 54, 27, -26]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![-121, -59, 54, 27, -26]] 
 ![![139, 0, 0, 0, 0], ![68, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![93, 0, 0, 0, 1]] where
  M :=![![![-121, -59, 54, 27, -26], ![624, 273, -276, -100, 108], ![-1296, -520, 589, 156, -200], ![2088, 766, -938, -161, 258], ![-2508, -899, 1154, 175, -315]]]
  hmulB := by decide  
  f := ![![![-1111675, -47587, 281092, 31907, -76896]], ![![-530564, -22711, 134156, 15228, -36700]], ![![-418899, -17931, 105921, 12023, -28976]], ![![-309399, -13243, 78234, 8880, -21402]], ![![-756969, -32402, 191404, 21726, -52361]]]
  g := ![![![18, -59, 54, 27, -26], ![-72, 273, -276, -100, 108], ![119, -520, 589, 156, -200], ![-143, 766, -938, -161, 258], ![160, -899, 1154, 175, -315]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-27107, -516, 7388, 693, -2062]] ![![31, 25, 12, -3, -4]]
  ![![100603, 86451, 42658, -13492, -16704]] where
 M := ![![![100603, 86451, 42658, -13492, -16704]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![100603, 86451, 42658, -13492, -16704]] ![![-121, -59, 54, 27, -26]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![210029, 165410, 76728, -25159, -29746]]]
 hmul := by decide  
 g := ![![![![1511, 1190, 552, -181, -214]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12716659, 544505, -3215340, -365003, 879590]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![12716659, 544505, -3215340, -365003, 879590]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![25, 119, 11, 1, 0], ![86, 100, 73, 0, 1]] where
  M :=![![![12716659, 544505, -3215340, -365003, 879590], ![-21110160, -904177, 5337376, 606040, -1460012], ![17520144, 749714, -4430241, -502672, 1212080], ![-3989880, -172072, 1007858, 115059, -275338], ![20967180, 896149, -5302712, -601103, 1451105]]]
  hmulB := by decide  
  f := ![![![6623, 2771, -2982, -929, 1088]], ![![-26112, -10185, 11752, 2740, -3716]], ![![44592, 15998, -20357, -3112, 5480]], ![![-16805, -6596, 7545, 1804, -2410]], ![![8558, 2723, -3999, -219, 851]]]
  g := ![![![-361094, -295162, -425573, -365003, 879590], ![599328, 489787, 706388, 606040, -1460012], ![-497664, -406982, -586461, -502672, 1212080], ![112837, 91743, 133167, 115059, -275338], ![-595975, -487806, -702156, -601103, 1451105]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [106, 127, 63, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 63, 12], [85, 85, 137], [0, 1]]
 g := ![![[52, 23, 7], [67, 35], [110, 105, 4], [76, 47], [87, 133, 130], [86, 1], []], ![[113, 52, 20, 97], [6, 64], [140, 89, 148, 55], [21, 53], [140, 15, 79, 87], [77, 73], [39, 144]], ![[8, 127, 24, 77], [126, 86], [22, 64, 114, 78], [10, 132], [22, 10, 106, 56], [80, 95], [63, 144]]]
 h' := ![![[1, 63, 12], [4, 68, 56], [111, 103, 66], [97, 97, 147], [16, 18, 14], [122, 147, 117], [0, 0, 1], [0, 1]], ![[85, 85, 137], [21, 115, 63], [106, 27, 141], [116, 103, 100], [133, 129, 65], [64, 0, 87], [39, 24, 85], [1, 63, 12]], ![[0, 1], [60, 115, 30], [119, 19, 91], [96, 98, 51], [115, 2, 70], [30, 2, 94], [100, 125, 63], [85, 85, 137]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136, 67], []]
 b := ![[], [38, 90, 131], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [106, 127, 63, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19722, 8144, -8424, -2728, 3143]
  a := ![4, 0, 0, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1224, 124, -1395, -2728, 3143]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6623, 2771, -2982, -929, 1088]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![6623, 2771, -2982, -929, 1088]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![139, 138, 1, 0, 0], ![39, 98, 0, 1, 0], ![38, 134, 0, 0, 1]] where
  M :=![![![6623, 2771, -2982, -929, 1088], ![-26112, -10185, 11752, 2740, -3716], ![44592, 15998, -20357, -3112, 5480], ![-52704, -16042, 24194, 193, -4366], ![61548, 18067, -28538, 439, 4791]]]
  hmulB := by decide  
  f := ![![![12716659, 544505, -3215340, -365003, 879590]], ![![-21110160, -904177, 5337376, 606040, -1460012]], ![![-7570915, -324433, 1914063, 217419, -523534]], ![![-10582791, -453327, 2675654, 303838, -731896]], ![![-15601082, -668271, 3944448, 447907, -1078967]]]
  g := ![![![2792, 2413, -2982, -929, 1088], ![-10908, -9413, 11752, 2740, -3716], ![18707, 16080, -20357, -3112, 5480], ![-21861, -18716, 24194, 193, -4366], ![25699, 21955, -28538, 439, 4791]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P1 : CertificateIrreducibleZModOfList' 149 2 2 7 [42, 107, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 148], [0, 1]]
 g := ![![[148, 110], [148], [72, 28], [102], [20, 35], [125], [1]], ![[0, 39], [148], [56, 121], [102], [0, 114], [125], [1]]]
 h' := ![![[42, 148], [41, 109], [105, 44], [122, 37], [54, 20], [90, 83], [107, 42], [0, 1]], ![[0, 1], [0, 40], [16, 105], [37, 112], [0, 129], [0, 66], [83, 107], [42, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [51, 104]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N1 : CertifiedPrimeIdeal' SI149N1 149 where
  n := 2
  hpos := by decide
  P := [42, 107, 1]
  hirr := P149P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-212292, -115467, -23830, 61531, 45090]
  a := ![7, -21, -1, -23, -21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6799, -59725, -23830, 61531, 45090]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N1 B_one_repr
lemma NI149N1 : Nat.card (O ⧸ I149N1) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![12716659, 544505, -3215340, -365003, 879590]] ![![6623, 2771, -2982, -929, 1088]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1199381, 523248, -535592, -192314, 210332]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![1199381, 523248, -535592, -192314, 210332]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![75, 140, 117, 1, 0], ![67, 88, 20, 0, 1]] where
  M :=![![![1199381, 523248, -535592, -192314, 210332], ![-5047968, -2034491, 2272452, 611472, -769256], ![9231072, 3454622, -4184475, -804572, 1222944], ![-12151344, -3990220, 5568856, 401565, -1224516], ![14486616, 4667136, -6648872, -372626, 1397665]]]
  hmulB := by decide  
  f := ![![![-51397, -9592, 7240, 4798, 324]], ![![-7776, -38125, -27484, 17072, 19192]], ![![-230304, -106114, -16813, 49284, 34144]], ![![-213873, -123942, -35399, 57135, 45000]], ![![-62113, -42800, -15580, 19648, 16637]]]
  g := ![![![10137, 59192, 117606, -192314, 210332], ![4184, -132093, -356852, 611472, -769256], ![-81876, 56130, 433719, -804572, 1222944], ![263403, 314888, -112079, 401565, -1224516], ![-339139, -438144, 59570, -372626, 1397665]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [12, 75, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [143, 75, 136], [113, 75, 15], [0, 1]]
 g := ![![[51, 56, 91], [30, 21, 94], [116, 103, 80], [22, 16], [65, 66, 44], [105, 1], []], ![[137, 150, 99, 85], [122, 148, 128, 100], [4, 55, 117, 88], [91, 136], [101, 104, 123, 124], [147, 38], [84, 74]], ![[20, 91, 53, 87], [137, 117], [31, 139, 51, 75], [34, 91], [83, 149, 79, 142], [132, 38], [54, 74]]]
 h' := ![![[143, 75, 136], [93, 97, 53], [118, 38, 83], [59, 140, 82], [126, 57, 4], [99, 116, 78], [0, 0, 1], [0, 1]], ![[113, 75, 15], [21, 7, 104], [133, 38, 68], [51, 70, 124], [122, 17, 49], [133, 112, 33], [113, 68, 75], [143, 75, 136]], ![[0, 1], [90, 47, 145], [114, 75], [64, 92, 96], [87, 77, 98], [97, 74, 40], [41, 83, 75], [113, 75, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110, 24], []]
 b := ![[], [146, 115, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [12, 75, 46, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16724702, 9646807, 2632368, -4505640, -3487270]
  a := ![1, -6, 1, -5, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3895992, 6273617, 3970448, -4505640, -3487270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51397, -9592, 7240, 4798, 324]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-51397, -9592, 7240, 4798, 324]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![55, 34, 1, 0, 0], ![93, 80, 0, 1, 0], ![17, 2, 0, 0, 1]] where
  M :=![![![-51397, -9592, 7240, 4798, 324], ![-7776, -38125, -27484, 17072, 19192], ![-230304, -106114, -16813, 49284, 34144], ![-405840, -243004, -73368, 111227, 88972], ![-645096, -342856, -82808, 157366, 118703]]]
  hmulB := by decide  
  f := ![![![1199381, 523248, -535592, -192314, 210332]], ![![-5047968, -2034491, 2272452, 611472, -769256]], ![![-638635, -244632, 288883, 62306, -88500]], ![![-2016201, -782036, 910960, 208173, -286120]], ![![164107, 62870, -74232, -16020, 22747]]]
  g := ![![![-5969, -4240, 7240, 4798, 324], ![-2716, -3363, -27484, 17072, 19192], ![-29599, -23480, -16813, 49284, 34144], ![-54485, -45196, -73368, 111227, 88972], ![-84395, -68570, -82808, 157366, 118703]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [13, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [147, 150], [0, 1]]
 g := ![![[70, 9], [18, 136], [83, 85], [40], [144, 90], [16], [1]], ![[34, 142], [78, 15], [45, 66], [40], [86, 61], [16], [1]]]
 h' := ![![[147, 150], [68, 3], [129, 49], [60, 113], [91, 77], [112, 40], [138, 147], [0, 1]], ![[0, 1], [56, 148], [84, 102], [61, 38], [85, 74], [103, 111], [3, 4], [147, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [84, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [13, 4, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21530, -11242, -3361, 6740, 5849]
  a := ![3, 8, -1, 11, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3728, -2966, -3361, 6740, 5849]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![1199381, 523248, -535592, -192314, 210332]] ![![-51397, -9592, 7240, 4798, 324]]
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


lemma PB934I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB934I3 : PrimesBelowBoundCertificateInterval O 103 151 934 where
  m := 9
  g := ![3, 2, 1, 2, 1, 3, 3, 2, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB934I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
    · exact ![I137N0, I137N1, I137N2]
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
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
    · exact ![1225043, 107, 107]
    · exact ![1295029, 11881]
    · exact ![18424351793]
    · exact ![2048383, 16129]
    · exact ![38579489651]
    · exact ![18769, 18769, 137]
    · exact ![2685619, 139, 139]
    · exact ![3307949, 22201]
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
      exact NI107N2
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
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I107N1, I107N2, I137N2, I139N1, I139N2]
  Il := ![[I107N1, I107N2], [], [], [], [], [I137N2], [I139N1, I139N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
