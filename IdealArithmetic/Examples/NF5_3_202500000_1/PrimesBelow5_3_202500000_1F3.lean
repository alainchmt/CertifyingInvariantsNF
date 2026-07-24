
import IdealArithmetic.Examples.NF5_3_202500000_1.RI5_3_202500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-205, 63, 39, -50, 94]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-205, 63, 39, -50, 94]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![89, 22, 1, 0, 0], ![19, 18, 0, 1, 0], ![78, 66, 0, 0, 1]] where
  M :=![![![-205, 63, 39, -50, 94], ![652, -200, -126, 161, -300], ![-2078, 639, 409, -517, 966], ![1756, -533, -346, 440, -812], ![-230, 70, 50, -60, 111]]]
  hmulB := by decide  
  f := ![![![-81, 19, 17, 0, -28]], ![![-224, -126, 2, 23, 0]], ![![-113, -12, 14, 5, -22]], ![![-49, -18, 3, 4, -4]], ![![-196, -62, 14, 14, -21]]]
  g := ![![![-94, -57, 39, -50, 94], ![301, 182, -126, 161, -300], ![-972, -587, 409, -517, 966], ![818, 493, -346, 440, -812], ![-114, -68, 50, -60, 111]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [17, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 106], [0, 1]]
 g := ![![[84, 101], [25, 23], [30], [23, 33], [23], [70, 1]], ![[92, 6], [30, 84], [30], [86, 74], [23], [33, 106]]]
 h' := ![![[70, 106], [3, 84], [3, 39], [37, 43], [99, 56], [94, 68], [0, 1]], ![[0, 1], [105, 23], [58, 68], [51, 64], [60, 51], [39, 39], [70, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [23, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [17, 37, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44891, 26985, 20180, 17955, 37686]
  a := ![-17, -10, -24, -5, -51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-47026, -30163, 20180, 17955, 37686]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, 6, 3, -3, 8]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-15, 6, 3, -3, 8]] 
 ![![107, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![96, 0, 1, 0, 0], ![92, 0, 0, 1, 0], ![79, 0, 0, 0, 1]] where
  M :=![![![-15, 6, 3, -3, 8], ![58, -13, -6, 14, -18], ![-116, 60, 35, -22, 84], ![190, -14, -4, 53, -22], ![10, 10, 8, 4, 15]]]
  hmulB := by decide  
  f := ![![![245, -184, -89, 13, 166]], ![![47, -21, -13, 1, 24]], ![![224, -152, -77, 10, 144]], ![![202, -154, -74, 11, 138]], ![![171, -146, -67, 11, 125]]]
  g := ![![![-7, 6, 3, -3, 8], ![9, -13, -6, 14, -18], ![-84, 60, 35, -22, 84], ![-22, -14, -4, 53, -22], ![-23, 10, 8, 4, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 29, 10, -7, -4]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![-17, 29, 10, -7, -4]] 
 ![![107, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-17, 29, 10, -7, -4], ![-46, -38, -2, 19, -42], ![-298, -67, 21, -29, 114], ![170, -113, -52, 46, -34], ![104, 88, 8, -18, 3]]]
  hmulB := by decide  
  f := ![![![-879, 847, 272, 51, 928]], ![![-554, 600, 200, 53, 662]], ![![40, 99, 47, 41, 118]], ![![247, 166, 98, 113, 210]], ![![46, 72, 36, 34, 87]]]
  g := ![![![-20, 29, 10, -7, -4], ![27, -38, -2, 19, -42], ![41, -67, 21, -29, 114], ![80, -113, -52, 46, -34], ![-60, 88, 8, -18, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2

def I107N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 6, 0, 0, 8]] i)))

def SI107N3: IdealEqSpanCertificate' Table ![![9, 6, 0, 0, 8]] 
 ![![107, 0, 0, 0, 0], ![101, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![9, 6, 0, 0, 8], ![64, 17, 6, 8, 0], ![16, 66, 35, 26, 48], ![172, 46, 50, 71, 68], ![64, -2, 8, 22, 33]]]
  hmulB := by decide  
  f := ![![![-340045, 103430, 69508, -86648, 159880]], ![![-310643, 94487, 63498, -79156, 146056]], ![![-259241, 78852, 52991, -66058, 121888]], ![![-38071, 11580, 7782, -9701, 17900]], ![![-64557, 19636, 13196, -16450, 30353]]]
  g := ![![![-7, 6, 0, 0, 8], ![-21, 17, 6, 8, 0], ![-99, 66, 35, 26, 48], ![-101, 46, 50, 71, 68], ![-13, -2, 8, 22, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N3 : Nat.card (O ⧸ I107N3) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N3)

lemma isPrimeI107N3 : Ideal.IsPrime I107N3 := prime_ideal_of_norm_prime hp107.out _ NI107N3
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-205, 63, 39, -50, 94]] ![![-15, 6, 3, -3, 8]]
  ![![-6355, 1931, 1324, -1635, 3012]] where
 M := ![![![-6355, 1931, 1324, -1635, 3012]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-6355, 1931, 1324, -1635, 3012]] ![![-17, 29, 10, -7, -4]]
  ![![-340045, 103430, 69508, -86648, 159880]] where
 M := ![![![-340045, 103430, 69508, -86648, 159880]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N2 : IdealMulLeCertificate' Table 
  ![![-340045, 103430, 69508, -86648, 159880]] ![![9, 6, 0, 0, 8]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2, I107N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
    exact isPrimeI107N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1 ⊙ MulI107N2)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107497, 57723, -201, -9214, -598]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![107497, 57723, -201, -9214, -598]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![88, 5, 84, 34, 1]] where
  M :=![![![107497, 57723, -201, -9214, -598], ![-23212, 97886, 30282, -10415, -55284], ![-463102, -119193, 36359, 25147, -62490], ![-311980, -186037, -4490, 28822, 11036], ![275906, 10442, -38258, -8172, 67641]]]
  hmulB := by decide  
  f := ![![![-61029, 18565, 12479, -15552, 28700]], ![![198496, -60360, -40570, 50585, -93312]], ![![-645326, 196339, 131965, -164437, 303510]], ![![550792, -167413, -112514, 140372, -258808]], ![![-366410, 111530, 74966, -93359, 172405]]]
  g := ![![![1469, 557, 459, 102, -598], ![44420, 3434, 42882, 17149, -55284], ![46202, 1773, 48491, 19723, -62490], ![-11772, -2213, -8546, -3178, 11036], ![-52078, -3007, -52478, -21174, 67641]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 4 2 6 [62, 53, 18, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 49, 86, 43], [45, 66, 47, 15], [48, 102, 85, 51], [0, 1]]
 g := ![![[93, 51, 20, 25], [1, 51, 75], [91, 100, 101, 89], [105, 31, 70, 4], [7, 104, 1], []], ![[58, 34, 74, 100, 4, 63], [3, 37, 81], [15, 60, 17, 77, 88, 29], [38, 2, 37, 72, 24, 4], [43, 65, 61], [22, 24, 88, 105, 46, 46]], ![[82, 59, 13, 22, 106, 3], [42, 9, 20], [84, 23, 71, 34, 63, 83], [72, 55, 52, 92, 39, 66], [101, 100, 5], [41, 58, 36, 17, 26, 105]], ![[103, 56, 84, 60, 72, 56], [102, 56, 3], [96, 22, 16, 102, 76, 19], [16, 28, 45, 68, 22, 40], [31, 80, 88], [9, 23, 32, 80, 0, 107]]]
 h' := ![![[11, 49, 86, 43], [69, 20, 69, 5], [26, 14, 89, 82], [30, 38, 58, 78], [2, 48, 77, 2], [0, 0, 0, 1], [0, 1]], ![[45, 66, 47, 15], [107, 14, 35, 107], [27, 80, 73, 9], [95, 6, 53, 73], [58, 2, 65, 75], [76, 91, 104, 72], [11, 49, 86, 43]], ![[48, 102, 85, 51], [83, 17, 105, 83], [17, 92, 0, 67], [39, 108, 7, 10], [17, 8, 42, 87], [75, 56, 10, 88], [45, 66, 47, 15]], ![[0, 1], [69, 58, 9, 23], [17, 32, 56, 60], [107, 66, 100, 57], [15, 51, 34, 54], [53, 71, 104, 57], [48, 102, 85, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [99, 79, 65], []]
 b := ![[], [], [101, 101, 69, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 4
  hpos := by decide
  P := [62, 53, 18, 5, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2720753065807102, 1028309792971173, 755998323026595, 979607379002779, 1403058137887449]
  a := ![-240, -181, -361, -1, -723]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1107783147415490, -54926430242808, -1074320048252469, -428663938616243, 1403058137887449]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 141158161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61029, -18565, -12479, 15552, -28700]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![61029, -18565, -12479, 15552, -28700]] 
 ![![109, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![91, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  M :=![![![61029, -18565, -12479, 15552, -28700], ![-198496, 60360, 40570, -50585, 93312], ![645326, -196339, -131965, 164437, -303510], ![-550792, 167413, 112514, -140372, 258808], ![80162, -24416, -16408, 20420, -37737]]]
  hmulB := by decide  
  f := ![![![-107497, -57723, 201, 9214, 598]], ![![-13594, -8312, -252, 1279, 584]], ![![-17448, -10557, -293, 1629, 694]], ![![-86883, -46484, 209, 7428, 398]], ![![-34090, -17042, 410, 2780, -445]]]
  g := ![![![905, -18565, -12479, 15552, -28700], ![-2925, 60360, 40570, -50585, 93312], ![9595, -196339, -131965, 164437, -303510], ![-8054, 167413, 112514, -140372, 258808], ![1214, -24416, -16408, 20420, -37737]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![107497, 57723, -201, -9214, -598]] ![![61029, -18565, -12479, 15552, -28700]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31187, -10812, -1350, 4244, -10494]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![31187, -10812, -1350, 4244, -10494]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![15, 25, 23, 72, 1]] where
  M :=![![![31187, -10812, -1350, 4244, -10494], ![-75464, 26287, 3270, -10300, 25464], ![183112, -63570, -7883, 24974, -61800], ![-112268, 38962, 4874, -15267, 37836], ![-25304, 8752, 1082, -3442, 8581]]]
  hmulB := by decide  
  f := ![![![-2181, 664, 446, -556, 1026]], ![![7096, -2157, -1450, 1808, -3336]], ![![-23072, 7018, 4717, -5878, 10848]], ![![19684, -5986, -4022, 5017, -9252]], ![![9101, -2767, -1859, 2320, -4277]]]
  g := ![![![1669, 2226, 2124, 6724, -10494], ![-4048, -5401, -5154, -16316, 25464], ![9824, 13110, 12509, 39598, -61800], ![-6016, -8026, -7658, -24243, 37836], ![-1363, -1821, -1737, -5498, 8581]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 4 2 6 [13, 26, 63, 67, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 49, 38, 108], [53, 30, 9, 33], [49, 33, 66, 85], [0, 1]]
 g := ![![[13, 105, 19, 1], [0, 16, 36], [109, 69, 63], [7, 36, 32], [97, 19, 46, 1], []], ![[84, 33, 40, 52, 37, 68], [80, 103, 28], [11, 71, 104], [49, 63, 72], [112, 96, 47, 11, 77, 10], [49, 100, 75, 0, 38, 101]], ![[92, 53, 32, 111, 111, 94], [63, 23, 25], [61, 109, 98], [62, 90, 83], [45, 55, 69, 100, 2, 39], [108, 58, 62, 20, 48, 3]], ![[50, 104, 86, 30, 98, 56], [20, 64, 97], [109, 8, 82], [104, 56, 60], [45, 56, 72, 108, 24, 91], [93, 84, 5, 59, 59, 83]]]
 h' := ![![[57, 49, 38, 108], [31, 91, 70, 112], [101, 77, 99, 107], [7, 46, 73, 17], [95, 56, 29, 22], [0, 0, 0, 1], [0, 1]], ![[53, 30, 9, 33], [97, 75, 40, 110], [81, 69, 34, 64], [26, 55, 26, 68], [95, 91, 3, 80], [27, 90, 19, 26], [57, 49, 38, 108]], ![[49, 33, 66, 85], [8, 15, 92, 30], [107, 101, 11, 108], [83, 1, 50, 95], [95, 20, 4, 99], [8, 83, 97, 91], [53, 30, 9, 33]], ![[0, 1], [105, 45, 24, 87], [34, 92, 82, 60], [35, 11, 77, 46], [101, 59, 77, 25], [50, 53, 110, 108], [49, 33, 66, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [79, 49, 90], []]
 b := ![[], [], [51, 13, 83, 100], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 4
  hpos := by decide
  P := [13, 26, 63, 67, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![59213889142, 21263319322, 15654729994, 21152178295, 28914818430]
  a := ![-15, -10, -22, -3, -46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3314233516, -6208912756, -5746779592, -18236413705, 28914818430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 163047361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2181, 664, 446, -556, 1026]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-2181, 664, 446, -556, 1026]] 
 ![![113, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-2181, 664, 446, -556, 1026], ![7096, -2157, -1450, 1808, -3336], ![-23072, 7018, 4717, -5878, 10848], ![19684, -5986, -4022, 5017, -9252], ![-2864, 872, 586, -730, 1349]]]
  hmulB := by decide  
  f := ![![![31187, -10812, -1350, 4244, -10494]], ![![4852, -1681, -210, 660, -1632]], ![![15972, -5538, -691, 2174, -5376]], ![![13910, -4822, -602, 1893, -4680]], ![![1984, -688, -86, 270, -667]]]
  g := ![![![-149, 664, 446, -556, 1026], ![484, -2157, -1450, 1808, -3336], ![-1576, 7018, 4717, -5878, 10848], ![1342, -5986, -4022, 5017, -9252], ![-196, 872, 586, -730, 1349]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![31187, -10812, -1350, 4244, -10494]] ![![-2181, 664, 446, -556, 1026]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2021, 609, 409, -516, 942]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-2021, 609, 409, -516, 942]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![91, 40, 1, 0, 0], ![87, 18, 0, 1, 0], ![6, 41, 0, 0, 1]] where
  M :=![![![-2021, 609, 409, -516, 942], ![6504, -2004, -1348, 1653, -3096], ![-21462, 6409, 4303, -5487, 9918], ![17804, -5643, -3800, 4502, -8700], ![-2746, 768, 514, -710, 1195]]]
  hmulB := by decide  
  f := ![![![5203, -1739, -225, 690, -1716]], ![![-12348, 4402, 556, -1701, 4140]], ![![73, 58, 4, -9, -6]], ![![1667, -518, -69, 212, -540]], ![![-3772, 1350, 170, -521, 1267]]]
  g := ![![![0, -355, 409, -516, 942], ![31, 1174, -1348, 1653, -3096], ![38, -3729, 4303, -5487, 9918], ![190, 3323, -3800, 4502, -8700], ![40, -441, 514, -710, 1195]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [5, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [103, 126], [0, 1]]
 g := ![![[81, 104], [111, 72], [42, 103], [68, 64], [1, 32], [103, 1]], ![[125, 23], [34, 55], [110, 24], [56, 63], [122, 95], [79, 126]]]
 h' := ![![[103, 126], [80, 55], [44, 31], [41, 105], [122, 119], [120, 63], [0, 1]], ![[0, 1], [30, 72], [62, 96], [61, 22], [60, 8], [5, 64], [103, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [63, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [5, 24, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![796469, 807917, 638203, 354380, 1222885]
  a := ![98, 72, 147, -1, 293]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-751562, -639664, 638203, 354380, 1222885]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 4, 2, 2, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![5, 4, 2, 2, 0]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![91, 73, 1, 0, 0], ![102, 56, 0, 1, 0], ![41, 52, 0, 0, 1]] where
  M :=![![![5, 4, 2, 2, 0], ![4, 5, 8, 8, 12], ![112, 16, 21, 44, 48], ![196, 68, 52, 69, 108], ![76, 32, 16, 20, 25]]]
  hmulB := by decide  
  f := ![![![-645, 220, 26, -86, 216]], ![![1556, -541, -64, 208, -516]], ![![403, -143, -17, 54, -132]], ![![186, -68, -8, 25, -60]], ![![433, -152, -18, 58, -143]]]
  g := ![![![-3, -2, 2, 2, 0], ![-16, -13, 8, 8, 12], ![-65, -51, 21, 44, 48], ![-126, -104, 52, 69, 108], ![-35, -28, 16, 20, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [78, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 126], [0, 1]]
 g := ![![[1, 115], [51, 13], [99, 15], [39, 84], [26, 99], [49, 1]], ![[48, 12], [53, 114], [72, 112], [91, 43], [51, 28], [98, 126]]]
 h' := ![![[49, 126], [86, 78], [25, 34], [6, 74], [4, 46], [115, 37], [0, 1]], ![[0, 1], [98, 49], [40, 93], [76, 53], [99, 81], [23, 90], [49, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [12, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [78, 78, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18784, 77179, 60185, 16494, 116865]
  a := ![-32, -24, -50, 8, -95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-93952, -89110, 60185, 16494, 116865]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4841, 1433, -329, -284, 560]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![4841, 1433, -329, -284, 560]] 
 ![![127, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![92, 0, 0, 1, 0], ![120, 0, 0, 0, 1]] where
  M :=![![![4841, 1433, -329, -284, 560], ![3912, 5446, 910, -711, -1704], ![-15054, 587, 2403, 315, -4266], ![-14880, -5125, 814, 954, -1360], ![6246, -3508, -1892, 236, 3411]]]
  hmulB := by decide  
  f := ![![![903041, -274535, -184507, 230134, -424402]], ![![76438, -23230, -15612, 19481, -35912]], ![![487616, -148231, -99621, 124267, -229150]], ![![590104, -179349, -120534, 150392, -277260]], ![![862626, -262238, -176242, 219836, -405393]]]
  g := ![![![-293, 1433, -329, -284, 560], ![1140, 5446, 910, -711, -1704], ![2522, 587, 2403, 315, -4266], ![670, -5125, 814, 954, -1360], ![-2094, -3508, -1892, 236, 3411]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-2021, 609, 409, -516, 942]] ![![5, 4, 2, 2, 0]]
  ![![8595, -3439, -2341, 2062, -5238]] where
 M := ![![![8595, -3439, -2341, 2062, -5238]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![8595, -3439, -2341, 2062, -5238]] ![![4841, 1433, -329, -284, 560]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![-2667, 20828, 6096, -2286, -11176]]]
 hmul := by decide  
 g := ![![![![-21, 164, 48, -18, -88]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0, 0, 0]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]] where
  M :=![![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 5 2 7 [19, 96, 109, 110, 99, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 123, 43, 130, 54], [116, 23, 31, 0, 26], [62, 24, 22, 110, 25], [68, 91, 35, 22, 26], [0, 1]]
 g := ![![[94, 101, 73, 110, 34], [63, 16, 99, 10, 105], [75, 33, 39, 89], [7, 116, 10, 44], [74, 128, 32, 1], [], []], ![[77, 110, 97, 17, 118, 33, 100, 92], [97, 121, 36, 59, 123, 114, 107, 31], [86, 115, 75, 105], [82, 54, 15, 52], [40, 123, 58, 60], [62, 73, 5, 34], [11, 39, 63, 34]], ![[52, 95, 93, 99, 128, 41, 82, 111], [20, 95, 67, 56, 119, 111, 47, 115], [30, 36, 85, 58], [86, 103, 8, 62], [84, 125, 2, 64], [22, 16, 124, 34], [100, 108, 17, 21]], ![[56, 106, 67, 110, 109, 9, 43, 80], [0, 79, 31, 64, 36, 38, 78, 94], [70, 83, 74, 109], [56, 97, 112, 108], [13, 66, 10, 33], [14, 23, 34, 105], [83, 126, 86, 101]], ![[91, 52, 84, 13, 44, 116, 2, 130], [54, 46, 104, 64, 81, 122, 57, 130], [110, 15, 50, 48], [35, 37, 0, 81], [21, 94, 81, 74], [7, 119, 65, 105], [46, 73, 113, 21]]]
 h' := ![![[48, 123, 43, 130, 54], [113, 105, 10, 60, 77], [118, 118, 119, 120, 57], [44, 62, 28, 66, 73], [35, 27, 129, 100, 31], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[116, 23, 31, 0, 26], [24, 71, 102, 82, 75], [78, 123, 129, 118, 93], [128, 117, 83, 115, 74], [30, 52, 96, 48, 107], [2, 18, 3, 55, 45], [130, 55, 17, 30, 54], [48, 123, 43, 130, 54]], ![[62, 24, 22, 110, 25], [42, 35, 66, 115, 121], [66, 27, 110, 14, 92], [80, 38, 79, 118, 53], [50, 75, 102, 47, 18], [104, 77, 106, 46, 123], [28, 103, 16, 72, 77], [116, 23, 31, 0, 26]], ![[68, 91, 35, 22, 26], [99, 81, 73, 48, 97], [79, 24, 79, 96, 128], [19, 119, 70, 67, 41], [67, 88, 15, 80, 97], [24, 114, 97, 2, 66], [40, 81, 46, 128, 74], [62, 24, 22, 110, 25]], ![[0, 1], [73, 101, 11, 88, 23], [19, 101, 87, 45, 23], [119, 57, 2, 27, 21], [103, 20, 51, 118, 9], [41, 53, 56, 28, 27], [82, 23, 51, 32, 57], [68, 91, 35, 22, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 89, 26, 118], [], [], []]
 b := ![[], [51, 117, 30, 42, 90], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 5
  hpos := by decide
  P := [19, 96, 109, 110, 99, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21013738021817, 6382033050788, 4365305105416, -5402147465472, 9943623206460]
  a := ![14, 18, 30, -26, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-160410213907, 48717809548, 33322939736, -41237766912, 75905520660]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-57, 12, 3, -7, 18]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-57, 12, 3, -7, 18]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![49, 69, 36, 1, 0], ![92, 96, 37, 0, 1]] where
  M :=![![![-57, 12, 3, -7, 18], ![130, -49, -12, 20, -42], ![-296, 120, 23, -58, 120], ![226, -62, -22, 31, -90], ![-2, -14, 2, 2, -13]]]
  hmulB := by decide  
  f := ![![![-7, 2, 1, -1, 0]], ![![-2, -9, -2, 2, -6]], ![![-44, -4, -1, -10, 12]], ![![-15, -5, -1, -2, 0]], ![![-18, -6, -1, -2, -1]]]
  g := ![![![-10, -9, -3, -7, 18], ![22, 19, 6, 20, -42], ![-62, -54, -17, -58, 120], ![51, 47, 16, 31, -90], ![8, 8, 3, 2, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [37, 74, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 111, 40], [68, 25, 97], [0, 1]]
 g := ![![[126, 82, 44], [2, 49], [20, 81], [120, 43, 56], [51, 72], [64, 1], []], ![[127, 88, 75, 54], [32, 105], [39, 17], [54, 4, 63, 10], [105, 34], [107, 77], [36, 93]], ![[60, 134, 30, 48], [93, 133], [30, 74], [35, 30, 71, 110], [106, 74], [71, 128], [116, 93]]]
 h' := ![![[133, 111, 40], [31, 61, 27], [67, 11, 7], [81, 48, 9], [45, 66, 78], [98, 22, 49], [0, 0, 1], [0, 1]], ![[68, 25, 97], [12, 33, 101], [127, 83, 67], [101, 68, 90], [20, 8, 69], [53, 93, 50], [54, 131, 25], [133, 111, 40]], ![[0, 1], [128, 43, 9], [125, 43, 63], [31, 21, 38], [15, 63, 127], [52, 22, 38], [58, 6, 111], [68, 25, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129, 125], []]
 b := ![[], [97, 11, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [37, 74, 73, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13523003, 4936433, 3643288, 4849309, 6728960]
  a := ![12, 6, 10, 5, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6154434, -7121504, -3064988, 4849309, 6728960]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -2, -1, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![7, -2, -1, 1, 0]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![13, 28, 1, 0, 0], ![20, 26, 0, 1, 0], ![94, 115, 0, 0, 1]] where
  M :=![![![7, -2, -1, 1, 0], ![2, 9, 2, -2, 6], ![44, 4, 1, 10, -12], ![-10, 18, 12, 3, 18], ![2, -6, 0, 4, 5]]]
  hmulB := by decide  
  f := ![![![57, -12, -3, 7, -18]], ![![-130, 49, 12, -20, 42]], ![![-19, 8, 2, -3, 6]], ![![-18, 8, 2, -3, 6]], ![![-70, 33, 8, -12, 23]]]
  g := ![![![0, 0, -1, 1, 0], ![-4, -5, 2, -2, 6], ![7, 8, 1, 10, -12], ![-14, -18, 12, 3, 18], ![-4, -5, 0, 4, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P1 : CertificateIrreducibleZModOfList' 137 2 2 7 [1, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 136], [0, 1]]
 g := ![![[109, 1], [32], [56], [61, 64], [28], [99], [1]], ![[0, 136], [32], [56], [72, 73], [28], [99], [1]]]
 h' := ![![[28, 136], [28, 136], [103, 124], [76, 59], [123, 8], [39, 113], [136, 28], [0, 1]], ![[0, 1], [0, 1], [13, 13], [84, 78], [73, 129], [52, 24], [98, 109], [28, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111]]
 b := ![[], [45, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N1 : CertifiedPrimeIdeal' SI137N1 137 where
  n := 2
  hpos := by decide
  P := [1, 109, 1]
  hirr := P137P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6285, 4495, 2784, 2843, 5086]
  a := ![-8, -6, -11, -1, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4123, -5345, 2784, 2843, 5086]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N1 B_one_repr
lemma NI137N1 : Nat.card (O ⧸ I137N1) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-57, 12, 3, -7, 18]] ![![7, -2, -1, 1, 0]]
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


def P139P0 : CertificateIrreducibleZModOfList' 139 5 2 7 [36, 6, 2, 80, 44, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 118, 133, 129, 68], [68, 124, 80, 113, 111], [5, 42, 111, 62, 127], [80, 132, 93, 113, 111], [0, 1]]
 g := ![![[102, 9, 30, 97, 81], [35, 122, 46, 123, 65], [49, 35, 32, 131], [93, 35, 128, 105, 113], [111, 49, 95, 1], [], []], ![[54, 60, 128, 99, 115, 133, 52, 76], [22, 85, 76, 20, 78, 81, 67, 8], [75, 54, 101, 30], [30, 90, 6, 109, 2, 3, 104, 12], [49, 77, 80, 7], [124, 84, 18, 47], [12, 55, 70, 37]], ![[10, 83, 135, 123, 55, 66, 71, 21], [97, 128, 130, 88, 128, 27, 74, 50], [114, 111, 47, 113], [119, 121, 100, 64, 120, 120, 97, 109], [47, 87, 99, 136], [50, 56, 125, 31], [83, 16, 42, 89]], ![[86, 39, 67, 108, 24, 105, 71, 16], [57, 114, 1, 44, 1, 96, 36, 25], [126, 33, 81, 1], [137, 34, 98, 62, 9, 22, 103, 112], [22, 125, 136, 6], [17, 56, 35, 80], [96, 38, 99, 5]], ![[131, 133, 122, 18, 68, 77, 87, 62], [37, 48, 75, 65, 19, 81, 12, 134], [31, 15, 8, 100], [110, 60, 30, 63, 12, 116, 120, 3], [4, 21, 85, 78], [102, 76, 103, 24], [133, 122, 42, 89]]]
 h' := ![![[81, 118, 133, 129, 68], [130, 65, 48, 103, 9], [48, 29, 18, 69, 75], [127, 102, 36, 54, 100], [35, 72, 95, 7, 35], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[68, 124, 80, 113, 111], [96, 112, 53, 48, 43], [66, 128, 48, 47, 72], [79, 23, 52, 60, 13], [100, 12, 23, 76, 100], [14, 100, 119, 69, 29], [13, 106, 70, 119, 66], [81, 118, 133, 129, 68]], ![[5, 42, 111, 62, 127], [130, 5, 82, 53, 112], [67, 126, 119, 127, 81], [1, 40, 66, 30, 35], [4, 87, 65, 38, 122], [58, 17, 106, 120, 85], [107, 83, 18, 60, 46], [68, 124, 80, 113, 111]], ![[80, 132, 93, 113, 111], [78, 107, 90, 44, 36], [3, 116, 84, 117, 45], [62, 48, 7, 132, 1], [89, 24, 114, 49, 68], [73, 129, 100, 72, 80], [44, 5, 2, 24, 48], [5, 42, 111, 62, 127]], ![[0, 1], [82, 128, 5, 30, 78], [96, 18, 9, 57, 5], [10, 65, 117, 2, 129], [117, 83, 120, 108, 92], [20, 32, 92, 17, 83], [83, 84, 48, 75, 118], [80, 132, 93, 113, 111]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80, 9, 69, 42], [], [], []]
 b := ![[], [76, 9, 64, 72, 28], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 5
  hpos := by decide
  P := [36, 6, 2, 80, 44, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![66403793727192, 23521984221730, 17328326752082, 23671468077249, 31958940743973]
  a := ![16, 10, 23, 2, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![477725134728, 169222908070, 124664221238, 170298331491, 229920437007]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![231, -64, -2, 36, -58]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![231, -64, -2, 36, -58]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![74, 0, 1, 0, 0], ![124, 74, 0, 1, 0], ![73, 83, 0, 0, 1]] where
  M :=![![![231, -64, -2, 36, -58], ![-392, 211, 46, -28, 216], ![1672, -250, 81, 326, -168], ![196, 570, 258, 233, 668], ![88, 156, 78, 70, 189]]]
  hmulB := by decide  
  f := ![![![947, 172, -94, -44, 166]], ![![1240, 1163, 134, -160, -264]], ![![454, 90, -43, -22, 76]], ![![1384, 716, -10, -115, 4]], ![![1159, 725, 26, -110, -61]]]
  g := ![![![1, 14, -2, 36, -58], ![-108, -105, 46, -28, 216], ![-218, -70, 81, 326, -168], ![-648, -484, 258, 233, 668], ![-189, -139, 78, 70, 189]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [97, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 148], [0, 1]]
 g := ![![[127, 120], [95], [75, 25], [82], [27, 110], [69], [1]], ![[76, 29], [95], [83, 124], [82], [92, 39], [69], [1]]]
 h' := ![![[48, 148], [103, 92], [26, 86], [38, 144], [63, 126], [34, 109], [52, 48], [0, 1]], ![[0, 1], [49, 57], [131, 63], [96, 5], [2, 23], [51, 40], [121, 101], [48, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135]]
 b := ![[], [19, 142]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [97, 101, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20389, 46327, 39608, 10423, 76628]
  a := ![24, 18, 37, -5, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-65751, -47551, 39608, 10423, 76628]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19321, 6713, 835, -2634, 6516]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-19321, 6713, 835, -2634, 6516]] 
 ![![149, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![143, 0, 0, 1, 0], ![93, 0, 0, 0, 1]] where
  M :=![![![-19321, 6713, 835, -2634, 6516], ![46860, -16274, -2024, 6387, -15804], ![-113658, 39467, 4911, -15489, 38322], ![69600, -24181, -3008, 9488, -23472], ![15726, -5458, -680, 2142, -5299]]]
  hmulB := by decide  
  f := ![![![-39443, 11975, 8047, -10056, 18522]], ![![-3376, 1024, 688, -861, 1584]], ![![-13920, 4225, 2839, -3549, 6534]], ![![-35477, 10764, 7233, -9046, 16650]], ![![-24969, 7579, 5093, -6366, 11723]]]
  g := ![![![-2625, 6713, 835, -2634, 6516], ![6367, -16274, -2024, 6387, -15804], ![-15439, 39467, 4911, -15489, 38322], ![9456, -24181, -3008, 9488, -23472], ![2135, -5458, -680, 2142, -5299]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![521, -139, -88, 133, -212]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![521, -139, -88, 133, -212]] 
 ![![149, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![120, 0, 1, 0, 0], ![141, 0, 0, 1, 0], ![95, 0, 0, 0, 1]] where
  M :=![![![521, -139, -88, 133, -212], ![-1430, 530, 348, -343, 798], ![5698, -1323, -847, 1499, -2058], ![-3066, 1731, 1174, -648, 2578], ![948, -54, -32, 280, -111]]]
  hmulB := by decide  
  f := ![![![-42639, -20775, 662, 3417, -832]], ![![-7153, -3759, 36, 604, -2]], ![![-33178, -16487, 427, 2695, -486]], ![![-39509, -19204, 626, 3161, -794]], ![![-27845, -13225, 526, 2193, -715]]]
  g := ![![![107, -139, -88, 133, -212], ![-563, 530, 348, -343, 798], ![836, -1323, -847, 1499, -2058], ![-2287, 1731, 1174, -648, 2578], ![-153, -54, -32, 280, -111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2

def I149N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5223, 1575, 1058, -1333, 2436]] i)))

def SI149N3: IdealEqSpanCertificate' Table ![![-5223, 1575, 1058, -1333, 2436]] 
 ![![149, 0, 0, 0, 0], ![108, 1, 0, 0, 0], ![107, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![98, 0, 0, 0, 1]] where
  M :=![![![-5223, 1575, 1058, -1333, 2436], ![16822, -5178, -3482, 4277, -7998], ![-55430, 16583, 11135, -14167, 25662], ![46118, -14555, -9800, 11670, -22446], ![-7072, 1996, 1336, -1826, 3101]]]
  hmulB := by decide  
  f := ![![![5657, -3541, -580, 1007, -1488]], ![![4034, -2528, -420, 715, -1038]], ![![4357, -2584, -423, 750, -1158]], ![![1526, -967, -158, 274, -402]], ![![3638, -2344, -380, 662, -967]]]
  g := ![![![-3145, 1575, 1058, -1333, 2436], ![10364, -5178, -3482, 4277, -7998], ![-33083, 16583, 11135, -14167, 25662], ![29214, -14555, -9800, 11670, -22446], ![-3954, 1996, 1336, -1826, 3101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N3 : Nat.card (O ⧸ I149N3) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N3)

lemma isPrimeI149N3 : Ideal.IsPrime I149N3 := prime_ideal_of_norm_prime hp149.out _ NI149N3
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![231, -64, -2, 36, -58]] ![![-19321, 6713, 835, -2634, 6516]]
  ![![-5641383, 1959353, 243751, -768912, 1902358]] where
 M := ![![![-5641383, 1959353, 243751, -768912, 1902358]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![-5641383, 1959353, 243751, -768912, 1902358]] ![![521, -139, -88, 133, -212]]
  ![![-191222559, 66412750, 8261307, -26064053, 64480458]] where
 M := ![![![-191222559, 66412750, 8261307, -26064053, 64480458]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N2 : IdealMulLeCertificate' Table 
  ![![-191222559, 66412750, 8261307, -26064053, 64480458]] ![![-5223, 1575, 1058, -1333, 2436]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![-1336083, 1789639, 601811, 251810, 1965906]]]
 hmul := by decide  
 g := ![![![![-8967, 12011, 4039, 1690, 13194]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2, I149N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
    exact isPrimeI149N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1 ⊙ MulI149N2)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![515, -290, -162, 16, 304]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![515, -290, -162, 16, 304]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![83, 109, 135, 1, 0], ![122, 40, 47, 0, 1]] where
  M :=![![![515, -290, -162, 16, 304], ![2464, 997, -80, -166, 96], ![436, 2474, 579, -310, -996], ![-1896, 674, 488, -15, -920], ![-1716, -1972, -280, 268, 519]]]
  hmulB := by decide  
  f := ![![![-459, 118, 78, -120, 184]], ![![1232, -473, -320, 298, -720]], ![![-5164, 1130, 741, -1382, 1788]], ![![-3963, 723, 467, -1083, 1164]], ![![-1658, 322, 209, -450, 515]]]
  g := ![![![-251, -94, -110, 16, 304], ![30, 101, 118, -166, 96], ![978, 504, 591, -310, -996], ![739, 259, 303, -15, -920], ![-578, -344, -403, 268, 519]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [54, 105, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 12, 92], [12, 138, 59], [0, 1]]
 g := ![![[132, 136, 38], [131, 36, 36], [22, 141, 50], [83, 16], [122, 23, 2], [132, 1], []], ![[12, 118, 141, 135], [150, 56, 55, 141], [48, 95, 112, 3], [83, 116], [9, 1, 4, 3], [93, 18], [93, 8]], ![[25, 92, 72, 69], [22, 132, 110, 40], [88, 121, 108, 116], [109, 137], [137, 15, 131, 32], [128, 144], [126, 8]]]
 h' := ![![[120, 12, 92], [23, 103, 76], [20, 60, 6], [13, 103, 72], [56, 46, 147], [120, 129, 105], [0, 0, 1], [0, 1]], ![[12, 138, 59], [9, 69, 32], [68, 4, 6], [86, 43, 84], [76, 73, 56], [66, 41, 84], [16, 82, 138], [120, 12, 92]], ![[0, 1], [43, 130, 43], [40, 87, 139], [97, 5, 146], [68, 32, 99], [139, 132, 113], [135, 69, 12], [12, 138, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 127], []]
 b := ![[], [31, 121, 125], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [54, 105, 19, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11264079, 4916707, 3622739, 4151176, 6790031]
  a := ![11, 7, 14, 1, 29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7693161, -4762667, -5800778, 4151176, 6790031]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![459, -118, -78, 120, -184]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![459, -118, -78, 120, -184]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![54, 47, 1, 0, 0], ![78, 52, 0, 1, 0], ![46, 77, 0, 0, 1]] where
  M :=![![![459, -118, -78, 120, -184], ![-1232, 473, 320, -298, 720], ![5164, -1130, -741, 1382, -1788], ![-2536, 1614, 1112, -515, 2408], ![932, -36, -16, 276, -81]]]
  hmulB := by decide  
  f := ![![![-515, 290, 162, -16, -304]], ![![-2464, -997, 80, 166, -96]], ![![-954, -223, 79, 48, -132]], ![![-1102, -198, 108, 49, -184]], ![![-1402, -407, 92, 78, -145]]]
  g := ![![![25, 76, -78, 120, -184], ![-188, -361, 320, -298, 720], ![130, 659, -741, 1382, -1788], ![-882, -1386, 1112, -515, 2408], ![-106, -49, -16, 276, -81]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [20, 120, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 150], [0, 1]]
 g := ![![[6, 68], [33, 72], [5, 127], [97], [46, 144], [55], [1]], ![[0, 83], [0, 79], [16, 24], [97], [131, 7], [55], [1]]]
 h' := ![![[31, 150], [95, 70], [51, 125], [68, 91], [137, 61], [55, 12], [131, 31], [0, 1]], ![[0, 1], [0, 81], [0, 26], [20, 60], [65, 90], [125, 139], [35, 120], [31, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127]]
 b := ![[], [35, 139]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [20, 120, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-43926, 51723, 41613, -22178, 73799]
  a := ![10, 24, 24, -50, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26198, -42605, 41613, -22178, 73799]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![515, -290, -162, 16, 304]] ![![459, -118, -78, 120, -184]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB696I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB696I3 : PrimesBelowBoundCertificateInterval O 103 151 696 where
  m := 9
  g := ![4, 2, 2, 3, 1, 2, 1, 4, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB696I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2, I107N3]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0]
    · exact ![I137N0, I137N1]
    · exact ![I139N0]
    · exact ![I149N0, I149N1, I149N2, I149N3]
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
    · exact ![11449, 107, 107, 107]
    · exact ![141158161, 109]
    · exact ![163047361, 113]
    · exact ![16129, 16129, 127]
    · exact ![38579489651]
    · exact ![2571353, 18769]
    · exact ![51888844699]
    · exact ![22201, 149, 149, 149]
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
      exact NI107N3
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
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
      exact NI137N1
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
      exact NI149N3
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I107N1, I107N2, I107N3, I109N1, I113N1, I127N2, I149N1, I149N2, I149N3]
  Il := ![[I107N1, I107N2, I107N3], [I109N1], [I113N1], [I127N2], [], [], [], [I149N1, I149N2, I149N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
