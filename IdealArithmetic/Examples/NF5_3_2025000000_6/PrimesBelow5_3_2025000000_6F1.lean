
import IdealArithmetic.Examples.NF5_3_2025000000_6.RI5_3_2025000000_6
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [18, 7, 7, 17, 7, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 22, 19, 16, 24], [17, 19, 26, 28, 6], [28, 20, 8, 26, 24], [28, 25, 5, 17, 4], [0, 1]]
 g := ![![[27, 20, 20, 17, 5], [19, 17, 19, 16], [3, 22, 1], []], ![[5, 2, 12, 12, 19, 17, 0, 28], [7, 2, 7, 6], [10, 10, 2, 14, 0, 4, 18, 20], [4, 15, 12, 0, 14, 4, 16, 20]], ![[5, 15, 22, 0, 7, 6], [19, 15, 14, 22], [26, 27, 21, 20, 10, 18, 6, 9], [4, 17, 6, 21, 27, 25, 4, 13]], ![[7, 17, 12, 21, 3, 2, 26, 20], [8, 19, 11, 24], [11, 26, 25, 20, 15, 3, 23, 28], [15, 17, 1, 1, 25, 12, 12, 20]], ![[14, 21, 6, 12, 18, 10, 5, 13], [27, 10, 27, 5], [8, 2, 14, 17, 18, 27, 4, 5], [26, 8, 24, 12, 10, 15, 20, 6]]]
 h' := ![![[7, 22, 19, 16, 24], [22, 24, 13, 5, 11], [4, 18, 10, 20, 4], [0, 0, 0, 1], [0, 1]], ![[17, 19, 26, 28, 6], [23, 27, 22, 6, 8], [27, 1, 20, 23, 8], [10, 7, 22, 23, 24], [7, 22, 19, 16, 24]], ![[28, 20, 8, 26, 24], [13, 2, 20, 28], [6, 12, 16, 23, 15], [27, 15, 11, 6, 4], [17, 19, 26, 28, 6]], ![[28, 25, 5, 17, 4], [7, 18, 16, 12, 5], [21, 3, 8, 8, 13], [19, 26, 3, 20, 21], [28, 20, 8, 26, 24]], ![[0, 1], [3, 16, 16, 7, 5], [5, 24, 4, 13, 18], [24, 10, 22, 8, 9], [28, 25, 5, 17, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 8, 17, 9], [], [], []]
 b := ![[], [28, 5, 0, 9, 25], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [18, 7, 7, 17, 7, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![34242284531766462, -10588548796205811, 2704384352822115, 9579767710643136, -40428910274436825]
  a := ![220, -541, 57, 274, -1115]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1180768432129878, -365122372282959, 93254632855935, 330336817608384, -1394100354290925]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 20511149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1389, -345, 90, 311, -1318]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![1389, -345, 90, 311, -1318]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![14, 1, 3, 1, 0], ![9, 10, 12, 0, 1]] where
  M :=![![![1389, -345, 90, 311, -1318], ![6900, -1289, 410, 1466, -6274], ![34116, -8966, 2637, 8548, -36304], ![191680, -43628, 12254, 42565, -181032], ![48122, -11135, 3120, 10779, -45827]]]
  hmulB := by decide  
  f := ![![![-3449, 525, -230, -675, 2876]], ![![-15376, 3179, -1206, -3632, 15310]], ![![-78444, 11542, -5145, -15056, 64228]], ![![-20774, 3829, -1529, -4561, 19302]], ![![-39113, 6222, -2666, -7854, 33411]]]
  g := ![![![287, 404, 483, 311, -1318], ![1382, 1935, 2300, 1466, -6274], ![7780, 11146, 13311, 8548, -36304], ![39518, 55617, 66353, 42565, -181032], ![9989, 14076, 16797, 10779, -45827]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [20, 23, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 3, 3], [25, 27, 28], [0, 1]]
 g := ![![[27, 3, 16], [19, 22, 16], [30, 29, 20], [1]], ![[16, 10, 18, 21], [11, 23, 23, 21], [24, 4, 22, 23], [22, 1, 2, 27]], ![[5, 8, 4, 1], [12, 9, 22, 16], [0, 26, 23, 2], [5, 29, 2, 4]]]
 h' := ![![[18, 3, 3], [23, 19, 4], [20, 29, 27], [11, 8, 12], [0, 1]], ![[25, 27, 28], [13, 19, 10], [26, 1, 10], [29, 3, 7], [18, 3, 3]], ![[0, 1], [2, 24, 17], [1, 1, 25], [25, 20, 12], [25, 27, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 6], []]
 b := ![[], [2, 13, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [20, 23, 19, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10286906899, 8248965882, -1709892022, -6316211882, 25974062597]
  a := ![-351, 800, -91, -439, 1779]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5020209804, -7908885426, -9498387340, -6316211882, 25974062597]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3449, -525, 230, 675, -2876]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![3449, -525, 230, 675, -2876]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![4, 28, 1, 0, 0], ![12, 26, 0, 1, 0], ![19, 23, 0, 0, 1]] where
  M :=![![![3449, -525, 230, 675, -2876], ![15376, -3179, 1206, 3632, -15310], ![78444, -11542, 5145, 15056, -64228], ![345000, -73544, 27538, 83141, -350104], ![86374, -17863, 6776, 20407, -86021]]]
  hmulB := by decide  
  f := ![![![-1389, 345, -90, -311, 1318]], ![![-6900, 1289, -410, -1466, 6274]], ![![-7512, 1498, -467, -1640, 7008]], ![![-12508, 2622, -774, -2723, 11612]], ![![-7523, 1527, -460, -1626, 6941]]]
  g := ![![![1583, 1343, 230, 675, -2876], ![8318, 7121, 1206, 3632, -15310], ![35404, 30006, 5145, 15056, -64228], ![189972, 162778, 27538, 83141, -350104], ![46735, 40010, 6776, 20407, -86021]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [28, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 30], [0, 1]]
 g := ![![[25, 10], [22, 20], [30, 10], [13, 1]], ![[0, 21], [3, 11], [5, 21], [26, 30]]]
 h' := ![![[13, 30], [4, 14], [28, 19], [8, 17], [0, 1]], ![[0, 1], [0, 17], [27, 12], [12, 14], [13, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [16, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [28, 18, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27877, 8808, -1511, -6856, 29376]
  a := ![15, -39, 4, 18, -76]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16055, -14396, -1511, -6856, 29376]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![1389, -345, 90, 311, -1318]] ![![3449, -525, 230, 675, -2876]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1729, 308, -122, -366, 1550]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-1729, 308, -122, -366, 1550]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![2, 16, 11, 1, 0], ![18, 13, 23, 0, 1]] where
  M :=![![![-1729, 308, -122, -366, 1550], ![-8092, 1365, -574, -1712, 7264], ![-38208, 7108, -2843, -8382, 35488], ![-185072, 32144, -13034, -38999, 165308], ![-45980, 8036, -3248, -9712, 41161]]]
  hmulB := by decide  
  f := ![![![-27517, 6356, -1862, -6330, 26942]], ![![-143452, 33129, -9706, -32996, 140440]], ![![-747792, 172732, -50603, -172026, 732184]], ![![-391202, 90356, -26471, -89989, 383016]], ![![-555162, 128233, -37567, -127710, 543565]]]
  g := ![![![-781, -378, -858, -366, 1550], ![-3660, -1775, -4022, -1712, 7264], ![-17844, -8652, -19645, -8382, 35488], ![-83314, -40348, -91517, -38999, 165308], ![-20742, -10045, -22787, -9712, 41161]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [31, 4, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 27, 14], [16, 9, 23], [0, 1]]
 g := ![![[23, 9, 11], [3, 11], [31, 34, 25], [6, 1], []], ![[32, 35, 26, 17], [9, 4], [30, 15, 7, 14], [36, 7], [8, 11]], ![[24, 5, 9, 15], [12, 34], [33, 20, 6, 14], [26, 26], [36, 11]]]
 h' := ![![[27, 27, 14], [19, 31, 14], [1, 7, 14], [36, 19, 32], [0, 0, 1], [0, 1]], ![[16, 9, 23], [5, 6, 5], [5, 24, 2], [31, 9, 36], [0, 12, 9], [27, 27, 14]], ![[0, 1], [19, 0, 18], [24, 6, 21], [15, 9, 6], [28, 25, 27], [16, 9, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 17], []]
 b := ![[], [36, 10, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [31, 4, 31, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21713105243, 11377010126, -2430508430, -8974077642, 37376156156]
  a := ![-381, 955, -99, -477, 1931]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18284750291, -8943993990, -20631547188, -8974077642, 37376156156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-375, 83, -29, -94, 402]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-375, 83, -29, -94, 402]] 
 ![![37, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-375, 83, -29, -94, 402], ![-2180, 627, -167, -543, 2296], ![-11912, 2220, -660, -2429, 10382], ![-56180, 13670, -4205, -13784, 58686], ![-14190, 3371, -1044, -3443, 14667]]]
  hmulB := by decide  
  f := ![![![-36191, -24757, 4109, 15402, -59668]], ![![-2528, -1887, 321, 1193, -4636]], ![![-36606, -24966, 4140, 15523, -60130]], ![![114063, 74071, -12098, -45604, 176314]], ![![19061, 12152, -1973, -7453, 28793]]]
  g := ![![![-61, 83, -29, -94, 402], ![-377, 627, -167, -543, 2296], ![-1675, 2220, -660, -2429, 10382], ![-9236, 13670, -4205, -13784, 58686], ![-2306, 3371, -1044, -3443, 14667]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4161, -738, 300, 892, -3780]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![4161, -738, 300, 892, -3780]] 
 ![![37, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![4161, -738, 300, 892, -3780], ![19784, -3507, 1426, 4240, -17968], ![94048, -16680, 6781, 20162, -85440], ![447184, -79280, 32234, 95841, -406148], ![111148, -19706, 8012, 23822, -100951]]]
  hmulB := by decide  
  f := ![![![293, -38, 8, 44, -188]], ![![170, -23, 6, 28, -120]], ![![233, -70, 17, 58, -244]], ![![1175, -154, 46, 193, -832]], ![![298, -42, 12, 50, -215]]]
  g := ![![![457, -738, 300, 892, -3780], ![2172, -3507, 1426, 4240, -17968], ![10329, -16680, 6781, 20162, -85440], ![49099, -79280, 32234, 95841, -406148], ![12204, -19706, 8012, 23822, -100951]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-1729, 308, -122, -366, 1550]] ![![-375, 83, -29, -94, 402]]
  ![![-2421, 599, 55, -86, 280]] where
 M := ![![![-2421, 599, 55, -86, 280]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-2421, 599, 55, -86, 280]] ![![4161, -738, 300, 892, -3780]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-386909, 69005, -27935, -83028, 351796]]]
 hmul := by decide  
 g := ![![![![-10457, 1865, -755, -2244, 9508]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [2, 1, 1, 31, 26, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 31, 11, 40, 12], [25, 17, 34, 10, 32], [3, 2, 30, 18, 24], [24, 31, 7, 14, 14], [0, 1]]
 g := ![![[39, 7, 4, 1, 20], [37, 3, 24, 10], [4, 4, 26, 20], [1], []], ![[13, 26, 24, 5, 26, 30, 26, 6], [29, 9], [28, 16, 26, 9], [3, 22, 26, 40, 20, 33, 23, 17], [33, 2, 4, 21]], ![[14, 39, 24, 12, 18, 13, 37, 21], [4, 36, 27, 32], [17, 19, 13, 31], [13, 16, 24, 22, 26, 19, 39, 21], [20, 38, 10, 40]], ![[15, 7, 11, 33, 21, 25, 40, 12], [34, 37, 11, 33], [14, 25, 6, 32], [3, 18, 36, 22, 34, 3, 17, 28], [19, 24, 33, 2]], ![[35, 26, 29, 25, 23, 7, 19, 38], [7, 3, 39, 31], [2, 10, 30, 2], [32, 32, 30, 29, 34, 33, 21, 27], [29, 16, 11, 32]]]
 h' := ![![[4, 31, 11, 40, 12], [24, 21, 6, 25, 26], [37, 33, 27, 14, 16], [39, 40, 40, 10, 15], [0, 0, 1], [0, 1]], ![[25, 17, 34, 10, 32], [33, 31, 32, 39, 12], [3, 13, 4, 38], [31, 23, 3, 16, 3], [32, 6, 22, 13, 30], [4, 31, 11, 40, 12]], ![[3, 2, 30, 18, 24], [37, 30, 30, 25, 5], [2, 6, 22, 3, 27], [6, 29, 36, 1, 20], [11, 16, 25, 6, 36], [25, 17, 34, 10, 32]], ![[24, 31, 7, 14, 14], [10, 25, 15, 28, 12], [23, 2, 29, 11, 19], [16, 20, 31, 14, 27], [12, 27, 34, 29, 7], [3, 2, 30, 18, 24]], ![[0, 1], [26, 16, 40, 6, 27], [32, 28, 0, 16, 20], [6, 11, 13, 0, 17], [26, 33, 0, 34, 9], [24, 31, 7, 14, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 34, 5, 24], [], [], []]
 b := ![[], [19, 19, 24, 26, 39], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [2, 1, 1, 31, 26, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![569347046117463248, -325705003672107090, 74277780406211956, 265791867655776626, -1099395010730305602]
  a := ![469, -1152, 123, 588, -2377]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13886513319938128, -7944024479807490, 1811653180639316, 6482728479409186, -26814512456836722]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 115856201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3755, 602, -256, -756, 3216]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-3755, 602, -256, -756, 3216]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![35, 0, 38, 41, 1]] where
  M :=![![![-3755, 602, -256, -756, 3216], ![-17088, 3397, -1306, -3928, 16584], ![-85520, 13416, -5763, -16994, 72352], ![-385680, 78432, -29834, -89927, 379396], ![-96372, 19178, -7364, -22158, 93553]]]
  hmulB := by decide  
  f := ![![![-65, -46, 12, 20, -80]], ![![320, 15, -26, -28, 120]], ![![-656, 632, -61, -186, 712]], ![![-2144, -3096, 638, 1175, -4636]], ![![-2693, -2448, 568, 979, -3883]]]
  g := ![![![-2705, 14, -2848, -3084, 3216], ![-13896, 79, -14686, -15904, 16584], ![-60880, 312, -64073, -69382, 72352], ![-317780, 1824, -335974, -363841, 379396], ![-78389, 446, -82846, -89717, 93553]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [12, 25, 33, 9, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 10, 29, 15], [37, 23, 2, 20], [14, 9, 12, 8], [0, 1]]
 g := ![![[5, 0, 36, 13], [40, 31, 35, 14], [30, 1, 25], [34, 1], []], ![[0, 17, 31, 33, 0, 13], [15, 40, 18, 11, 22, 6], [21, 0, 4], [22, 11, 4, 9, 28, 38], [26, 6, 10]], ![[15, 18, 27, 29, 14, 27], [17, 12, 19, 34, 35, 39], [8, 16, 10], [2, 7, 3, 33, 23, 19], [11, 6, 13]], ![[3, 8, 33, 12, 32, 34], [35, 21, 1, 7, 42, 34], [25, 19, 15], [5, 6, 14, 0, 2, 30], [41, 3, 21]]]
 h' := ![![[26, 10, 29, 15], [36, 29, 8, 23], [38, 10, 36, 10], [22, 41, 14, 5], [0, 0, 1], [0, 1]], ![[37, 23, 2, 20], [20, 39, 18, 27], [21, 36, 14, 40], [31, 25, 34, 41], [20, 13, 7, 33], [26, 10, 29, 15]], ![[14, 9, 12, 8], [5, 39, 12, 5], [1, 5, 19, 24], [21, 33, 28, 28], [33, 22, 8, 4], [37, 23, 2, 20]], ![[0, 1], [8, 22, 5, 31], [36, 35, 17, 12], [32, 30, 10, 12], [5, 8, 27, 6], [14, 9, 12, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [32, 31, 30], []]
 b := ![[], [], [28, 40, 41, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [12, 25, 33, 9, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28910402284284, 19160281317488, -3216503186116, -12027926001364, 46622889829766]
  a := ![-264, 648, -68, -340, 1338]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-37276528878082, 445587937616, -41276425970168, -44734102535390, 46622889829766]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65, 46, -12, -20, 80]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![65, 46, -12, -20, 80]] 
 ![![43, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![65, 46, -12, -20, 80], ![-320, -15, 26, 28, -120], ![656, -632, 61, 186, -712], ![2144, 3096, -638, -1175, 4636], ![692, 734, -164, -290, 1149]]]
  hmulB := by decide  
  f := ![![![3755, -602, 256, 756, -3216]], ![![1096, -191, 78, 232, -984]], ![![3910, -620, 265, 782, -3328]], ![![12375, -2370, 926, 2777, -11740]], ![![4599, -824, 332, 990, -4195]]]
  g := ![![![-33, 46, -12, -20, 80], ![32, -15, 26, 28, -120], ![380, -632, 61, 186, -712], ![-2045, 3096, -638, -1175, 4636], ![-495, 734, -164, -290, 1149]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-3755, 602, -256, -756, 3216]] ![![65, 46, -12, -20, 80]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![34285, -7876, 2324, 7874, -33510]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![34285, -7876, 2324, 7874, -33510]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![22, 20, 21, 25, 1]] where
  M :=![![![34285, -7876, 2324, 7874, -33510], ![178348, -40961, 12082, 40954, -174296], ![927744, -213276, 62873, 213134, -907076], ![4828184, -1110340, 327098, 1109185, -4720596], ![1215380, -279524, 82340, 279220, -1188337]]]
  hmulB := by decide  
  f := ![![![-1453, -972, 160, 602, -2330]], ![![7604, 5089, -838, -3150, 12192]], ![![-39792, -26620, 4387, 16478, -63780]], ![![208216, 139116, -22934, -86133, 333388]], ![![96442, 64424, -10621, -39889, 154395]]]
  g := ![![![16415, 14092, 15022, 17992, -33510], ![85380, 73297, 78134, 93582, -174296], ![444328, 381452, 406627, 487022, -907076], ![2312368, 1985140, 2116162, 2534555, -4720596], ![582102, 499728, 532711, 638035, -1188337]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [43, 14, 32, 37, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 17, 22, 3], [14, 8, 33, 46], [21, 21, 39, 45], [0, 1]]
 g := ![![[29, 30, 46, 18], [43, 42, 44, 14], [17, 17, 17, 18], [10, 1], []], ![[28, 29, 36, 6, 17, 32], [23, 7, 39, 44, 11, 37], [34, 24, 34, 23, 46, 1], [7, 12, 1, 26, 35, 21], [27, 34, 9]], ![[32, 25, 0, 44, 2, 26], [1, 36, 44, 18, 42, 33], [32, 41, 21, 17, 43, 23], [28, 6, 21, 40, 0, 13], [11, 38, 1]], ![[23, 13, 9, 46, 8, 30], [28, 43, 45, 12, 7, 38], [44, 28, 38, 15, 4, 44], [29, 27, 35, 15, 22, 11], [8, 25, 4]]]
 h' := ![![[22, 17, 22, 3], [31, 7, 39, 26], [21, 20, 15, 25], [40, 5, 42, 21], [0, 0, 1], [0, 1]], ![[14, 8, 33, 46], [38, 10, 3, 18], [6, 38, 11, 13], [27, 8, 26, 4], [28, 36, 0, 30], [22, 17, 22, 3]], ![[21, 21, 39, 45], [41, 44, 7, 31], [37, 27, 32, 22], [39, 33, 19, 27], [5, 34, 14, 38], [14, 8, 33, 46]], ![[0, 1], [26, 33, 45, 19], [5, 9, 36, 34], [23, 1, 7, 42], [3, 24, 32, 26], [21, 21, 39, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [42, 16, 12], []]
 b := ![[], [], [2, 22, 10, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [43, 14, 32, 37, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1287335263465439, 403417116839536, -98868933420086, -358371111503816, 1514400557106270]
  a := ![-641, 1583, -166, -797, 3249]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-736258457868157, -635842426069912, -678750651758548, -813157128492778, 1514400557106270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1453, -972, 160, 602, -2330]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-1453, -972, 160, 602, -2330]] 
 ![![47, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![-1453, -972, 160, 602, -2330], ![7604, 5089, -838, -3150, 12192], ![-39792, -26620, 4387, 16478, -63780], ![208216, 139116, -22934, -86133, 333388], ![42892, 28652, -4724, -17740, 68665]]]
  hmulB := by decide  
  f := ![![![34285, -7876, 2324, 7874, -33510]], ![![18384, -4223, 1246, 4222, -17968]], ![![36517, -8392, 2475, 8388, -35698]], ![![110022, -25300, 7454, 25275, -107568]], ![![52120, -11980, 3532, 11972, -50951]]]
  g := ![![![1961, -972, 160, 602, -2330], ![-10262, 5089, -838, -3150, 12192], ![53681, -26620, 4387, 16478, -63780], ![-280580, 139116, -22934, -86133, 333388], ![-57788, 28652, -4724, -17740, 68665]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![34285, -7876, 2324, 7874, -33510]] ![![-1453, -972, 160, 602, -2330]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-89183, 15808, -6428, -19112, 80992]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-89183, 15808, -6428, -19112, 80992]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![39, 36, 1, 0, 0], ![27, 15, 0, 1, 0], ![44, 10, 0, 0, 1]] where
  M :=![![![-89183, 15808, -6428, -19112, 80992], ![-423936, 75201, -30568, -90892, 385168], ![-2015872, 357296, -145291, -431984, 1830648], ![-9582256, 1699928, -690960, -2054547, 8706416], ![-2381744, 422496, -171736, -510648, 2163945]]]
  hmulB := by decide  
  f := ![![![-619, -1472, 284, 552, -2176]], ![![8000, 3285, -1112, -1684, 6832]], ![![4423, 1268, -527, -744, 3048]], ![![2283, -1289, 44, 289, -1056]], ![![988, -982, 88, 272, -1031]]]
  g := ![![![-54455, -5208, -6428, -19112, 80992], ![-258964, -24767, -30568, -90892, 385168], ![-1230839, -117716, -145291, -431984, 1830648], ![-5853667, -559839, -690960, -2054547, 8706416], ![-1454908, -139146, -171736, -510648, 2163945]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [40, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 52], [0, 1]]
 g := ![![[45, 4], [17], [2, 7], [24], [2, 1]], ![[0, 49], [17], [16, 46], [24], [4, 52]]]
 h' := ![![[2, 52], [49, 2], [26, 32], [34, 31], [26, 17], [0, 1]], ![[0, 1], [0, 51], [37, 21], [43, 22], [7, 36], [2, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [36, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [40, 51, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24230, 71365, -13358, -50783, 203872]
  a := ![-59, 141, -15, -75, 299]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-133095, -13674, -13358, -50783, 203872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![351, -62, 25, 75, -318]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![351, -62, 25, 75, -318]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![21, 52, 1, 0, 0], ![21, 20, 0, 1, 0], ![34, 48, 0, 0, 1]] where
  M :=![![![351, -62, 25, 75, -318], ![1668, -303, 121, 361, -1530], ![8012, -1446, 574, 1721, -7294], ![38196, -6834, 2735, 8202, -34774], ![9504, -1700, 680, 2040, -8649]]]
  hmulB := by decide  
  f := ![![![-45, -38, 7, 23, -90]], ![![316, 153, -27, -93, 358]], ![![271, 120, -21, -72, 276]], ![![239, 112, -18, -69, 264]], ![![286, 128, -22, -78, 299]]]
  g := ![![![171, 234, 25, 75, -318], ![822, 1125, 121, 361, -1530], ![3921, 5366, 574, 1721, -7294], ![18695, 25586, 2735, 8202, -34774], ![4650, 6364, 680, 2040, -8649]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [24, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 52], [0, 1]]
 g := ![![[25, 42], [42], [], [], [36, 1]], ![[0, 11], [42], [], [], [19, 52]]]
 h' := ![![[36, 52], [52, 28], [0, 28], [44], [37], [0, 1]], ![[0, 1], [0, 25], [1, 25], [44], [37], [36, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [26, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [24, 17, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5366572, 4962578, -941490, -3858334, 15934570]
  a := ![-527, 1296, -134, -662, 2671]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8421616, -11957974, -941490, -3858334, 15934570]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2069, 478, -140, -476, 2026]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-2069, 478, -140, -476, 2026]] 
 ![![53, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![-2069, 478, -140, -476, 2026], ![-10788, 2493, -730, -2482, 10564], ![-56248, 12992, -3805, -12938, 55068], ![-293224, 67748, -19842, -67461, 287132], ![-73832, 17058, -4996, -16986, 72297]]]
  hmulB := by decide  
  f := ![![![71, -62, 8, 36, -142]], ![![34, -15, 2, 10, -40]], ![![45, -90, 15, 54, -214]], ![![350, 80, -14, -41, 152]], ![![137, -36, 4, 22, -89]]]
  g := ![![![-1703, 478, -140, -476, 2026], ![-8880, 2493, -730, -2482, 10564], ![-46289, 12992, -3805, -12938, 55068], ![-241356, 67748, -19842, -67461, 287132], ![-60771, 17058, -4996, -16986, 72297]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-89183, 15808, -6428, -19112, 80992]] ![![351, -62, 25, 75, -318]]
  ![![-16690609, 2959418, -1203239, -3577569, 15160666]] where
 M := ![![![-16690609, 2959418, -1203239, -3577569, 15160666]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![-16690609, 2959418, -1203239, -3577569, 15160666]] ![![-2069, 478, -140, -476, 2026]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-26743747, 4732900, -1928723, -5729777, 24280360]]]
 hmul := by decide  
 g := ![![![![-504599, 89300, -36391, -108109, 458120]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1571, 37, -32, -203, 896]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-1571, 37, -32, -203, 896]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![2, 57, 40, 3, 1]] where
  M :=![![![-1571, 37, -32, -203, 896], ![-5432, 2069, -670, -1894, 8022], ![-41900, 10630, -2501, -8924, 37696], ![-194784, 28404, -10294, -38653, 166456], ![-49958, 7183, -2532, -9683, 41691]]]
  hmulB := by decide  
  f := ![![![-565, -293, 44, 171, -654]], ![![1956, 1709, -302, -1108, 4326]], ![![-14972, -8094, 1237, 4776, -18308]], ![![55720, 46320, -8094, -29807, 116216]], ![![-5260, -1328, 108, 552, -1933]]]
  g := ![![![-57, -865, -608, -49, 896], ![-364, -7715, -5450, -440, 8022], ![-1988, -36238, -25599, -2068, 37696], ![-8944, -160332, -113026, -9119, 166456], ![-2260, -40156, -28308, -2284, 41691]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [33, 11, 24, 33, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 43, 31, 31], [33, 51, 29, 5], [43, 23, 58, 23], [0, 1]]
 g := ![![[48, 47, 5, 5], [44, 5, 18, 19], [28, 16, 25], [33, 3, 26, 1], []], ![[37, 16, 15, 5, 57, 13], [11, 47, 35, 8, 8, 11], [5, 55, 51], [45, 52, 11, 34, 17, 11], [54, 6, 19, 28, 2, 55]], ![[7, 45, 25, 29, 12, 35], [15, 50, 22, 8, 53, 12], [14, 9, 21], [9, 9, 25, 56, 39, 5], [28, 53, 36, 28, 56, 7]], ![[5, 26, 28, 3, 8, 39], [16, 31, 57, 4, 34, 37], [12, 40, 7], [50, 10, 58, 14, 51, 37], [1, 9, 58, 8, 49, 13]]]
 h' := ![![[9, 43, 31, 31], [23, 29, 41, 51], [41, 40, 42, 14], [32, 10, 28, 54], [0, 0, 0, 1], [0, 1]], ![[33, 51, 29, 5], [10, 36, 38, 44], [15, 52, 50, 26], [11, 23, 26, 13], [9, 40, 7, 26], [9, 43, 31, 31]], ![[43, 23, 58, 23], [42, 56, 3, 40], [26, 28, 5, 47], [4, 23, 46, 32], [26, 9, 47, 1], [33, 51, 29, 5]], ![[0, 1], [35, 56, 36, 42], [36, 57, 21, 31], [45, 3, 18, 19], [1, 10, 5, 31], [43, 23, 58, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [58, 23, 12], []]
 b := ![[], [], [35, 28, 8, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [33, 11, 24, 33, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24941996114346, 12457919819793, -2813834827447, -10266022138923, 42663936961895]
  a := ![-293, 721, -77, -367, 1485]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1868980848104, -41006550627258, -28972395140733, -2343353102112, 42663936961895]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![565, 293, -44, -171, 654]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![565, 293, -44, -171, 654]] 
 ![![59, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![565, 293, -44, -171, 654], ![-1956, -1709, 302, 1108, -4326], ![14972, 8094, -1237, -4776, 18308], ![-55720, -46320, 8094, 29807, -116216], ![-11018, -9621, 1700, 6237, -24351]]]
  hmulB := by decide  
  f := ![![![1571, -37, 32, 203, -896]], ![![811, -52, 26, 125, -546]], ![![1722, -204, 63, 282, -1216]], ![![4260, -504, 194, 779, -3368]], ![![900, -123, 44, 171, -737]]]
  g := ![![![-14, 293, -44, -171, 654], ![25, -1709, 302, 1108, -4326], ![-360, 8094, -1237, -4776, 18308], ![792, -46320, 8094, 29807, -116216], ![141, -9621, 1700, 6237, -24351]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-1571, 37, -32, -203, 896]] ![![565, 293, -44, -171, 654]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15395, -3559, 1043, 3544, -15084]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![15395, -3559, 1043, 3544, -15084]] 
 ![![61, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![15395, -3559, 1043, 3544, -15084], ![80312, -18553, 5433, 18471, -78616], ![418568, -96600, 28310, 96255, -409694], ![2181604, -504134, 147699, 501998, -2136610], ![549298, -126927, 37188, 126395, -537965]]]
  hmulB := by decide  
  f := ![![![-441525, -295087, 48633, 182744, -707330]], ![![23378, 15615, -2573, -9669, 37424]], ![![-610433, -407971, 67237, 252651, -977912]], ![![976828, 652618, -107545, -404128, 1564198]], ![![-184985, -123684, 20387, 76603, -296505]]]
  g := ![![![12530, -3559, 1043, 3544, -15084], ![65309, -18553, 5433, 18471, -78616], ![340348, -96600, 28310, 96255, -409694], ![1774895, -504134, 147699, 501998, -2136610], ![446891, -126927, 37188, 126395, -537965]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2011149, 464507, -136084, -462623, 1969042]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-2011149, 464507, -136084, -462623, 1969042]] 
 ![![61, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![-2011149, 464507, -136084, -462623, 1969042], ![-10484268, 2421509, -709416, -2411688, 10264762], ![-54655268, 12623510, -3698239, -12572310, 53510972], ![-284921992, 65807288, -19279192, -65540383, 278956660], ![-71740334, 16569577, -4854296, -16502373, 70238327]]]
  hmulB := by decide  
  f := ![![![25075, -4533, 1836, 5461, -23128]], ![![4035, -718, 292, 867, -3674]], ![![24128, -4358, 1761, 5246, -22216]], ![![45933, -7935, 3276, 9704, -41164]], ![![25076, -4449, 1816, 5393, -22855]]]
  g := ![![![-1065479, 464507, -136084, -462623, 1969042], ![-5554421, 2421509, -709416, -2411688, 10264762], ![-28955612, 12623510, -3698239, -12572310, 53510972], ![-150947751, 65807288, -19279192, -65540383, 278956660], ![-38007042, 16569577, -4854296, -16502373, 70238327]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8975, 2009, -737, -2234, 9392]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-8975, 2009, -737, -2234, 9392]] 
 ![![61, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![-8975, 2009, -737, -2234, 9392], ![-47600, 6257, -2961, -8581, 36756], ![-200528, 46972, -16916, -51463, 216034], ![-1088140, 133266, -65583, -188904, 811242], ![-267454, 35133, -16632, -48197, 206453]]]
  hmulB := by decide  
  f := ![![![12345, 7185, -2067, -3346, 13470]], ![![3538, 2649, -691, -1169, 4684]], ![![2012, -1512, 98, 381, -1422]], ![![13982, 12716, -3113, -5434, 21710]], ![![9458, 6257, -1712, -2837, 11395]]]
  g := ![![![-5121, 2009, -737, -2234, 9392], ![-19752, 6257, -2961, -8581, 36756], ![-117930, 46972, -16916, -51463, 216034], ![-435076, 133266, -65583, -188904, 811242], ![-110942, 35133, -16632, -48197, 206453]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2

def I61N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7693, 1352, -552, -1640, 6952]] i)))

def SI61N3: IdealEqSpanCertificate' Table ![![-7693, 1352, -552, -1640, 6952]] 
 ![![61, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![-7693, 1352, -552, -1640, 6952], ![-36432, 6523, -2640, -7856, 33280], ![-173952, 30512, -12469, -37040, 157024], ![-823104, 147680, -59712, -177717, 752800], ![-204672, 36648, -14832, -44136, 186971]]]
  hmulB := by decide  
  f := ![![![14735, -3560, 1032, 3464, -14728]], ![![10701, -2565, 744, 2504, -10648]], ![![7532, -1744, 515, 1744, -7424]], ![![40953, -9656, 2808, 9499, -40408]], ![![19049, -4544, 1320, 4448, -18917]]]
  g := ![![![-5129, 1352, -552, -1640, 6952], ![-24577, 6523, -2640, -7856, 33280], ![-115836, 30512, -12469, -37040, 157024], ![-555997, 147680, -59712, -177717, 752800], ![-138077, 36648, -14832, -44136, 186971]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N3 : Nat.card (O ⧸ I61N3) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N3)

lemma isPrimeI61N3 : Ideal.IsPrime I61N3 := prime_ideal_of_norm_prime hp61.out _ NI61N3

def I61N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, -39, 15, 44, -186]] i)))

def SI61N4: IdealEqSpanCertificate' Table ![![197, -39, 15, 44, -186]] 
 ![![61, 0, 0, 0, 0], ![54, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![197, -39, 15, 44, -186], ![964, -157, 65, 197, -836], ![4400, -792, 328, 967, -4098], ![21452, -3922, 1555, 4604, -19498], ![5318, -979, 388, 1147, -4857]]]
  hmulB := by decide  
  f := ![![![-39355, 9089, -2663, -9052, 38528]], ![![-38202, 8823, -2585, -8787, 37400]], ![![-25276, 5836, -1710, -5813, 24742]], ![![-106229, 24545, -7190, -24442, 104030]], ![![-33334, 7701, -2256, -7669, 32641]]]
  g := ![![![67, -39, 15, 44, -186], ![287, -157, 65, 197, -836], ![1419, -792, 328, 967, -4098], ![6896, -3922, 1555, 4604, -19498], ![1719, -979, 388, 1147, -4857]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N4 : Nat.card (O ⧸ I61N4) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N4)

lemma isPrimeI61N4 : Ideal.IsPrime I61N4 := prime_ideal_of_norm_prime hp61.out _ NI61N4
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![15395, -3559, 1043, 3544, -15084]] ![![-2011149, 464507, -136084, -462623, 1969042]]
  ![![21714084841, -5015215132, 1469279503, 4994874157, -21259464000]] where
 M := ![![![21714084841, -5015215132, 1469279503, 4994874157, -21259464000]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![21714084841, -5015215132, 1469279503, 4994874157, -21259464000]] ![![-8975, 2009, -737, -2234, 9392]]
  ![![14968115661, -3457125677, 1012814756, 3443104081, -14654733024]] where
 M := ![![![14968115661, -3457125677, 1012814756, 3443104081, -14654733024]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N2 : IdealMulLeCertificate' Table 
  ![![14968115661, -3457125677, 1012814756, 3443104081, -14654733024]] ![![-7693, 1352, -552, -1640, 6952]]
  ![![-87550617, 20236201, -5922860, -20143581, 85737352]] where
 M := ![![![-87550617, 20236201, -5922860, -20143581, 85737352]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N3 : IdealMulLeCertificate' Table 
  ![![-87550617, 20236201, -5922860, -20143581, 85737352]] ![![197, -39, 15, 44, -186]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![30780539, -5447300, 2219851, 6594649, -27945320]]]
 hmul := by decide  
 g := ![![![![504599, -89300, 36391, 108109, -458120]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2, I61N3, I61N4] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
    exact isPrimeI61N3
    exact isPrimeI61N4
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1 ⊙ MulI61N2 ⊙ MulI61N3)


lemma PB2201I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB2201I1 : PrimesBelowBoundCertificateInterval O 23 61 2201 where
  m := 9
  g := ![1, 2, 3, 1, 2, 2, 3, 2, 5]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB2201I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2, I61N3, I61N4]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![20511149]
    · exact ![29791, 961]
    · exact ![50653, 37, 37]
    · exact ![115856201]
    · exact ![3418801, 43]
    · exact ![4879681, 47]
    · exact ![2809, 2809, 53]
    · exact ![12117361, 59]
    · exact ![61, 61, 61, 61, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
      exact NI61N3
      exact NI61N4
  β := ![I31N1, I37N1, I37N2, I43N1, I47N1, I53N2, I59N1, I61N0, I61N1, I61N2, I61N3, I61N4]
  Il := ![[], [I31N1], [I37N1, I37N2], [], [I43N1], [I47N1], [I53N2], [I59N1], [I61N0, I61N1, I61N2, I61N3, I61N4]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
