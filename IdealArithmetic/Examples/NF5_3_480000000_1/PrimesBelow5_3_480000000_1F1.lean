
import IdealArithmetic.Examples.NF5_3_480000000_1.RI5_3_480000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![373, 256, -3, 258, 211]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![373, 256, -3, 258, 211]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![1, 15, 17, 1, 0], ![18, 5, 6, 0, 1]] where
  M :=![![![373, 256, -3, 258, 211], ![1688, 1167, -4, 1213, 985], ![3940, 2698, -46, 2837, 2312], ![8404, 5725, -137, 6021, 4919], ![19108, 13043, -275, 13682, 11170]]]
  hmulB := by decide  
  f := ![![![-151, 5, -75, -66, 47]], ![![376, 75, 142, 245, -151]], ![![-604, -241, -170, -509, 292]], ![![-131, -83, -22, -140, 76]], ![![-202, -61, -67, -152, 90]]]
  g := ![![![-127, -161, -195, 258, 211], ![-595, -757, -915, 1213, 985], ![-1397, -1773, -2143, 2837, 2312], ![-2971, -3765, -4552, 6021, 4919], ![-6746, -8553, -10341, 13682, 11170]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [11, 17, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 12, 2], [8, 16, 27], [0, 1]]
 g := ![![[9, 25, 9], [20, 16], [20, 14, 16], [1]], ![[22, 28, 2, 17], [11, 4], [11, 24, 23, 10], [16, 20, 25, 8]], ![[5, 12, 8, 15], [28, 4], [22, 4, 18, 14], [13, 4, 21, 21]]]
 h' := ![![[17, 12, 2], [11, 15, 3], [12, 4, 25], [18, 12, 25], [0, 1]], ![[8, 16, 27], [19, 17, 20], [13, 14, 2], [10, 23, 18], [17, 12, 2]], ![[0, 1], [5, 26, 6], [9, 11, 2], [21, 23, 15], [8, 16, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 6], []]
 b := ![[], [14, 10, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [11, 17, 4, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-654725, -465821, 49731, -410217, -604810]
  a := ![0, 1, 1, 0, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![366968, 300396, 367320, -410217, -604810]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85, -2, 41, 37, -24]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![85, -2, 41, 37, -24]] 
 ![![29, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![85, -2, 41, 37, -24], ![-192, -31, -78, -123, 87], ![348, 144, 92, 288, -141], ![-468, -261, -105, -484, 318], ![860, 499, 149, 823, -337]]]
  hmulB := by decide  
  f := ![![![7889, -1303, -8933, -739, 2142]], ![![1407, 224, -963, -150, 219]], ![![2710, -143, -2648, -266, 627]], ![![6603, -1455, -7980, -604, 1923]], ![![2201, -443, -2602, -203, 626]]]
  g := ![![![-38, -2, 41, 37, -24], ![111, -31, -78, -123, 87], ![-259, 144, 92, 288, -141], ![399, -261, -105, -484, 318], ![-735, 499, 149, 823, -337]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 14, -9, 9, -4]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![35, 14, -9, 9, -4]] 
 ![![29, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![35, 14, -9, 9, -4], ![-32, -3, 10, -55, 23], ![92, 74, 52, 118, -71], ![-268, -163, -49, -228, 130], ![308, 181, 65, 331, -181]]]
  hmulB := by decide  
  f := ![![![2503, -887, 1629, 369, -542]], ![![1663, -606, 1093, 236, -373]], ![![2322, -849, 1528, 328, -523]], ![![1739, -679, 1172, 222, -425]], ![![754, -408, 581, 34, -272]]]
  g := ![![![-6, 14, -9, 9, -4], ![24, -3, 10, -55, 23], ![-158, 74, 52, 118, -71], ![273, -163, -49, -228, 130], ![-356, 181, 65, 331, -181]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![373, 256, -3, 258, 211]] ![![85, -2, 41, 37, -24]]
  ![![42225, 28837, -602, 30230, 24680]] where
 M := ![![![42225, 28837, -602, 30230, 24680]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![42225, 28837, -602, 30230, 24680]] ![![35, 14, -9, 9, -4]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-493, -319, -29, -406, -87]]]
 hmul := by decide  
 g := ![![![![-17, -11, -1, -14, -3]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [8, 7, 1, 7, 29, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 6, 3, 7, 27], [9, 10, 2, 21, 24], [14, 29, 10, 12, 26], [0, 16, 16, 22, 16], [0, 1]]
 g := ![![[22, 13, 20, 20, 16], [16, 10, 6, 6, 7], [28, 2, 1], []], ![[3, 12, 8, 17, 13, 24, 2, 15], [27, 7, 3, 5, 24, 19, 11, 22], [20, 7, 2, 19, 19, 22, 27, 29], [18, 28, 24, 6, 9, 17, 22, 29]], ![[10, 5, 29, 19, 28, 25, 7, 17], [17, 3, 9, 15, 24, 3, 12, 27], [6, 14, 25, 27, 28, 7, 26, 23], [20, 12, 6, 26, 11, 3, 14, 29]], ![[28, 10, 1, 12, 13, 1, 8, 24], [24, 15, 1, 6, 24, 2, 15, 26], [19, 25, 7, 10, 27, 7, 2, 26], [25, 25, 26, 11, 12, 21, 30, 30]], ![[0, 16, 28, 26, 23, 10, 6, 28], [6, 28, 10, 17, 17, 23, 25, 25], [2, 5, 16, 17, 7, 13, 6, 10], [28, 24, 1, 24, 23, 15, 9, 4]]]
 h' := ![![[10, 6, 3, 7, 27], [27, 12, 13, 17, 27], [24, 5, 12, 12, 10], [0, 0, 0, 1], [0, 1]], ![[9, 10, 2, 21, 24], [5, 10, 4, 12, 29], [9, 23, 22, 6, 17], [19, 24, 24, 19, 4], [10, 6, 3, 7, 27]], ![[14, 29, 10, 12, 26], [21, 27, 7, 29, 23], [18, 11, 0, 6, 25], [11, 24, 27, 23, 14], [9, 10, 2, 21, 24]], ![[0, 16, 16, 22, 16], [27, 27, 30, 8, 19], [28, 6, 10, 8, 1], [2, 30, 29, 0, 1], [14, 29, 10, 12, 26]], ![[0, 1], [14, 17, 8, 27, 26], [15, 17, 18, 30, 9], [24, 15, 13, 19, 12], [0, 16, 16, 22, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 26, 7, 29], [], [], []]
 b := ![[], [11, 3, 15, 29, 15], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [8, 7, 1, 7, 29, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7120480175494861, -4894403140872758, 170543182808916, -4995815622248921, -4545913367667915]
  a := ![3, -2, 0, -3, -61]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-229692908886931, -157883972286218, 5501392993836, -161155342653191, -146642366698965]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 28629151 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀

instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [32, 16, 4, 28, 11, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 18, 28, 36, 11], [9, 11, 22, 2, 20], [7, 34, 12, 33, 34], [15, 10, 12, 3, 9], [0, 1]]
 g := ![![[36, 13, 28, 19, 21], [11, 29, 13, 30], [5, 21, 19, 26, 1], [], []], ![[23, 2, 6, 33, 12, 10, 35, 34], [8, 24, 21, 28], [0, 9, 16, 2, 6, 0, 30, 12], [16, 14, 0, 25], [5, 13, 16, 10]], ![[17, 30, 12, 9, 5, 18, 19, 32], [31, 28, 24, 25], [17, 11, 12, 34, 27, 1, 34, 18], [15, 19, 20, 34], [21, 19, 9, 30]], ![[16, 17, 4, 20, 30, 31, 36, 1], [28, 7, 16, 36], [36, 12, 19, 0, 19, 4, 13, 10], [26, 29, 33, 33], [36, 36, 36, 9]], ![[12, 26, 9, 21, 15, 26, 21, 28], [23, 11], [20, 27, 26, 7, 13, 29, 3, 4], [14, 12, 20, 1], [23, 23, 14, 7]]]
 h' := ![![[32, 18, 28, 36, 11], [14, 35, 8, 16, 24], [25, 25, 35, 9, 17], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[9, 11, 22, 2, 20], [31, 12, 28, 8, 17], [18, 17, 24, 33, 19], [27, 35, 31, 24, 19], [13, 27, 7, 28, 32], [32, 18, 28, 36, 11]], ![[7, 34, 12, 33, 34], [33, 27, 35, 6, 34], [10, 21, 6, 33, 32], [2, 28, 9, 24, 7], [1, 31, 26, 10, 16], [9, 11, 22, 2, 20]], ![[15, 10, 12, 3, 9], [25, 23, 29, 19, 30], [25, 25, 25, 22, 6], [31, 35, 27, 15, 34], [7, 6, 7, 2, 25], [7, 34, 12, 33, 34]], ![[0, 1], [25, 14, 11, 25, 6], [24, 23, 21, 14], [8, 13, 7, 11, 13], [7, 10, 33, 34, 1], [15, 10, 12, 3, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 34, 3, 12], [], [], []]
 b := ![[], [23, 4, 18, 2, 9], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [32, 16, 4, 28, 11, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-69675125500, -47699428676, 1257933807, -49480574969, -42216950568]
  a := ![1, 0, 1, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1883111500, -1289173748, 33998211, -1337312837, -1140998664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 69343957 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11471, -3717, 7244, 1883, -2215]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![11471, -3717, 7244, 1883, -2215]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![9, 27, 13, 3, 1]] where
  M :=![![![11471, -3717, 7244, 1883, -2215], ![-17720, 5757, -11200, -2900, 3434], ![13736, -4425, 8657, 2269, -2633], ![-1672, 601, -1094, -243, 370], ![3680, -1055, 2236, 680, -607]]]
  hmulB := by decide  
  f := ![![![-41, -11, 22, 5, -5]], ![![-40, -49, -32, 4, 10]], ![![40, -13, -53, 1, 11]], ![![64, 45, 2, -17, 2]], ![![-17, -35, -33, 3, 9]]]
  g := ![![![766, 1368, 879, 208, -2215], ![-1186, -2121, -1362, -322, 3434], ![913, 1626, 1046, 248, -2633], ![-122, -229, -144, -33, 370], ![223, 374, 247, 61, -607]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [16, 19, 5, 20, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 36, 13, 6], [5, 40, 18, 24], [10, 5, 10, 11], [0, 1]]
 g := ![![[15, 28, 9, 20], [24, 23, 5], [30, 40, 20], [21, 1], []], ![[19, 18, 30, 39, 37, 29], [11, 1, 18], [29, 3, 20], [26, 1, 4, 14, 38, 27], [16, 10, 36]], ![[33, 39, 15, 34, 37, 19], [33, 26, 39], [0, 1, 21], [28, 33, 28, 29, 3, 28], [22, 4, 2]], ![[10, 31, 25, 6, 6, 26], [28, 31, 32], [32, 5, 1], [32, 9, 8, 10, 8, 26], [22, 14, 39]]]
 h' := ![![[6, 36, 13, 6], [21, 26, 15, 15], [35, 18, 0, 13], [33, 36, 40, 26], [0, 0, 1], [0, 1]], ![[5, 40, 18, 24], [20, 37, 6, 30], [27, 17, 25, 31], [32, 25, 18, 26], [26, 9, 32, 36], [6, 36, 13, 6]], ![[10, 5, 10, 11], [1, 15, 33, 8], [23, 23, 18, 11], [8, 5, 32, 29], [1, 0, 4, 34], [5, 40, 18, 24]], ![[0, 1], [4, 4, 28, 29], [1, 24, 39, 27], [12, 16, 33, 1], [35, 32, 4, 12], [10, 5, 10, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 9, 27], []]
 b := ![[], [], [17, 0, 10, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [16, 19, 5, 20, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42160512781, 30530608973, -4308905550, 24797351570, 45107980239]
  a := ![1, -4, -2, -5, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8873446570, -28960606280, -14407625577, -2695770467, 45107980239]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -11, 22, 5, -5]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-41, -11, 22, 5, -5]] 
 ![![41, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-41, -11, 22, 5, -5], ![-40, -49, -32, 4, 10], ![40, -13, -53, 1, 11], ![64, 45, 2, -17, 2], ![40, 21, -4, 8, -5]]]
  hmulB := by decide  
  f := ![![![11471, -3717, 7244, 1883, -2215]], ![![8241, -2670, 5204, 1353, -1591]], ![![9288, -3009, 5865, 1525, -1793]], ![![239, -76, 150, 40, -45]], ![![2328, -751, 1468, 384, -447]]]
  g := ![![![-9, -11, 22, 5, -5], ![59, -49, -32, 4, 10], ![50, -13, -53, 1, 11], ![-34, 45, 2, -17, 2], ![-11, 21, -4, 8, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![11471, -3717, 7244, 1883, -2215]] ![![-41, -11, 22, 5, -5]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [15, 34, 40, 31, 10, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 20, 1, 21], [7, 33, 11, 16, 20], [6, 13, 8, 6, 21], [0, 19, 23, 0, 2], [0, 1]]
 g := ![![[13, 4, 12, 41, 14], [11, 11, 3, 7, 11], [4, 10, 7, 14], [1], []], ![[7, 20, 27, 22, 13, 6, 10], [17, 42, 9, 18, 34, 30, 17], [23, 15, 38, 23], [19, 8, 24, 12, 9, 22, 13], [18, 11]], ![[42, 16, 16, 37, 25, 6, 27, 37], [17, 36, 4, 2, 8, 12, 21, 18], [13, 9, 6, 4], [2, 11, 5, 2, 6, 7, 35, 2], [1, 9, 37, 13]], ![[16, 0, 16, 27, 21, 36, 29, 10], [2, 27, 27, 19, 10, 32, 2, 24], [15, 38, 15, 24], [20, 11, 20, 3, 3, 33, 12, 17], [15, 30, 13, 11]], ![[0, 5, 20, 34, 11, 29, 21, 20], [40, 18, 40, 32, 28, 26, 25, 2], [27, 10, 32, 1], [11, 13, 10, 23, 18, 5, 42, 2], [13, 24, 3, 4]]]
 h' := ![![[20, 20, 1, 21], [7, 26, 2, 6, 33], [36, 3, 31, 12, 21], [28, 9, 3, 12, 33], [0, 0, 1], [0, 1]], ![[7, 33, 11, 16, 20], [30, 25, 14, 36, 18], [5, 40, 21, 35, 40], [36, 2, 31, 26, 25], [1, 23, 34, 11, 19], [20, 20, 1, 21]], ![[6, 13, 8, 6, 21], [22, 4, 0, 9, 2], [31, 17, 42, 10, 17], [21, 8, 9, 10, 41], [34, 35, 41, 9, 20], [7, 33, 11, 16, 20]], ![[0, 19, 23, 0, 2], [13, 0, 20, 22, 18], [0, 12, 33, 8, 9], [15, 2, 40, 17, 29], [26, 13, 41, 29, 3], [6, 13, 8, 6, 21]], ![[0, 1], [2, 31, 7, 13, 15], [31, 14, 2, 21, 42], [7, 22, 3, 21, 1], [20, 15, 12, 37, 1], [0, 19, 23, 0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 6, 30], [], [], []]
 b := ![[], [18, 36, 3, 1, 17], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [15, 34, 40, 31, 10, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1234208888255, 672774990000, 343969921930, 1407466487368, -1271710752552]
  a := ![-1, 7, 6, 9, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![28702532285, 15645930000, 7999300510, 32731778776, -29574668664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 147008443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 5 2 5 [31, 26, 19, 36, 37, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 31, 8, 45, 21], [23, 26, 10, 0, 22], [21, 1, 16, 28, 46], [14, 35, 13, 21, 5], [0, 1]]
 g := ![![[44, 35, 19, 5, 37], [41, 18, 44, 30, 18], [12, 39, 22, 45, 6], [1], []], ![[23, 3, 9, 6, 1, 17, 41, 28], [39, 25, 19, 36, 38, 12, 32, 7], [43, 22, 40, 29, 14, 34, 14, 8], [33, 5, 22, 33, 44, 39, 24, 21], [44, 41, 2, 18]], ![[11, 3, 3, 37, 11, 8, 25, 11], [34, 46, 40, 24, 1, 2, 30, 5], [12, 16, 2, 15, 21, 31, 9, 46], [45, 44, 0, 21, 39, 34, 29, 22], [33, 20, 46, 14]], ![[18, 26, 15, 39, 36, 31, 43, 13], [8, 25, 45, 34, 13, 21, 14, 40], [18, 28, 40, 23, 6, 21, 11, 19], [3, 27, 9, 39, 10, 1, 32, 22], [15, 21, 1, 1]], ![[13, 18, 12, 37, 23, 35, 33, 39], [19, 43, 42, 39, 18, 17, 26, 31], [37, 10, 29, 34, 43, 33, 13, 26], [40, 43, 18, 18, 0, 28, 7, 45], [16, 41, 37, 25]]]
 h' := ![![[46, 31, 8, 45, 21], [45, 37, 6, 20, 32], [4, 4, 17, 30, 21], [16, 21, 28, 11, 10], [0, 0, 1], [0, 1]], ![[23, 26, 10, 0, 22], [4, 37, 16, 36, 39], [3, 32, 15, 5, 4], [11, 21, 10, 5, 42], [0, 14, 15, 18, 1], [46, 31, 8, 45, 21]], ![[21, 1, 16, 28, 46], [13, 34, 19, 21, 20], [34, 5, 17, 26, 34], [9, 34, 11, 16, 28], [23, 0, 20, 1, 1], [23, 26, 10, 0, 22]], ![[14, 35, 13, 21, 5], [42, 10, 24, 29, 9], [42, 3, 27, 5, 30], [18, 7, 2, 19, 34], [23, 35, 46, 24, 42], [21, 1, 16, 28, 46]], ![[0, 1], [23, 23, 29, 35, 41], [15, 3, 18, 28, 5], [6, 11, 43, 43, 27], [29, 45, 12, 4, 3], [14, 35, 13, 21, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 31, 19, 36], [], [], []]
 b := ![[], [45, 39, 21, 10, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 5
  hpos := by decide
  P := [31, 26, 19, 36, 37, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3799724552609, -2225867241936, -730049492240, -3856294333764, 2101547082276]
  a := ![0, -12, 0, -22, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-80845203247, -47358877488, -15532967920, -82048815612, 44713767708]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 229345007 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1901, -1114, -368, -1934, 1062]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-1901, -1114, -368, -1934, 1062]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![50, 36, 49, 1, 0], ![44, 17, 29, 0, 1]] where
  M :=![![![-1901, -1114, -368, -1934, 1062], ![8496, 4975, 1640, 8632, -4740], ![-18960, -11098, -3657, -19266, 10578], ![38064, 22282, 7348, 38683, -21240], ![-53760, -31470, -10376, -54628, 29995]]]
  hmulB := by decide  
  f := ![![![23, -6, 8, -2, -6]], ![![-48, 3, -8, -24, -12]], ![![-48, -46, 27, -38, -42]], ![![-58, -48, 27, -55, -54]], ![![-28, -33, 19, -34, -35]]]
  g := ![![![907, 952, 1200, -1934, 1062], ![-4048, -4249, -5356, 8632, -4740], ![9036, 9484, 11955, -19266, 10578], ![-18142, -19042, -24003, 38683, -21240], ![25620, 26891, 33897, -54628, 29995]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [9, 32, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 46, 37], [41, 6, 16], [0, 1]]
 g := ![![[34, 9, 37], [36, 38], [21, 27, 24], [], [1]], ![[33, 46, 15, 28], [21, 25], [42, 3, 7, 42], [45, 6], [6, 30, 30, 38]], ![[2, 37, 22, 11], [34, 49], [45, 17, 42, 52], [31, 6], [49, 35, 50, 15]]]
 h' := ![![[12, 46, 37], [46, 6, 14], [23, 28, 12], [28, 46, 17], [44, 21], [0, 1]], ![[41, 6, 16], [39, 42, 41], [49, 35, 48], [26, 45, 2], [31, 12, 35], [12, 46, 37]], ![[0, 1], [5, 5, 51], [24, 43, 46], [2, 15, 34], [4, 20, 18], [41, 6, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 3], []]
 b := ![[], [27, 3, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [9, 32, 0, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![657318, 206824, 508485, 1219324, -2463249]
  a := ![13, 5, 5, 6, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![907058, -34219, 230110, 1219324, -2463249]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -6, 8, -2, -6]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![23, -6, 8, -2, -6]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![4, 4, 1, 0, 0], ![37, 13, 0, 1, 0], ![51, 2, 0, 0, 1]] where
  M :=![![![23, -6, 8, -2, -6], ![-48, 3, -8, -24, -12], ![-48, -46, 27, -38, -42], ![-144, -98, -4, -89, -72], ![-288, -202, 8, -204, -169]]]
  hmulB := by decide  
  f := ![![![-1901, -1114, -368, -1934, 1062]], ![![8496, 4975, 1640, 8632, -4740]], ![![140, 82, 27, 142, -78]], ![![1475, 863, 284, 1497, -822]], ![![-2523, -1478, -488, -2566, 1409]]]
  g := ![![![7, 0, 8, -2, -6], ![28, 7, -8, -24, -12], ![64, 8, 27, -38, -42], ![129, 23, -4, -89, -72], ![299, 52, 8, -204, -169]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [32, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 52], [0, 1]]
 g := ![![[9, 44], [1], [18, 36], [29], [30, 1]], ![[4, 9], [1], [38, 17], [29], [7, 52]]]
 h' := ![![[30, 52], [17, 16], [7, 52], [9, 47], [47, 20], [0, 1]], ![[0, 1], [20, 37], [30, 1], [41, 6], [11, 33], [30, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [1, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [32, 23, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10, -36, -25, -111, 144]
  a := ![-1, -2, 0, -3, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-59, 23, -25, -111, 144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-1901, -1114, -368, -1934, 1062]] ![![23, -6, 8, -2, -6]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [14, 22, 10, 57, 22, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 53, 30, 3, 37], [8, 7, 28, 37, 56], [21, 25, 34, 22, 22], [35, 32, 26, 56, 3], [0, 1]]
 g := ![![[23, 11, 13, 47, 49], [9, 54, 3, 45, 22], [56, 43, 50, 5], [14, 37, 1], []], ![[55, 49, 55, 10, 40, 51, 16, 23], [55, 4, 5, 36, 17, 39, 25, 43], [35, 22, 38, 4], [18, 45, 7, 42, 22, 55, 11, 33], [54, 24, 20, 56, 38, 19, 16, 31]], ![[48, 58, 55, 15, 34, 56, 19, 13], [47, 29, 15, 15, 44, 15, 50, 31], [41, 17, 58, 53], [39, 57, 11, 20, 34, 42, 22, 58], [29, 31, 51, 55, 44, 4, 0, 32]], ![[45, 34, 15, 49, 40, 20, 30, 41], [40, 49, 51, 43, 48, 19, 40, 48], [35, 24, 51, 46], [9, 57, 47, 23, 15, 47, 34, 3], [5, 46, 48, 8, 37, 29, 58, 28]], ![[55, 33, 11, 3, 4, 41, 7, 46], [30, 43, 24, 30, 1, 22, 49, 25], [33, 51, 57, 9], [41, 44, 40, 37, 43, 47, 3, 45], [34, 41, 44, 54, 32, 52, 33, 27]]]
 h' := ![![[32, 53, 30, 3, 37], [51, 31, 19, 25, 52], [49, 54, 4, 13, 9], [40, 0, 35, 49, 51], [0, 0, 0, 1], [0, 1]], ![[8, 7, 28, 37, 56], [21, 54, 41, 3, 19], [35, 31, 51, 18, 52], [42, 42, 5, 2, 2], [34, 45, 45, 47, 38], [32, 53, 30, 3, 37]], ![[21, 25, 34, 22, 22], [34, 36, 30, 42, 25], [36, 20, 56, 19, 18], [16, 51, 57, 23, 42], [47, 36, 28, 20, 16], [8, 7, 28, 37, 56]], ![[35, 32, 26, 56, 3], [22, 5, 11, 2, 47], [42, 18, 2, 49, 18], [1, 31, 51, 31, 20], [46, 48, 23, 58, 34], [21, 25, 34, 22, 22]], ![[0, 1], [50, 51, 17, 46, 34], [8, 54, 5, 19, 21], [23, 53, 29, 13, 3], [37, 48, 22, 51, 30], [35, 32, 26, 56, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 24, 29, 34], [], [], []]
 b := ![[], [21, 36, 58, 17, 23], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [14, 22, 10, 57, 22, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30565043338, -17942127032, -5797820732, -30914852568, 16497977424]
  a := ![3, -4, 7, -8, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-518051582, -304103848, -98268148, -523980552, 279626736]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 714924299 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-167, -531, -582, 38, 154]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-167, -531, -582, 38, 154]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![31, 12, 39, 5, 1]] where
  M :=![![![-167, -531, -582, 38, 154], ![1232, -17, -1138, -124, 268], ![1072, 779, 107, -138, -52], ![-824, 537, 1486, 56, -367], ![-128, 283, 508, 1, -134]]]
  hmulB := by decide  
  f := ![![![133, -43, 84, 22, -26]], ![![-208, 65, -130, -36, 40]], ![![160, -51, 101, 28, -34]], ![![-32, -1, -14, -14, 5]], ![![127, -42, 81, 21, -27]]]
  g := ![![![-81, -39, -108, -12, 154], ![-116, -53, -190, -24, 268], ![44, 23, 35, 2, -52], ![173, 81, 259, 31, -367], ![66, 31, 94, 11, -134]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [19, 59, 41, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 33, 42, 18], [24, 24, 34, 31], [46, 3, 46, 12], [0, 1]]
 g := ![![[4, 37, 10, 22], [41, 35, 34], [42, 7, 20, 46], [34, 56, 55, 1], []], ![[19, 45, 16, 27, 27, 29], [42, 8, 34], [11, 25, 11, 15, 15, 55], [33, 12, 13, 54, 10, 11], [44, 59, 23, 55, 37, 37]], ![[47, 8, 48, 41, 0, 33], [4, 48, 36], [49, 53, 35, 7, 8, 26], [30, 0, 5, 22, 26, 8], [6, 32, 40, 20, 40, 23]], ![[4, 17, 22, 1, 12, 20], [12, 46, 42], [60, 39, 7, 27, 1, 39], [15, 50, 58, 36, 40, 39], [12, 19, 26, 47, 49, 20]]]
 h' := ![![[46, 33, 42, 18], [39, 1, 11, 12], [56, 27, 23, 41], [25, 41, 52, 31], [0, 0, 0, 1], [0, 1]], ![[24, 24, 34, 31], [36, 26, 17, 26], [38, 51, 13, 41], [45, 17, 51, 9], [59, 14, 36, 2], [46, 33, 42, 18]], ![[46, 3, 46, 12], [60, 31, 13, 35], [21, 15, 39, 55], [11, 42, 56, 28], [46, 6, 35, 4], [24, 24, 34, 31]], ![[0, 1], [50, 3, 20, 49], [41, 29, 47, 46], [24, 22, 24, 54], [57, 41, 51, 54], [46, 3, 46, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [39, 45], []]
 b := ![[], [], [20, 12, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [19, 59, 41, 6, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-188861562, -81682985, -97874870, -280964890, 444073817]
  a := ![1, -4, -4, -5, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-228772949, -88697849, -285520553, -41005475, 444073817]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![133, -43, 84, 22, -26]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![133, -43, 84, 22, -26]] 
 ![![61, 0, 0, 0, 0], ![45, 1, 0, 0, 0], ![55, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![133, -43, 84, 22, -26], ![-208, 65, -130, -36, 40], ![160, -51, 101, 28, -34], ![-32, -1, -14, -14, 5], ![40, -15, 28, 9, -20]]]
  hmulB := by decide  
  f := ![![![-167, -531, -582, 38, 154]], ![![-103, -392, -448, 26, 118]], ![![-133, -466, -523, 32, 138]], ![![-71, -174, -176, 14, 47]], ![![-24, -65, -68, 5, 18]]]
  g := ![![![-46, -43, 84, 22, -26], ![73, 65, -130, -36, 40], ![-56, -51, 101, 28, -34], ![17, -1, -14, -14, 5], ![-14, -15, 28, 9, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-167, -531, -582, 38, 154]] ![![133, -43, 84, 22, -26]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)


lemma PB1072I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1072I1 : PrimesBelowBoundCertificateInterval O 23 61 1072 where
  m := 9
  g := ![3, 1, 1, 2, 1, 1, 2, 1, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1072I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0]
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
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
    · exact ![24389, 29, 29]
    · exact ![28629151]
    · exact ![69343957]
    · exact ![2825761, 41]
    · exact ![147008443]
    · exact ![229345007]
    · exact ![148877, 2809]
    · exact ![714924299]
    · exact ![13845841, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I29N1, I29N2, I41N1, I61N1]
  Il := ![[I29N1, I29N2], [], [], [I41N1], [], [], [], [], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
