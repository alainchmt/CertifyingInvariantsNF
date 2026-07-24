
import IdealArithmetic.Examples.NF5_3_125000000_3.RI5_3_125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![145, -39, -75, -26, -188]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![145, -39, -75, -26, -188]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![63, 11, 43, 1, 0], ![65, 19, 39, 0, 1]] where
  M :=![![![145, -39, -75, -26, -188], ![-128, -188, 341, 186, 1032], ![-336, 807, -716, -470, -2376], ![952, -719, 89, 183, 632], ![-52, -289, 401, 230, 1241]]]
  hmulB := by decide  
  f := ![![![-125, -93, 37, 26, 116]], ![![-160, -118, 31, 26, 120]], ![![-144, -143, -22, -2, 56]], ![![-233, -197, 21, 25, 156]], ![![-251, -207, 33, 32, 181]]]
  g := ![![![209, 57, 125, -26, -188], ![-1178, -326, -715, 186, 1032], ![2742, 763, 1674, -470, -2376], ![-771, -220, -484, 183, 632], ![-1421, -394, -864, 230, 1241]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [22, 12, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 51, 38], [45, 15, 29], [0, 1]]
 g := ![![[29, 50, 40], [52, 9, 40], [34, 64], [54, 39], [10, 1], []], ![[51, 28, 10, 45], [48, 47, 30, 7], [32, 16], [31, 54], [18, 24], [25, 37]], ![[66, 35, 40, 22], [6, 43, 23, 36], [13, 10], [55, 19], [5, 55], [34, 37]]]
 h' := ![![[32, 51, 38], [62, 38, 43], [49, 10, 24], [44, 4, 8], [48, 59, 21], [0, 0, 1], [0, 1]], ![[45, 15, 29], [19, 52, 12], [20, 51, 3], [11, 51, 4], [31, 53, 11], [5, 6, 15], [32, 51, 38]], ![[0, 1], [1, 44, 12], [59, 6, 40], [55, 12, 55], [40, 22, 35], [4, 61, 51], [45, 15, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 18], []]
 b := ![[], [26, 59, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [22, 12, 57, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2375655191, 1206515280, -2581289279, -1378767073, -4882245681]
  a := ![174, 136, -265, -119, -551]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6068417165, 1628889866, 3688257857, -1378767073, -4882245681]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-191, -139, 61, 42, 182]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-191, -139, 61, 42, 182]] 
 ![![67, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![66, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![-191, -139, 61, 42, 182], ![-280, -200, 99, 66, 280], ![-464, -315, 216, 134, 536], ![-396, -225, 329, 183, 664], ![150, 91, -105, -60, -223]]]
  hmulB := by decide  
  f := ![![![143, 523, -687, -262, -1658]], ![![-3, -25, 30, 12, 74]], ![![154, 643, -828, -318, -2004]], ![![-20, -225, 263, 103, 640]], ![![133, 484, -636, -242, -1533]]]
  g := ![![![-232, -139, 61, 42, 182], ![-362, -200, 99, 66, 280], ![-719, -315, 216, 134, 536], ![-951, -225, 329, 183, 664], ![314, 91, -105, -60, -223]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 4, -5, -3, -11]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![2, 4, -5, -3, -11]] 
 ![![67, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![2, 4, -5, -3, -11], ![28, 10, -27, -14, -52], ![128, 59, -130, -70, -232], ![362, 195, -405, -219, -778], ![-101, -52, 109, 59, 202]]]
  hmulB := by decide  
  f := ![![![420, 272, -77, -71, -269]], ![![304, 200, -60, -53, -205]], ![![24, 7, 6, 0, 10]], ![![194, 143, -57, -41, -176]], ![![123, 80, -23, -21, -80]]]
  g := ![![![2, 4, -5, -3, -11], ![16, 10, -27, -14, -52], ![65, 59, -130, -70, -232], ![211, 195, -405, -219, -778], ![-55, -52, 109, 59, 202]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![145, -39, -75, -26, -188]] ![![-191, -139, 61, 42, 182]]
  ![![121, 12, -30, -12, -70]] where
 M := ![![![121, 12, -30, -12, -70]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![121, 12, -30, -12, -70]] ![![2, 4, -5, -3, -11]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![-536, 134, 201, 67, 201]]]
 hmul := by decide  
 g := ![![![![-8, 2, 3, 1, 3]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![382, -728, 577, 389, 1941]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![382, -728, 577, 389, 1941]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![10, 17, 27, 31, 1]] where
  M :=![![![382, -728, 577, 389, 1941], ![-1572, 1332, -311, -386, -1492], ![3296, -517, -2120, -830, -5464], ![-182, -3121, 4081, 2361, 12918], ![-1861, 1146, 137, -153, -250]]]
  hmulB := by decide  
  f := ![![![2480, 1812, -763, -531, -2321]], ![![3460, 2522, -1057, -738, -3220]], ![![4832, 3545, -1506, -1042, -4568]], ![![1638, 1165, -467, -337, -1442]], ![![3717, 2706, -1133, -792, -3452]]]
  g := ![![![-268, -475, -730, -842, 1941], ![188, 376, 563, 646, -1492], ![816, 1301, 2048, 2374, -5464], ![-1822, -3137, -4855, -5607, 12918], ![9, 76, 97, 107, -250]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [5, 38, 61, 47, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 4, 19, 28], [13, 20, 7, 63], [68, 46, 45, 51], [0, 1]]
 g := ![![[54, 38, 51, 57], [67, 3, 61, 4], [63, 57, 27, 45], [0, 33, 8], [1], []], ![[13, 31, 34, 10, 68, 11], [7, 58, 35, 39, 7, 46], [45, 13, 46, 66, 36, 14], [13, 21, 25], [64, 34, 24], [47, 0, 3]], ![[52, 24, 13, 19, 35, 67], [63, 59, 64, 30, 19, 44], [57, 21, 26, 9, 27, 59], [51, 69, 5], [62, 9, 18], [39, 4, 64]], ![[66, 43, 18, 5, 67, 68], [9, 52, 4, 17, 37, 55], [0, 48, 11, 56, 54, 22], [0, 44, 18], [32, 44, 4], [40, 61, 45]]]
 h' := ![![[14, 4, 19, 28], [20, 33, 12, 25], [40, 5, 62, 69], [25, 2, 50, 20], [66, 33, 10, 24], [0, 0, 1], [0, 1]], ![[13, 20, 7, 63], [6, 12, 44, 47], [47, 44, 21, 13], [42, 59, 63, 6], [65, 28, 65, 66], [32, 30, 9, 33], [14, 4, 19, 28]], ![[68, 46, 45, 51], [22, 68, 69, 65], [50, 31, 21, 39], [8, 37, 34, 26], [11, 28, 34, 17], [45, 12, 3, 36], [13, 20, 7, 63]], ![[0, 1], [23, 29, 17, 5], [70, 62, 38, 21], [38, 44, 66, 19], [40, 53, 33, 35], [22, 29, 58, 2], [68, 46, 45, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [70, 53, 45], []]
 b := ![[], [], [66, 39, 13, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [5, 38, 61, 47, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-356453631576916352, -176915075667579240, 382636436000218144, 205174600276884913, 720909357243989896]
  a := ![2553, 2006, -3890, -1701, -8084]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-106557002873476272, -175103861250921232, -268759383233626888, -311873457384321153, 720909357243989896]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2480, -1812, 763, 531, 2321]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-2480, -1812, 763, 531, 2321]] 
 ![![71, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![62, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![-2480, -1812, 763, 531, 2321], ![-3460, -2522, 1057, 738, 3220], ![-4832, -3545, 1506, 1042, 4568], ![-1638, -1165, 467, 337, 1442], ![955, 698, -295, -205, -896]]]
  hmulB := by decide  
  f := ![![![-382, 728, -577, -389, -1941]], ![![6, 12, -20, -11, -61]], ![![-380, 643, -474, -328, -1618]], ![![-62, 167, -155, -99, -510]], ![![-189, 394, -327, -217, -1090]]]
  g := ![![![-2022, -1812, 763, 531, 2321], ![-2804, -2522, 1057, 738, 3220], ![-3983, -3545, 1506, 1042, 4568], ![-1251, -1165, 467, 337, 1442], ![781, 698, -295, -205, -896]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![382, -728, 577, 389, 1941]] ![![-2480, -1812, 763, 531, 2321]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![-71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-353, -275, 131, 84, 384]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-353, -275, 131, 84, 384]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![66, 13, 40, 1, 0], ![70, 51, 26, 0, 1]] where
  M :=![![![-353, -275, 131, 84, 384], ![-480, -282, 61, 70, 240], ![-720, -789, 558, 282, 1480], ![-184, 341, -529, -181, -1244], ![140, 115, -63, -38, -177]]]
  hmulB := by decide  
  f := ![![![-25, 29, -15, -12, -56]], ![![64, -36, -11, 2, -16]], ![![-112, -49, 148, 74, 408]], ![![-74, -5, 64, 29, 164]], ![![-18, -15, 30, 16, 79]]]
  g := ![![![-449, -287, -181, 84, 384], ![-300, -184, -123, 70, 240], ![-1684, -1095, -674, 282, 1480], ![1354, 906, 535, -181, -1244], ![206, 132, 83, -38, -177]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [55, 39, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 42, 49], [64, 30, 24], [0, 1]]
 g := ![![[67, 26, 16], [11, 25], [68, 24], [31, 65, 1], [29, 1], []], ![[71, 29, 36, 55], [25, 65], [42, 72], [68, 55, 41, 67], [67, 24], [15, 65]], ![[57, 37, 64, 9], [35, 38], [67, 37], [30, 19, 15, 6], [46, 12], [40, 65]]]
 h' := ![![[38, 42, 49], [56, 0, 4], [2, 13, 68], [47, 9, 30], [11, 55, 72], [0, 0, 1], [0, 1]], ![[64, 30, 24], [50, 70, 47], [29, 57, 49], [52, 27, 27], [22, 66, 37], [35, 54, 30], [38, 42, 49]], ![[0, 1], [48, 3, 22], [41, 3, 29], [52, 37, 16], [29, 25, 37], [71, 19, 42], [64, 30, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 64], []]
 b := ![[], [43, 16, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [55, 39, 44, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1580671688, 812219443, -1728194804, -921285629, -3275057771]
  a := ![157, 123, -239, -106, -497]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3995062564, 2463244917, 1647599074, -921285629, -3275057771]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, 29, -15, -12, -56]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-25, 29, -15, -12, -56]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![72, 66, 1, 0, 0], ![33, 12, 0, 1, 0], ![51, 4, 0, 0, 1]] where
  M :=![![![-25, 29, -15, -12, -56], ![64, -36, -11, 2, -16], ![-112, -49, 148, 74, 408], ![-104, 149, -115, -77, -444], ![84, -15, -47, -18, -105]]]
  hmulB := by decide  
  f := ![![![-353, -275, 131, 84, 384]], ![![-480, -282, 61, 70, 240]], ![![-792, -537, 192, 150, 616]], ![![-241, -166, 62, 47, 196]], ![![-271, -206, 94, 62, 279]]]
  g := ![![![59, 19, -15, -12, -56], ![22, 10, -11, 2, -16], ![-466, -169, 148, 74, 408], ![457, 143, -115, -77, -444], ![129, 51, -47, -18, -105]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [27, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 72], [0, 1]]
 g := ![![[63, 46], [69], [61], [9, 24], [46], [1]], ![[0, 27], [69], [61], [65, 49], [46], [1]]]
 h' := ![![[51, 72], [27, 51], [24, 19], [49, 34], [71, 30], [46, 51], [0, 1]], ![[0, 1], [0, 22], [44, 54], [31, 39], [68, 43], [19, 22], [51, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [71, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [27, 22, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-676354, -512548, 923621, 465825, 1858146]
  a := ![221, 177, -336, -143, -700]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2428969, -1020466, 923621, 465825, 1858146]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-353, -275, 131, 84, 384]] ![![-25, 29, -15, -12, -56]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![453, 329, -137, -96, -418]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![453, 329, -137, -96, -418]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![24, 49, 1, 0, 0], ![44, 76, 0, 1, 0], ![59, 67, 0, 0, 1]] where
  M :=![![![453, 329, -137, -96, -418], ![632, 468, -201, -138, -608], ![880, 621, -244, -178, -760], ![300, 255, -133, -79, -380], ![-174, -125, 51, 36, 157]]]
  hmulB := by decide  
  f := ![![![15, 19, -37, -20, -114]], ![![24, -98, 97, 62, 304]], ![![16, -53, 49, 32, 152]], ![![32, -85, 73, 49, 228]], ![![33, -70, 55, 38, 175]]]
  g := ![![![413, 536, -137, -96, -418], ![600, 779, -201, -138, -608], ![752, 975, -244, -178, -760], ![372, 484, -133, -79, -380], ![-155, -201, 51, 36, 157]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [65, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 78], [0, 1]]
 g := ![![[27, 62], [57, 8], [67, 42], [11, 52], [52], [1]], ![[0, 17], [0, 71], [64, 37], [75, 27], [52], [1]]]
 h' := ![![[62, 78], [8, 33], [69, 18], [75, 11], [55, 62], [14, 62], [0, 1]], ![[0, 1], [0, 46], [0, 61], [46, 68], [28, 17], [66, 17], [62, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [43, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [65, 17, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-165063, -323166, 449044, 199986, 1015132]
  a := ![-168, -142, 256, 94, 532]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1008029, -1335938, 449044, 199986, 1015132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 8, 8, 2, 18]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-21, 8, 8, 2, 18]] 
 ![![79, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![77, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-21, 8, 8, 2, 18], ![24, 21, -46, -24, -136], ![32, -110, 109, 68, 352], ![-124, 118, -40, -39, -164], ![14, 34, -54, -30, -165]]]
  hmulB := by decide  
  f := ![![![353, 240, -92, -70, -286]], ![![47, 33, -14, -10, -42]], ![![355, 238, -91, -70, -282]], ![![208, 146, -68, -47, -196]], ![![14, 10, -2, -2, -9]]]
  g := ![![![-11, 8, 8, 2, 18], ![63, 21, -46, -24, -136], ![-149, -110, 109, 68, 352], ![54, 118, -40, -39, -164], ![74, 34, -54, -30, -165]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-334, 449, -272, -203, -965]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-334, 449, -272, -203, -965]] 
 ![![79, 0, 0, 0, 0], ![40, 1, 0, 0, 0], ![59, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![-334, 449, -272, -203, -965], ![1012, -609, -104, 68, 12], ![-1584, -336, 1755, 832, 4976], ![-538, 2438, -2556, -1575, -8198], ![1077, -443, -364, -77, -782]]]
  hmulB := by decide  
  f := ![![![-27136, -19837, 8384, 5825, 25465]], ![![-14220, -10393, 4392, 3052, 13340]], ![![-20944, -15313, 6483, 4501, 19677]], ![![-22234, -16238, 6876, 4777, 20862]], ![![-17379, -12706, 5364, 3728, 16301]]]
  g := ![![![759, 449, -272, -203, -965], ![336, -609, -104, 68, 12], ![-5047, -336, 1755, 832, 4976], ![7236, 2438, -2556, -1575, -8198], ![1077, -443, -364, -77, -782]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2

def I79N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-76, -53, 20, 15, 63]] i)))

def SI79N3: IdealEqSpanCertificate' Table ![![-76, -53, 20, 15, 63]] 
 ![![79, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![-76, -53, 20, 15, 63], ![-108, -89, 46, 28, 132], ![-144, -66, -5, 12, 16], ![-58, -112, 104, 45, 262], ![29, 19, -6, -5, -20]]]
  hmulB := by decide  
  f := ![![![82, -99, 56, 43, 213]], ![![60, -73, 42, 32, 160]], ![![44, -40, 15, 14, 70]], ![![70, -72, 36, 29, 154]], ![![55, -74, 46, 34, 167]]]
  g := ![![![-27, -53, 20, 15, 63], ![-72, -89, 46, 28, 132], ![30, -66, -5, 12, 16], ![-188, -112, 104, 45, 262], ![7, 19, -6, -5, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N3 : Nat.card (O ⧸ I79N3) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N3)

lemma isPrimeI79N3 : Ideal.IsPrime I79N3 := prime_ideal_of_norm_prime hp79.out _ NI79N3
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![453, 329, -137, -96, -418]] ![![-21, 8, 8, 2, 18]]
  ![![51, 63, -31, -22, -100]] where
 M := ![![![51, 63, -31, -22, -100]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![51, 63, -31, -22, -100]] ![![-334, 449, -272, -203, -965]]
  ![![-38, -14388, 17803, 10489, 55841]] where
 M := ![![![-38, -14388, 17803, 10489, 55841]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N2 : IdealMulLeCertificate' Table 
  ![![-38, -14388, 17803, 10489, 55841]] ![![-76, -53, 20, 15, 63]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![4187, -6241, 4187, 3002, 14536]]]
 hmul := by decide  
 g := ![![![![53, -79, 53, 38, 184]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2, I79N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
    exact isPrimeI79N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1 ⊙ MulI79N2)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![182, 117, -44, -31, -131]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![182, 117, -44, -31, -131]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![32, 51, 1, 1, 0], ![62, 58, 2, 0, 1]] where
  M :=![![![182, 117, -44, -31, -131], ![220, 203, -82, -60, -260], ![400, 238, -137, -84, -400], ![98, 28, 48, 21, 138], ![-97, -27, 18, 9, 46]]]
  hmulB := by decide  
  f := ![![![0, 7, -8, -3, -21]], ![![-12, -35, 46, 20, 108]], ![![-48, 86, -71, -20, -208]], ![![-10, -21, 29, 13, 66]], ![![-9, -17, 24, 11, 54]]]
  g := ![![![112, 112, 3, -31, -131], ![220, 221, 6, -60, -260], ![336, 334, 9, -84, -400], ![-110, -109, -3, 21, 138], ![-39, -38, -1, 9, 46]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [70, 76, 74, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 10, 56], [11, 72, 27], [0, 1]]
 g := ![![[19, 55, 12], [78], [60, 21], [63, 33], [5, 9, 1], []], ![[43, 45, 76, 43], [17, 36, 3, 60], [50, 10], [62, 23], [34, 2, 62, 53], [45, 65]], ![[44, 55, 46, 1], [16, 25, 59, 23], [44, 64], [64, 4], [36, 36, 64, 44], [74, 65]]]
 h' := ![![[81, 10, 56], [18, 74, 26], [62, 24], [64, 46, 41], [65, 69, 38], [0, 0, 1], [0, 1]], ![[11, 72, 27], [78, 63, 40], [14, 74, 16], [51, 66, 50], [65, 7, 43], [8, 41, 72], [81, 10, 56]], ![[0, 1], [23, 29, 17], [77, 68, 67], [70, 54, 75], [63, 7, 2], [4, 42, 10], [11, 72, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 17], []]
 b := ![[], [49, 76, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [70, 76, 74, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-146627056, -70935454, 155390395, 83646530, 291630498]
  a := ![-23, -11, 37, 27, 75]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-251860324, -256041896, -6162857, 83646530, 291630498]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-131, -96, 40, 28, 122]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-131, -96, 40, 28, 122]] 
 ![![83, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![76, 0, 1, 0, 0], ![48, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![-131, -96, 40, 28, 122], ![-184, -135, 58, 40, 176], ![-256, -182, 73, 52, 224], ![-84, -70, 32, 21, 96], ![50, 36, -14, -10, -43]]]
  hmulB := by decide  
  f := ![![![43, -16, -12, 0, -6]], ![![8, -3, -2, 0, 0]], ![![44, -10, -19, -4, -24]], ![![36, -10, -12, -3, -8]], ![![3, -4, 2, 2, 7]]]
  g := ![![![-55, -96, 40, 28, 122], ![-80, -135, 58, 40, 176], ![-100, -182, 73, 52, 224], ![-44, -70, 32, 21, 96], ![19, 36, -14, -10, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![505, 369, -155, -108, -472]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![505, 369, -155, -108, -472]] 
 ![![83, 0, 0, 0, 0], ![65, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![81, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![505, 369, -155, -108, -472], ![704, 514, -215, -150, -656], ![976, 715, -294, -206, -904], ![312, 233, -79, -59, -268], ![-188, -139, 53, 38, 169]]]
  hmulB := by decide  
  f := ![![![-133, 83, 17, 4, 48]], ![![-103, 65, 12, 2, 32]], ![![-8, 7, 0, 2, 8]], ![![-143, 74, 34, 9, 84]], ![![-17, 14, -2, -2, -7]]]
  g := ![![![-100, 369, -155, -108, -472], ![-140, 514, -215, -150, -656], ![-199, 715, -294, -206, -904], ![-78, 233, -79, -59, -268], ![42, -139, 53, 38, 169]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![182, 117, -44, -31, -131]] ![![-131, -96, 40, 28, 122]]
  ![![-38052, -27805, 11696, 8147, 35597]] where
 M := ![![![-38052, -27805, 11696, 8147, 35597]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![-38052, -27805, 11696, 8147, 35597]] ![![505, 369, -155, -108, -472]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![-31526056, -23020050, 9680539, 6743003, 29459937]]]
 hmul := by decide  
 g := ![![![![-379832, -277350, 116633, 81241, 354939]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0, 0, 0]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]] where
  M :=![![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 5 2 6 [6, 44, 11, 7, 68, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 54, 47, 22, 56], [57, 17, 79, 81, 77], [11, 71, 0, 61, 24], [80, 35, 52, 14, 21], [0, 1]]
 g := ![![[36, 27, 50, 25, 39], [8, 70, 55, 40], [24, 4, 47, 1], [75, 30, 43, 67, 85], [1], []], ![[39, 43, 51, 82, 15, 4, 6, 61], [22, 32, 35, 11], [77, 50, 84, 69], [4, 49, 80, 18, 84, 84, 52, 56], [77, 41, 8, 17, 2, 63, 11, 52], [12, 34, 57, 21]], ![[54, 69, 27, 51, 72, 58, 60, 77], [77, 54, 82, 44], [51, 79, 19, 5], [34, 62, 37, 57, 65, 7, 14, 62], [37, 50, 33, 34, 53, 28, 7, 28], [73, 82, 12, 55]], ![[13, 42, 16, 75, 69, 80, 23, 76], [36, 2, 7, 40], [74, 39, 55, 85], [74, 81, 15, 45, 49, 68, 48, 70], [86, 54, 73, 53, 54, 38, 47, 12], [73, 44, 72, 42]], ![[63, 81, 83, 15, 69, 80, 3, 49], [19, 50, 49, 72], [19, 19, 74, 67], [26, 22, 58, 11, 33, 37, 63, 71], [59, 54, 21, 13, 53, 1, 62, 2], [23, 87, 59, 85]]]
 h' := ![![[51, 54, 47, 22, 56], [51, 39, 5, 14, 67], [59, 74, 67, 12, 60], [84, 27, 83, 76, 88], [83, 45, 78, 82, 21], [0, 0, 1], [0, 1]], ![[57, 17, 79, 81, 77], [48, 39, 41, 70, 20], [64, 49, 10, 8, 10], [9, 84, 58, 10, 43], [26, 59, 17, 74, 1], [37, 59, 44, 45, 38], [51, 54, 47, 22, 56]], ![[11, 71, 0, 61, 24], [3, 10, 12, 43, 88], [51, 33, 66, 19, 20], [88, 4, 80, 21, 70], [25, 29, 84, 29, 43], [52, 14, 6, 37, 71], [57, 17, 79, 81, 77]], ![[80, 35, 52, 14, 21], [31, 86, 8, 69, 14], [43, 3, 3, 65, 60], [65, 70, 48, 69, 21], [17, 36, 50, 74, 60], [39, 44, 1, 42, 32], [11, 71, 0, 61, 24]], ![[0, 1], [74, 4, 23, 71, 78], [30, 19, 32, 74, 28], [77, 82, 87, 2, 45], [42, 9, 38, 8, 53], [32, 61, 37, 54, 37], [80, 35, 52, 14, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 69, 17, 69], [], [], []]
 b := ![[], [0, 47, 26, 47, 83], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 5
  hpos := by decide
  P := [6, 44, 11, 7, 68, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![228735978492942, 111949867481374, -243755635434448, -131003402405604, -458177562456390]
  a := ![59, 45, -90, -41, -187]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2570067174078, 1257863679566, -2738827364432, -1471948341636, -5148062499510]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 5584059449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18, 31, -34, -15, -81]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![18, 31, -34, -15, -81]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![58, 11, 1, 0, 0], ![69, 66, 0, 1, 0], ![86, 69, 0, 0, 1]] where
  M :=![![![18, 31, -34, -15, -81], ![36, -55, 58, 16, 156], ![240, 414, -571, -252, -1280], ![446, -304, 122, -35, 586], ![-151, -89, 174, 91, 338]]]
  hmulB := by decide  
  f := ![![![-280, 175, 26, -21, -13]], ![![452, 93, -490, -232, -1388]], ![![-116, 103, -25, -30, -118]], ![![94, 205, -324, -180, -987]], ![![77, 224, -332, -187, -1018]]]
  g := ![![![103, 72, -34, -15, -81], ![-184, -129, 58, 16, 156], ![1658, 1151, -571, -252, -1280], ![-563, -410, 122, -35, 586], ![-470, -323, 174, 91, 338]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [25, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 96], [0, 1]]
 g := ![![[63, 66], [3], [62], [22], [70], [74, 1]], ![[0, 31], [3], [62], [22], [70], [51, 96]]]
 h' := ![![[74, 96], [24, 39], [14, 87], [20, 16], [45, 64], [90, 19], [0, 1]], ![[0, 1], [0, 58], [50, 10], [40, 81], [28, 33], [41, 78], [74, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [16, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [25, 23, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1590355, -1052591, 2003255, 1028200, 3949690]
  a := ![-303, -239, 463, 203, 960]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5447405, -3747198, 2003255, 1028200, 3949690]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18, -4, -9, -1, -15]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![18, -4, -9, -1, -15]] 
 ![![97, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![73, 0, 1, 0, 0], ![78, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![18, -4, -9, -1, -15], ![-36, -32, 65, 26, 164], ![32, 191, -244, -110, -648], ![42, -341, 351, 159, 922], ![-29, -14, 41, 19, 114]]]
  hmulB := by decide  
  f := ![![![18284, 13352, -5607, -3907, -17075]], ![![2336, 1706, -716, -499, -2181]], ![![14124, 10315, -4329, -3017, -13187]], ![![14818, 10823, -4537, -3163, -13828]], ![![3323, 2426, -1021, -711, -3106]]]
  g := ![![![11, -4, -9, -1, -15], ![-97, -32, 65, 26, 164], ![371, 191, -244, -110, -648], ![-524, -341, 351, 159, 922], ![-66, -14, 41, 19, 114]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 2, -3, -1, -7]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![0, 2, -3, -1, -7]] 
 ![![97, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![0, 2, -3, -1, -7], ![-4, -12, 15, 6, 36], ![0, 41, -48, -18, -120], ![-22, -87, 109, 45, 258], ![3, 0, -1, -1, 0]]]
  hmulB := by decide  
  f := ![![![-18, -58, 3, 9, 21]], ![![-6, -16, 2, 3, 9]], ![![-12, -31, 0, 4, 6]], ![![-6, -27, 3, 5, 14]], ![![-1, -4, 1, 1, 4]]]
  g := ![![![2, 2, -3, -1, -7], ![-10, -12, 15, 6, 36], ![31, 41, -48, -18, -120], ![-73, -87, 109, 45, 258], ![1, 0, -1, -1, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2

def I97N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, -13, 18, 5, 37]] i)))

def SI97N3: IdealEqSpanCertificate' Table ![![-6, -13, 18, 5, 37]] 
 ![![97, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-6, -13, 18, 5, 37], ![28, 65, -92, -32, -212], ![-80, -304, 397, 152, 960], ![82, 602, -730, -291, -1798], ![23, -1, -16, -3, -30]]]
  hmulB := by decide  
  f := ![![![-2804, -2057, 834, 587, 2585]], ![![-1484, -1089, 440, 310, 1366]], ![![-680, -502, 193, 138, 614]], ![![-186, -145, 28, 26, 133]], ![![-317, -230, 102, 70, 303]]]
  g := ![![![-2, -13, 18, 5, 37], ![14, 65, -92, -32, -212], ![-54, -304, 397, 152, 960], ![81, 602, -730, -291, -1798], ![8, -1, -16, -3, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N3 : Nat.card (O ⧸ I97N3) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N3)

lemma isPrimeI97N3 : Ideal.IsPrime I97N3 := prime_ideal_of_norm_prime hp97.out _ NI97N3
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![18, 31, -34, -15, -81]] ![![18, -4, -9, -1, -15]]
  ![![-161, -1309, 1563, 604, 3782]] where
 M := ![![![-161, -1309, 1563, 604, 3782]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![-161, -1309, 1563, 604, 3782]] ![![0, 2, -3, -1, -7]]
  ![![3294, 26921, -32122, -12429, -77725]] where
 M := ![![![3294, 26921, -32122, -12429, -77725]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N2 : IdealMulLeCertificate' Table 
  ![![3294, 26921, -32122, -12429, -77725]] ![![-6, -13, 18, 5, 37]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![496931, 4067598, -4853104, -1877532, -11743402]]]
 hmul := by decide  
 g := ![![![![5123, 41934, -50032, -19356, -121066]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2, I97N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
    exact isPrimeI97N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1 ⊙ MulI97N2)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0, 0, 0]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]] where
  M :=![![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 5 2 6 [73, 52, 34, 2, 72, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 62, 19, 2, 91], [21, 70, 84, 0, 94], [7, 16, 1, 25, 18], [63, 53, 98, 74, 100], [0, 1]]
 g := ![![[5, 47, 28, 84, 47], [26, 35, 20, 70], [92, 16, 48, 28, 25], [5, 80, 46, 52], [29, 1], []], ![[91, 89, 16, 25, 51, 45, 82, 12], [71, 49, 2, 22], [80, 85, 45, 58, 70, 5, 61, 63], [87, 35, 67, 95], [81, 83, 88, 70], [47, 62, 72, 40, 91, 60, 82, 10]], ![[4, 25, 13, 36, 82, 58, 40, 86], [46, 83, 11, 77], [72, 94, 80, 9, 82, 60, 4, 39], [74, 29, 10, 1], [33, 52, 85, 37], [57, 67, 20, 14, 75, 99, 52, 61]], ![[57, 95, 9, 52, 40, 68, 100, 39], [18, 50, 89, 13], [10, 18, 99, 63, 95, 45, 56, 18], [82, 34, 59, 13], [84, 29, 69, 43], [62, 54, 6, 54, 78, 3, 13, 75]], ![[36, 17, 88, 44, 59, 10, 98, 100], [47, 25, 3, 36], [15, 14, 92, 0, 92, 30, 85, 4], [71, 87, 21, 58], [10, 15, 67, 87], [13, 25, 60, 17, 50, 70, 92, 100]]]
 h' := ![![[39, 62, 19, 2, 91], [97, 34, 30, 2, 59], [51, 2, 49, 27, 75], [55, 38, 80, 1, 5], [4, 35, 73, 9, 31], [0, 0, 0, 1], [0, 1]], ![[21, 70, 84, 0, 94], [47, 50, 33, 81, 76], [33, 91, 32, 78, 27], [59, 26, 13, 36, 23], [59, 8, 37, 96, 87], [35, 4, 56, 49, 75], [39, 62, 19, 2, 91]], ![[7, 16, 1, 25, 18], [46, 68, 4, 43, 43], [77, 14, 31, 0, 28], [51, 60, 7, 64, 92], [91, 27, 61, 60, 100], [50, 16, 62, 39, 21], [21, 70, 84, 0, 94]], ![[63, 53, 98, 74, 100], [36, 78, 59, 100, 25], [21, 87, 74, 7, 66], [93, 47, 43, 6, 1], [76, 52, 82, 94, 66], [59, 34, 68, 7, 89], [7, 16, 1, 25, 18]], ![[0, 1], [61, 73, 76, 77, 100], [82, 8, 16, 90, 6], [49, 31, 59, 95, 81], [92, 80, 50, 44, 19], [32, 47, 16, 5, 17], [63, 53, 98, 74, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 17, 14, 11], [], [], []]
 b := ![[], [5, 61, 67, 99, 92], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 5
  hpos := by decide
  P := [73, 52, 34, 2, 72, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18170272068224911, -8945731867063796, 19422962020144496, 10428560023594136, 36544661043178180]
  a := ![-167, -133, 254, 109, 529]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-179903683843811, -88571602644196, 192306554654896, 103253069540536, 361828327160180]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10510100501 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0, 0, 0]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]] where
  M :=![![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 5 2 6 [2, 51, 95, 62, 28, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [79, 41, 91, 96, 38], [68, 90, 60, 3, 3], [11, 77, 11, 15, 33], [20, 100, 44, 92, 29], [0, 1]]
 g := ![![[12, 66, 45, 4, 41], [99, 53, 52, 25, 25], [36, 64, 42, 94, 17], [81, 98, 61, 1], [75, 1], []], ![[76, 21, 33, 26, 32, 68, 18, 61], [78, 89, 61, 69, 37, 98, 39, 92], [101, 37, 101, 75, 72, 44, 38, 100], [64, 4, 13, 100], [25, 68, 73, 8], [55, 96, 34, 83, 84, 71, 96, 76]], ![[61, 13, 50, 63, 14, 16, 28, 10], [68, 35, 65, 34, 74, 67, 29, 102], [26, 79, 11, 39, 98, 32, 99, 22], [17, 33, 65, 4], [91, 0, 54, 55], [23, 35, 28, 15, 53, 78, 46, 27]], ![[0, 12, 83, 79, 57, 84, 92, 38], [65, 19, 91, 74, 21, 52, 74, 2], [33, 86, 62, 60, 33, 53, 1, 56], [86, 10, 81, 61], [74, 31, 18, 2], [41, 28, 55, 54, 85, 33, 51, 93]], ![[11, 60, 89, 5, 62, 78, 46, 26], [72, 6, 18, 44, 89, 44, 13, 68], [80, 89, 44, 80, 2, 96, 71, 63], [32, 26, 36, 83], [37, 2, 64, 7], [7, 49, 95, 36, 27, 29, 55, 81]]]
 h' := ![![[79, 41, 91, 96, 38], [8, 29, 98, 48, 12], [31, 59, 92, 82, 98], [90, 61, 4, 47, 74], [56, 87, 34, 96, 1], [0, 0, 0, 1], [0, 1]], ![[68, 90, 60, 3, 3], [76, 27, 41, 99, 52], [70, 69, 57, 85, 10], [34, 8, 26, 102, 56], [70, 97, 45, 19, 93], [74, 77, 71, 46, 76], [79, 41, 91, 96, 38]], ![[11, 77, 11, 15, 33], [77, 59, 92, 43, 81], [12, 38, 83, 31, 72], [78, 35, 59, 9, 30], [100, 79, 47, 70, 2], [30, 10, 42, 74, 40], [68, 90, 60, 3, 3]], ![[20, 100, 44, 92, 29], [26, 72, 42, 24, 34], [24, 21, 98, 8, 87], [63, 55, 10, 7, 79], [21, 40, 1, 48, 24], [13, 54, 62, 18, 65], [11, 77, 11, 15, 33]], ![[0, 1], [49, 19, 36, 95, 27], [57, 19, 82, 0, 42], [99, 47, 4, 41, 70], [67, 6, 79, 76, 86], [55, 65, 31, 67, 25], [20, 100, 44, 92, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96, 19, 68, 35], [], [], []]
 b := ![[], [38, 20, 67, 102, 56], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 5
  hpos := by decide
  P := [2, 51, 95, 62, 28, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-44579380708526, -21808534700418, 47495461719298, 25527726653741, 89268515356330]
  a := ![-32, -23, 49, 25, 102]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-432809521442, -211733346606, 461120987566, 247842006347, 866684615110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 11592740743 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀



lemma PB547I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB547I2 : PrimesBelowBoundCertificateInterval O 61 103 547 where
  m := 9
  g := ![3, 2, 2, 4, 3, 1, 4, 1, 1]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB547I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2, I79N3]
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0]
    · exact ![I97N0, I97N1, I97N2, I97N3]
    · exact ![I101N0]
    · exact ![I103N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![300763, 67, 67]
    · exact ![25411681, 71]
    · exact ![389017, 5329]
    · exact ![6241, 79, 79, 79]
    · exact ![571787, 83, 83]
    · exact ![5584059449]
    · exact ![9409, 97, 97, 97]
    · exact ![10510100501]
    · exact ![11592740743]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
      exact NI79N3
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
      exact NI97N3
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
  β := ![I67N1, I67N2, I71N1, I79N1, I79N2, I79N3, I83N1, I83N2, I97N1, I97N2, I97N3]
  Il := ![[I67N1, I67N2], [I71N1], [], [I79N1, I79N2, I79N3], [I83N1, I83N2], [], [I97N1, I97N2, I97N3], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
