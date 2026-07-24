
import IdealArithmetic.Examples.NF5_3_729000000_3.RI5_3_729000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5511, -1652, 7274, 1580, 5228]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-5511, -1652, 7274, 1580, 5228]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![124, 120, 2, 1, 0], ![25, 114, 172, 0, 1]] where
  M :=![![![-5511, -1652, 7274, 1580, 5228], ![-20912, -5533, 28064, 6160, 19936], ![-39872, -10200, 54275, 11936, 38416], ![-66376, -16512, 91016, 20051, 64256], ![-57992, -14288, 79736, 17576, 56243]]]
  hmulB := by decide  
  f := ![![![191, 180, -306, -60, 196]], ![![-784, -627, 1536, -688, 32]], ![![-64, -344, -531, 2208, -2032]], ![![-332, -248, 694, -437, 144]], ![![-487, -638, 398, 1492, -1705]]]
  g := ![![![-1669, -3956, -4498, 1580, 5228], ![-6448, -15163, -17152, 6160, 19936], ![-12464, -29256, -33051, 11936, 38416], ![-20900, -48984, -55282, 20051, 64256], ![-18309, -42890, -48388, 17576, 56243]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [163, 55, 139, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 105, 32], [31, 93, 167], [0, 1]]
 g := ![![[139, 71, 111], [40, 183, 7], [91, 112, 115], [123, 184], [191, 158], [52, 18], [1]], ![[127, 192, 130, 111], [19, 145, 153, 123], [93, 158, 20, 180], [121, 125], [42, 92], [165, 128], [57, 0, 140, 132]], ![[41, 132, 16, 167], [122, 139, 112, 85], [39, 117, 48, 42], [29, 7], [190, 45], [174, 50], [185, 42, 171, 67]]]
 h' := ![![[29, 105, 32], [47, 116, 132], [92, 94, 112], [79, 120, 48], [167, 55, 69], [183, 196, 122], [36, 144, 60], [0, 1]], ![[31, 93, 167], [137, 20, 68], [28, 65, 91], [89, 182, 145], [132, 88, 18], [49, 145, 106], [173, 95, 39], [29, 105, 32]], ![[0, 1], [146, 63, 198], [69, 40, 195], [67, 96, 6], [139, 56, 112], [57, 57, 170], [34, 159, 100], [31, 93, 167]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 155], []]
 b := ![[], [164, 68, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [163, 55, 139, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-38241, -42037, 344655, -805779, 377553]
  a := ![0, -8, -3, 2, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![454470, 269399, -316497, -805779, 377553]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 7880599 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-191, -180, 306, 60, -196]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-191, -180, 306, 60, -196]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![167, 197, 1, 0, 0], ![135, 80, 0, 1, 0], ![36, 136, 0, 0, 1]] where
  M :=![![![-191, -180, 306, 60, -196], ![784, 627, -1536, 688, -32], ![64, 344, 531, -2208, 2032], ![-4456, -4256, 7208, 1379, -4576], ![1304, 816, -3080, 2936, -1661]]]
  hmulB := by decide  
  f := ![![![5511, 1652, -7274, -1580, -5228]], ![![20912, 5533, -28064, -6160, -19936]], ![![25527, 6915, -34159, -7484, -24316]], ![![12479, 3428, -16674, -3649, -11884]], ![![15580, 4152, -20896, -4584, -14853]]]
  g := ![![![-263, -194, 306, 60, -196], ![832, 1269, -1536, 688, -32], ![685, -1025, 531, -2208, 2032], ![-6179, -4584, 7208, 1379, -4576], ![900, 3008, -3080, 2936, -1661]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P1 : CertificateIrreducibleZModOfList' 199 2 2 7 [75, 189, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 198], [0, 1]]
 g := ![![[106, 65], [163, 61], [96, 111], [111], [49], [28], [10, 1]], ![[159, 134], [176, 138], [12, 88], [111], [49], [28], [20, 198]]]
 h' := ![![[10, 198], [113, 142], [163, 114], [135, 67], [163, 67], [16, 192], [46, 25], [0, 1]], ![[0, 1], [140, 57], [109, 85], [9, 132], [37, 132], [145, 7], [97, 174], [10, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [189, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N1 : CertifiedPrimeIdeal' SI199N1 199 where
  n := 2
  hpos := by decide
  P := [75, 189, 1]
  hirr := P199P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2115, 6524, -29810, 76750, -1816]
  a := ![3, -61, 2, -69, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26711, -70, -29810, 76750, -1816]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N1 B_one_repr
lemma NI199N1 : Nat.card (O ⧸ I199N1) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-5511, -1652, 7274, 1580, 5228]] ![![-191, -180, 306, 60, -196]]
  ![![199, 0, 0, 0, 0]] where
 M := ![![![-199, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51, 29, -2, 5, -10]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-51, 29, -2, 5, -10]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![178, 66, 1, 0, 0], ![68, 59, 0, 1, 0], ![109, 140, 0, 0, 1]] where
  M :=![![![-51, 29, -2, 5, -10], ![40, -23, -2, -4, 10], ![-20, 5, 7, -3, -2], ![-16, 4, 0, 13, -16], ![-8, 16, -14, 4, -1]]]
  hmulB := by decide  
  f := ![![![-25, -31, -8, -3, 4]], ![![-16, -47, -38, -14, -10]], ![![-26, -41, -19, -7, 0]], ![![-12, -23, -14, -5, -2]], ![![-23, -47, -30, -11, -5]]]
  g := ![![![5, 6, -2, 5, -10], ![-2, -5, -2, -4, 10], ![-4, 0, 7, -3, -2], ![4, 7, 0, 13, -16], ![11, 4, -14, 4, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [185, 197, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 210], [0, 1]]
 g := ![![[33, 73], [168, 199], [70], [34], [50, 16], [121], [14, 1]], ![[0, 138], [0, 12], [70], [34], [63, 195], [121], [28, 210]]]
 h' := ![![[14, 210], [148, 110], [179, 153], [141, 131], [34, 178], [180, 207], [153, 11], [0, 1]], ![[0, 1], [0, 101], [0, 58], [76, 80], [205, 33], [124, 4], [96, 200], [14, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [159, 128]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [185, 197, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-169, -1126, 618, -671, 6]
  a := ![1, -6, -1, -3, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-309, -15, 618, -671, 6]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2873, 2613, -4944, 131, 2034]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![2873, 2613, -4944, 131, 2034]] 
 ![![211, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![68, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![2873, 2613, -4944, 131, 2034], ![-8136, -5877, 17430, -12184, 4854], ![-9708, -12391, 8685, 27187, -31698], ![67464, 61312, -116200, 3439, 47436], ![-6424, -392, 23330, -42578, 33445]]]
  hmulB := by decide  
  f := ![![![116915, -50843, -31350, -16233, -6420]], ![![7325, -2820, -2596, -1113, -918]], ![![12681, -4922, -4375, -1906, -1500]], ![![39340, -16076, -12216, -5709, -3540]], ![![46930, -19504, -14034, -6730, -3779]]]
  g := ![![![-488, 2613, -4944, 131, 2034], ![629, -5877, 17430, -12184, 4854], ![3410, -12391, 8685, 27187, -31698], ![-11436, 61312, -116200, 3439, 47436], ![-1604, -392, 23330, -42578, 33445]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-189, -200, 28, -5, 74]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![-189, -200, 28, -5, 74]] 
 ![![211, 0, 0, 0, 0], ![88, 1, 0, 0, 0], ![137, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![141, 0, 0, 0, 1]] where
  M :=![![![-189, -200, 28, -5, 74], ![-296, -319, 44, -8, 118], ![-236, -252, 35, -7, 94], ![-40, -42, 8, -1, 14], ![76, 82, -12, 3, -31]]]
  hmulB := by decide  
  f := ![![![89, 78, -212, -41, -152]], ![![40, 33, -92, -18, -66]], ![![63, 52, -145, -28, -104]], ![![29, 20, -60, -12, -42]], ![![67, 54, -152, -30, -109]]]
  g := ![![![16, -200, 28, -5, 74], ![26, -319, 44, -8, 118], ![20, -252, 35, -7, 94], ![3, -42, 8, -1, 14], ![-6, 82, -12, 3, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2

def I211N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -7, -18, 41, -32]] i)))

def SI211N3: IdealEqSpanCertificate' Table ![![-1, -7, -18, 41, -32]] 
 ![![211, 0, 0, 0, 0], ![189, 1, 0, 0, 0], ![180, 0, 1, 0, 0], ![92, 0, 0, 1, 0], ![94, 0, 0, 0, 1]] where
  M :=![![![-1, -7, -18, 41, -32], ![128, 127, -206, -86, 182], ![-364, -307, 673, -211, -76], ![88, -44, -432, 965, -800], ![520, 474, -890, 18, 371]]]
  hmulB := by decide  
  f := ![![![20517, -15871, 6692, -987, 8798]], ![![18211, -14180, 6094, -853, 7936]], ![![17392, -13597, 5911, -801, 7654]], ![![8732, -7000, 3256, -359, 4080]], ![![8962, -7146, 3278, -378, 4135]]]
  g := ![![![18, -7, -18, 41, -32], ![19, 127, -206, -86, 182], ![-175, -307, 673, -211, -76], ![344, -44, -432, 965, -800], ![164, 474, -890, 18, 371]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N3 : Nat.card (O ⧸ I211N3) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N3)

lemma isPrimeI211N3 : Ideal.IsPrime I211N3 := prime_ideal_of_norm_prime hp211.out _ NI211N3
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-51, 29, -2, 5, -10]] ![![2873, 2613, -4944, 131, 2034]]
  ![![38509, 31566, -74056, 28584, 3158]] where
 M := ![![![38509, 31566, -74056, 28584, 3158]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![38509, 31566, -74056, 28584, 3158]] ![![-189, -200, 28, -5, 74]]
  ![![-47873, -50814, 65972, 54209, -84532]] where
 M := ![![![-47873, -50814, 65972, 54209, -84532]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI211N2 : IdealMulLeCertificate' Table 
  ![![-47873, -50814, 65972, 54209, -84532]] ![![-1, -7, -18, 41, -32]]
  ![![211, 0, 0, 0, 0]] where
 M := ![![![-69656375, -68825035, 107543746, 39277228, -87458656]]]
 hmul := by decide  
 g := ![![![![-330125, -326185, 509686, 186148, -414496]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1, I211N2, I211N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
    exact isPrimeI211N2
    exact isPrimeI211N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0 ⊙ MulI211N1 ⊙ MulI211N2)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-885, -347, 1026, 216, 770]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![-885, -347, 1026, 216, 770]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![0, 0, 223, 0, 0], ![0, 0, 0, 223, 0], ![148, 118, 189, 75, 1]] where
  M :=![![![-885, -347, 1026, 216, 770], ![-3080, -967, 3926, 850, 2836], ![-5672, -1563, 7541, 1658, 5386], ![-9232, -2310, 12632, 2765, 8942], ![-8012, -1940, 11074, 2437, 7781]]]
  hmulB := by decide  
  f := ![![![173, -105, 8, -16, 34]], ![![-136, 81, -6, 14, -28]], ![![56, -29, -3, -6, 14]], ![![40, -34, 16, -11, 10]], ![![104, -63, 5, -12, 23]]]
  g := ![![![-515, -409, -648, -258, 770], ![-1896, -1505, -2386, -950, 2836], ![-3600, -2857, -4531, -1804, 5386], ![-5976, -4742, -7522, -2995, 8942], ![-5200, -4126, -6545, -2606, 7781]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 4 2 7 [62, 17, 87, 84, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [182, 118, 180, 113], [219, 1, 162, 30], [184, 103, 104, 80], [0, 1]]
 g := ![![[69, 32, 170, 144], [17, 98, 2, 203], [200, 198, 66, 66], [111, 122, 130, 218], [54, 58, 182, 116], [56, 139, 1], []], ![[168, 147, 24, 188, 167, 20], [64, 49, 7, 201, 57, 149], [4, 29, 90, 181, 95, 209], [171, 20, 174, 15, 198, 180], [134, 2, 21, 170, 120, 22], [123, 183, 171], [126, 72, 196, 14, 151, 87]], ![[73, 48, 217, 99, 148, 112], [107, 165, 99, 111, 130, 178], [85, 151, 105, 134, 22, 63], [43, 175, 80, 20, 218, 146], [43, 28, 78, 188, 155, 188], [19, 60, 89], [10, 1, 24, 131, 7, 17]], ![[27, 207, 84, 91, 44, 90], [210, 20, 46, 2, 222, 44], [135, 59, 201, 61, 76, 170], [54, 48, 94, 143, 103, 20], [17, 110, 203, 120, 8, 97], [7, 143, 110], [13, 67, 134, 188, 61, 215]]]
 h' := ![![[182, 118, 180, 113], [61, 41, 158, 12], [88, 3, 89, 181], [31, 147, 165, 17], [220, 19, 60, 202], [96, 19, 62, 134], [0, 0, 0, 1], [0, 1]], ![[219, 1, 162, 30], [45, 71, 166, 88], [164, 171, 220, 218], [68, 144, 219, 43], [68, 120, 210, 41], [174, 46, 202, 85], [202, 194, 87, 49], [182, 118, 180, 113]], ![[184, 103, 104, 80], [216, 136, 130, 190], [184, 200, 75, 188], [117, 213, 5, 31], [67, 179, 145, 92], [162, 139, 25, 6], [208, 39, 37, 138], [219, 1, 162, 30]], ![[0, 1], [196, 198, 215, 156], [199, 72, 62, 82], [3, 165, 57, 132], [54, 128, 31, 111], [101, 19, 157, 221], [85, 213, 99, 35], [184, 103, 104, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [157, 120, 75], []]
 b := ![[], [], [36, 130, 134, 109], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 4
  hpos := by decide
  P := [62, 17, 87, 84, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4436453733, -1747771978, 6370620226, 1187884954, 2548477793]
  a := ![1, 26, 4, 10, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1711260839, -1356359424, -2131352837, -851784527, 2548477793]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 2472973441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, -105, 8, -16, 34]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![173, -105, 8, -16, 34]] 
 ![![223, 0, 0, 0, 0], ![217, 1, 0, 0, 0], ![205, 0, 1, 0, 0], ![172, 0, 0, 1, 0], ![157, 0, 0, 0, 1]] where
  M :=![![![173, -105, 8, -16, 34], ![-136, 81, -6, 14, -28], ![56, -29, -3, -6, 14], ![40, -34, 16, -11, 10], ![52, -36, 6, -1, 5]]]
  hmulB := by decide  
  f := ![![![-885, -347, 1026, 216, 770]], ![![-875, -342, 1016, 214, 762]], ![![-839, -326, 977, 206, 732]], ![![-724, -278, 848, 179, 634]], ![![-659, -253, 772, 163, 577]]]
  g := ![![![84, -105, 8, -16, 34], ![-65, 81, -6, 14, -28], ![26, -29, -3, -6, 14], ![20, -34, 16, -11, 10], ![27, -36, 6, -1, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![-885, -347, 1026, 216, 770]] ![![173, -105, 8, -16, 34]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2741355, -1654090, 116726, -248364, 536236]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![2741355, -1654090, 116726, -248364, 536236]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![75, 71, 42, 1, 0], ![110, 71, 55, 0, 1]] where
  M :=![![![2741355, -1654090, 116726, -248364, 536236], ![-2144944, 1288881, -90764, 193944, -417712], ![835424, -506198, 35745, -75852, 164120], ![744232, -448828, 31544, -67435, 145420], ![866112, -520892, 36580, -78370, 168749]]]
  hmulB := by decide  
  f := ![![![-3607, -3258, 6258, -340, -2396]], ![![9584, 6763, -20892, 15592, -6832]], ![![13664, 16770, -13733, -33068, 39944]], ![![3961, 3805, -6360, -1391, 4216]], ![![4586, 4593, -6941, -3066, 6189]]]
  g := ![![![-165715, -97326, -83458, -248364, 536236], ![128888, 75667, 64924, 193944, -417712], ![-50788, -29838, -25573, -75852, 164120], ![-44909, -26369, -22618, -67435, 145420], ![-52064, -30563, -26225, -78370, 168749]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [48, 107, 108, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 22, 190], [97, 204, 37], [0, 1]]
 g := ![![[9], [220, 62, 144], [163, 161], [74, 113], [196, 167], [97, 96, 87], [1]], ![[207, 55, 77, 166], [62, 57, 39, 172], [2, 33], [83, 33], [134, 7], [65, 192, 122, 65], [138, 86, 59, 195]], ![[219, 105, 188, 61], [15, 153, 50, 123], [109, 112], [93, 110], [210, 43], [206, 61, 177, 200], [210, 142, 147, 32]]]
 h' := ![![[22, 22, 190], [109, 224], [33, 125, 215], [162, 1, 36], [189, 150, 106], [111, 29, 103], [179, 120, 119], [0, 1]], ![[97, 204, 37], [43, 161, 111], [92, 199, 191], [85, 184, 43], [133, 145, 184], [182, 80, 190], [165, 111, 87], [22, 22, 190]], ![[0, 1], [45, 69, 116], [29, 130, 48], [99, 42, 148], [93, 159, 164], [171, 118, 161], [41, 223, 21], [97, 204, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105, 114], []]
 b := ![[], [194, 15, 181], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [48, 107, 108, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4285412, -3754022, 7830634, -1703513, -1821722]
  a := ![-1, -6, -4, 13, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1426729, 1086069, 791070, -1703513, -1821722]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3607, 3258, -6258, 340, 2396]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![3607, 3258, -6258, 340, 2396]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![209, 185, 1, 0, 0], ![152, 157, 0, 1, 0], ![9, 6, 0, 0, 1]] where
  M :=![![![3607, 3258, -6258, 340, 2396], ![-9584, -6763, 20892, -15592, 6832], ![-13664, -16770, 13733, 33068, -39944], ![84680, 76428, -147048, 8433, 55844], ![-5808, 1532, 25340, -53126, 43385]]]
  hmulB := by decide  
  f := ![![![-2741355, 1654090, -116726, 248364, -536236]], ![![2144944, -1288881, 90764, -193944, 417712]], ![![-779577, 474749, -33657, 70944, -154012]], ![![-355392, 218133, -15524, 32465, -70804]], ![![-55809, 33808, -2390, 5066, -10963]]]
  g := ![![![5455, 4816, -6258, 340, 2396], ![-9108, -6453, 20892, -15592, 6832], ![-33263, -33081, 13733, 33068, -39944], ![127900, 112869, -147048, 8433, 55844], ![10497, 14952, 25340, -53126, 43385]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P1 : CertificateIrreducibleZModOfList' 227 2 2 7 [164, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [184, 226], [0, 1]]
 g := ![![[93, 112], [116, 12], [134], [172], [100], [210, 136], [184, 1]], ![[44, 115], [54, 215], [134], [172], [100], [37, 91], [141, 226]]]
 h' := ![![[184, 226], [44, 79], [212, 100], [13, 208], [181, 95], [64, 217], [15, 96], [0, 1]], ![[0, 1], [52, 148], [225, 127], [149, 19], [182, 132], [40, 10], [200, 131], [184, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133]]
 b := ![[], [11, 180]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N1 : CertifiedPrimeIdeal' SI227N1 227 where
  n := 2
  hpos := by decide
  P := [164, 43, 1]
  hirr := P227P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6140, -7626, 6732, 13558, -16690]
  a := ![0, -2, 4, -26, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14642, -14456, 6732, 13558, -16690]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N1 B_one_repr
lemma NI227N1 : Nat.card (O ⧸ I227N1) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![2741355, -1654090, 116726, -248364, 536236]] ![![3607, 3258, -6258, 340, 2396]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![-227, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0, 0, 0]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![0, 0, 0, 229, 0], ![0, 0, 0, 0, 229]] where
  M :=![![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![0, 0, 0, 229, 0], ![0, 0, 0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 5 2 7 [170, 126, 108, 186, 103, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 50, 218, 19, 192], [127, 21, 127, 155, 110], [225, 89, 96, 40, 74], [209, 68, 17, 15, 82], [0, 1]]
 g := ![![[144, 175, 57, 123, 33], [143, 215, 70, 4], [19, 58, 208, 21, 173], [68, 83, 101, 202], [57, 56, 111, 218], [118, 126, 1], []], ![[93, 56, 20, 106, 119, 215, 72, 62], [129, 127, 87, 103], [33, 187, 205, 45, 131, 74, 165, 217], [178, 132, 152, 165], [216, 62, 153, 53], [200, 111, 12, 116, 166, 194, 108, 53], [80, 13, 170, 87, 97, 58, 125, 185]], ![[83, 16, 168, 145, 205, 21, 83, 54], [201, 29, 186, 171], [104, 184, 194, 109, 183, 182, 140, 66], [137, 183, 204, 76], [90, 76, 211, 225], [156, 216, 141, 12, 32, 29, 13, 2], [124, 120, 176, 164, 211, 208, 110, 52]], ![[142, 202, 156, 27, 52, 3, 201, 54], [198, 14, 84, 186], [48, 119, 92, 214, 217, 172, 105, 40], [21, 175, 158, 173], [101, 91, 145, 64], [161, 153, 41, 171, 33, 131, 162, 30], [228, 203, 130, 102, 224, 182, 45, 123]], ![[30, 68, 146, 76, 2, 227, 36, 33], [72, 213, 11, 180], [140, 108, 196, 89, 141, 98, 118, 183], [11, 23, 45, 132], [91, 6, 120, 51], [227, 122, 139, 161, 168, 27, 82, 25], [158, 207, 106, 195, 118, 63, 22, 165]]]
 h' := ![![[23, 50, 218, 19, 192], [82, 97, 10, 101, 124], [205, 30, 144, 6, 2], [39, 217, 30, 76, 33], [148, 205, 90, 202, 109], [92, 123, 64, 42, 26], [0, 0, 0, 1], [0, 1]], ![[127, 21, 127, 155, 110], [98, 188, 149, 114, 111], [68, 118, 172, 189, 164], [149, 27, 117, 27, 145], [160, 58, 139, 130, 169], [34, 24, 211, 49, 104], [170, 192, 220, 195, 155], [23, 50, 218, 19, 192]], ![[225, 89, 96, 40, 74], [177, 3, 186, 47, 149], [189, 54, 89, 76, 209], [82, 199, 110, 166, 67], [181, 26, 90, 118, 166], [67, 212, 200, 62, 15], [195, 212, 61, 10, 5], [127, 21, 127, 155, 110]], ![[209, 68, 17, 15, 82], [129, 12, 134, 97, 103], [85, 80, 186, 139, 145], [61, 92, 145, 211, 9], [215, 181, 204, 144, 33], [50, 25, 221, 6, 8], [106, 116, 73, 54, 24], [225, 89, 96, 40, 74]], ![[0, 1], [64, 158, 208, 99, 200], [25, 176, 96, 48, 167], [195, 152, 56, 207, 204], [2, 217, 164, 93, 210], [75, 74, 220, 70, 76], [177, 167, 104, 198, 45], [209, 68, 17, 15, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 23, 206, 227], [], [], []]
 b := ![[], [53, 76, 134, 145, 198], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 5
  hpos := by decide
  P := [170, 126, 108, 186, 103, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![88463855534, 105652933080, -94181461124, -195316176572, 240339325674]
  a := ![13, -6, -3, 8, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![386305046, 461366520, -411272756, -852909068, 1049516706]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 629763392149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def PBC229 : ContainsPrimesAboveP 229 ![I229N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![229, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 229 (by decide) 𝕀

instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-113201, -28074, 155276, 34215, 109596]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![-113201, -28074, 155276, 34215, 109596]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![53, 43, 161, 1, 0], ![47, 228, 204, 0, 1]] where
  M :=![![![-113201, -28074, 155276, 34215, 109596], ![-438384, -108687, 601428, 132526, 424482], ![-848964, -210434, 1164759, 256661, 822060], ![-1424928, -353158, 1955032, 430805, 1379802], ![-1248716, -309472, 1713284, 377535, 1209179]]]
  hmulB := by decide  
  f := ![![![-49, -20, 20, 77, -90]], ![![360, 305, -580, -24, 282]], ![![-564, -416, 1151, -697, 210]], ![![-337, -239, 695, -461, 168]], ![![-147, -66, 436, -616, 443]]]
  g := ![![![-30376, -113679, -118931, 34215, 109596], ![-117652, -440297, -460642, 132526, 424482], ![-227849, -852689, -892094, 256661, 822060], ![-382439, -1431213, -1497357, 430805, 1379802], ![-335148, -1254233, -1312199, 377535, 1209179]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [158, 144, 121, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 139, 61], [111, 93, 172], [0, 1]]
 g := ![![[87, 131, 183], [93, 104], [228, 170], [198, 17, 187], [31, 32], [175, 69, 195], [1]], ![[169, 146, 107, 153], [205, 104], [73, 219], [52, 80, 182, 84], [172, 26], [179, 163, 35, 61], [72, 43, 51, 39]], ![[16, 1, 60, 87], [130, 183], [108, 81], [16, 58, 97, 223], [209, 142], [25, 32, 84, 10], [127, 160, 203, 194]]]
 h' := ![![[1, 139, 61], [195, 23, 79], [207, 13, 156], [171, 39, 183], [99, 127, 113], [77, 46, 126], [75, 89, 112], [0, 1]], ![[111, 93, 172], [211, 10, 129], [100, 97, 156], [123, 162, 59], [157, 185, 82], [44, 84, 78], [42, 31, 1], [1, 139, 61]], ![[0, 1], [68, 200, 25], [77, 123, 154], [150, 32, 224], [28, 154, 38], [68, 103, 29], [126, 113, 120], [111, 93, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 2], []]
 b := ![[], [208, 99, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [158, 144, 121, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![300798, 263869, -552754, 132997, 121534]
  a := ![-1, 0, 2, -8, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-53477, -142338, -200679, 132997, 121534]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85, -55, 4, -8, 18]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![85, -55, 4, -8, 18]] 
 ![![233, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![205, 0, 1, 0, 0], ![113, 0, 0, 1, 0], ![139, 0, 0, 0, 1]] where
  M :=![![![85, -55, 4, -8, 18], ![-72, 37, -2, 6, -12], ![24, -19, 1, -2, 6], ![24, -14, 0, -3, 6], ![28, -16, 2, -3, 5]]]
  hmulB := by decide  
  f := ![![![53, -3, -86, -24, -66]], ![![5, 0, -8, -2, -6]], ![![49, -2, -79, -22, -60]], ![![29, -1, -46, -13, -36]], ![![35, -1, -56, -15, -43]]]
  g := ![![![-6, -55, 4, -8, 18], ![3, 37, -2, 6, -12], ![-2, -19, 1, -2, 6], ![-1, -14, 0, -3, 6], ![-2, -16, 2, -3, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 27, -78, 51, -18]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![37, 27, -78, 51, -18]] 
 ![![233, 0, 0, 0, 0], ![127, 1, 0, 0, 0], ![207, 0, 1, 0, 0], ![73, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![37, 27, -78, 51, -18], ![72, 97, -54, -240, 270], ![-540, -501, 907, 51, -450], ![864, 636, -1824, 1201, -432], ![552, 564, -810, -456, 823]]]
  hmulB := by decide  
  f := ![![![-15715, -4527, 22188, 4821, 15804]], ![![-8837, -2534, 12462, 2709, 8874]], ![![-14481, -4152, 20425, 4440, 14544]], ![![-5795, -1635, 8148, 1774, 5796]], ![![-2719, -753, 3810, 831, 2707]]]
  g := ![![![41, 27, -78, 51, -18], ![37, 97, -54, -240, 270], ![-495, -501, 907, 51, -450], ![955, 636, -1824, 1201, -432], ![455, 564, -810, -456, 823]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![-113201, -28074, 155276, 34215, 109596]] ![![85, -55, 4, -8, 18]]
  ![![15715, 4527, -22188, -4821, -15804]] where
 M := ![![![15715, 4527, -22188, -4821, -15804]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![15715, 4527, -22188, -4821, -15804]] ![![37, 27, -78, 51, -18]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![-233, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1, I233N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
    exact isPrimeI233N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0 ⊙ MulI233N1)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127973, -80787, 5858, -11846, 26296]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![127973, -80787, 5858, -11846, 26296]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![0, 0, 0, 239, 0], ![18, 39, 100, 97, 1]] where
  M :=![![![127973, -80787, 5858, -11846, 26296], ![-105184, 57547, -3798, 9112, -18484], ![36968, -26895, 2095, -3668, 8852], ![34888, -21762, 1560, -3219, 7090], ![41964, -23798, 1622, -3699, 7669]]]
  hmulB := by decide  
  f := ![![![627, 155, -860, -190, -608]], ![![2432, 603, -3338, -732, -2356]], ![![4712, 1171, -6465, -1428, -4552]], ![![7888, 1946, -10816, -2395, -7658]], ![![5646, 1397, -7744, -1712, -5471]]]
  g := ![![![-1445, -4629, -10978, -10722, 26296], ![952, 3257, 7718, 7540, -18484], ![-512, -1557, -3695, -3608, 8852], ![-388, -1248, -2960, -2891, 7090], ![-402, -1351, -3202, -3128, 7669]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 4 2 7 [159, 29, 236, 19, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [113, 133, 201, 99], [127, 50, 142, 125], [219, 55, 135, 15], [0, 1]]
 g := ![![[100, 7, 67, 36], [204, 71, 33, 33], [135, 154, 85, 220], [24, 102, 68, 101], [29, 216, 30], [168, 125, 220, 1], []], ![[141, 133, 78, 16, 183, 64], [80, 159, 12, 168, 96, 186], [217, 200, 209, 115, 24, 109], [118, 109, 174, 238, 162, 31], [182, 202, 155], [192, 177, 12, 151, 87, 180], [212, 197, 154, 107, 73, 198]], ![[218, 71, 157, 191, 36, 216], [16, 119, 28, 25, 225, 101], [124, 36, 216, 163, 62, 216], [27, 61, 72, 152, 122, 170], [160, 4, 30], [31, 178, 174, 105, 203, 163], [181, 3, 165, 120, 16, 17]], ![[133, 37, 209, 190, 130, 62], [71, 1, 95, 114, 140, 142], [11, 113, 171, 112, 98, 4], [110, 236, 82, 101, 52, 8], [66, 172, 202], [153, 181, 38, 94, 105, 155], [201, 161, 76, 177, 232, 29]]]
 h' := ![![[113, 133, 201, 99], [68, 116, 37, 233], [45, 104, 162, 64], [8, 63, 2, 170], [198, 206, 11, 36], [56, 109, 139, 204], [0, 0, 0, 1], [0, 1]], ![[127, 50, 142, 125], [215, 122, 167, 104], [219, 107, 173, 84], [229, 118, 107, 181], [52, 155, 13, 69], [166, 26, 58, 91], [45, 120, 217, 211], [113, 133, 201, 99]], ![[219, 55, 135, 15], [118, 59, 230, 135], [10, 23, 126, 102], [64, 71, 29, 135], [200, 219, 57, 209], [211, 111, 183, 204], [54, 202, 61, 152], [127, 50, 142, 125]], ![[0, 1], [173, 181, 44, 6], [70, 5, 17, 228], [152, 226, 101, 231], [222, 137, 158, 164], [34, 232, 98, 218], [193, 156, 200, 114], [219, 55, 135, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [65, 115, 184], []]
 b := ![[], [], [88, 18, 63, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 4
  hpos := by decide
  P := [159, 29, 236, 19, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1338196096, -312619050, 3717941061, -5224251872, 4364323169]
  a := ![3, 10, 7, -15, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-334292942, -713477919, -1810520401, -1793153135, 4364323169]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 3262808641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-627, -155, 860, 190, 608]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-627, -155, 860, 190, 608]] 
 ![![239, 0, 0, 0, 0], ![133, 1, 0, 0, 0], ![118, 0, 1, 0, 0], ![93, 0, 0, 1, 0], ![116, 0, 0, 0, 1]] where
  M :=![![![-627, -155, 860, 190, 608], ![-2432, -603, 3338, 732, 2356], ![-4712, -1171, 6465, 1428, 4552], ![-7888, -1946, 10816, 2395, 7658], ![-6924, -1714, 9502, 2085, 6715]]]
  hmulB := by decide  
  f := ![![![-127973, 80787, -5858, 11846, -26296]], ![![-70775, 44716, -3244, 6554, -14556]], ![![-63338, 39999, -2901, 5864, -13020]], ![![-49943, 31527, -2286, 4623, -10262]], ![![-62288, 39310, -2850, 5765, -12795]]]
  g := ![![![-710, -155, 860, 190, 608], ![-2751, -603, 3338, 732, 2356], ![-5325, -1171, 6465, 1428, 4552], ![-8939, -1946, 10816, 2395, 7658], ![-7837, -1714, 9502, 2085, 6715]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![127973, -80787, 5858, -11846, 26296]] ![![-627, -155, 860, 190, 608]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![-239, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![719, 596, -1366, 477, 108]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![719, 596, -1366, 477, 108]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![22, 111, 1, 0, 0], ![209, 102, 0, 1, 0], ![125, 111, 0, 0, 1]] where
  M :=![![![719, 596, -1366, 477, 108], ![-432, 91, 1840, -3794, 3078], ![-6156, -6168, 9325, 4095, -8304], ![16824, 13938, -32000, 11279, 2442], ![4124, 5032, -4192, -9809, 11881]]]
  hmulB := by decide  
  f := ![![![-147673, 117722, -9566, 15395, -39006]], ![![156024, -48437, 1408, -10916, 14358]], ![![58262, -11341, -247, -3601, 2976]], ![![-62201, 81718, -7710, 8748, -27792]], ![![-4977, 38849, -4318, 2976, -13649]]]
  g := ![![![-342, 380, -1366, 477, 108], ![1524, -659, 1840, -3794, 3078], ![-121, -2229, 9325, 4095, -8304], ![-8057, 8898, -32000, 11279, 2442], ![2744, 631, -4192, -9809, 11881]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [142, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [208, 240], [0, 1]]
 g := ![![[80, 216], [45], [145], [159], [162, 128], [80, 48], [208, 1]], ![[182, 25], [45], [145], [159], [35, 113], [183, 193], [175, 240]]]
 h' := ![![[208, 240], [189, 79], [109, 173], [148, 77], [132, 221], [208, 65], [107, 224], [0, 1]], ![[0, 1], [233, 162], [184, 68], [17, 164], [69, 20], [232, 176], [186, 17], [208, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [210]]
 b := ![[], [166, 105]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [142, 33, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2136, -1735, 3784, 245, -844]
  a := ![1, 4, 2, -6, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-129, -1465, 3784, 245, -844]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-276847, 167066, -12176, 25004, -54414]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![-276847, 167066, -12176, 25004, -54414]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![41, 68, 1, 0, 0], ![104, 217, 0, 1, 0], ![202, 152, 0, 0, 1]] where
  M :=![![![-276847, 167066, -12176, 25004, -54414], ![217656, -130187, 7648, -19946, 41196], ![-82392, 51510, -6599, 6996, -18642], ![-71544, 46236, -8240, 5699, -18252], ![-84232, 53494, -8136, 6944, -20201]]]
  hmulB := by decide  
  f := ![![![257, -94, -1120, 2616, -2214]], ![![8856, 8797, -13472, -5258, 11268]], ![![2449, 2388, -3815, -1096, 2784]], ![![8104, 7865, -12720, -3351, 8976]], ![![5938, 5594, -9672, -1116, 5347]]]
  g := ![![![35741, 15934, -12176, 25004, -54414], ![-26320, -10721, 7648, -19946, 41196], ![13387, 7534, -6599, 6996, -18642], ![13944, 8897, -8240, 5699, -18252], ![14970, 9006, -8136, 6944, -20201]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P1 : CertificateIrreducibleZModOfList' 241 2 2 7 [198, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [204, 240], [0, 1]]
 g := ![![[72, 94], [128], [160], [1], [75, 87], [105, 192], [204, 1]], ![[209, 147], [128], [160], [1], [230, 154], [231, 49], [167, 240]]]
 h' := ![![[204, 240], [157, 217], [14, 65], [72, 147], [92, 1], [177, 91], [96, 207], [0, 1]], ![[0, 1], [81, 24], [19, 176], [176, 94], [55, 240], [184, 150], [149, 34], [204, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [175]]
 b := ![[], [233, 208]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N1 : CertifiedPrimeIdeal' SI241N1 241 where
  n := 2
  hpos := by decide
  P := [198, 37, 1]
  hirr := P241P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![34, -342, 456, 308, -554]
  a := ![4, -1, -1, 3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![254, -58, 456, 308, -554]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N1 B_one_repr
lemma NI241N1 : Nat.card (O ⧸ I241N1) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 6, -8, 3, 0]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![-1, 6, -8, 3, 0]] 
 ![![241, 0, 0, 0, 0], ![124, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![137, 0, 0, 1, 0], ![65, 0, 0, 0, 1]] where
  M :=![![![-1, 6, -8, 3, 0], ![0, -3, 12, -22, 18], ![-36, -34, 51, 25, -48], ![96, 82, -184, 61, 18], ![20, 28, -20, -57, 67]]]
  hmulB := by decide  
  f := ![![![-5257, -1364, 7064, 1553, 5010]], ![![-2788, -723, 3748, 824, 2658]], ![![-684, -176, 923, 203, 654]], ![![-3257, -842, 4384, 964, 3108]], ![![-1653, -426, 2228, 490, 1579]]]
  g := ![![![-4, 6, -8, 3, 0], ![8, -3, 12, -22, 18], ![11, -34, 51, 25, -48], ![-63, 82, -184, 61, 18], ![2, 28, -20, -57, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![719, 596, -1366, 477, 108]] ![![-276847, 167066, -12176, 25004, -54414]]
  ![![-6089, -1734, 8730, 1899, 6210]] where
 M := ![![![-6089, -1734, 8730, 1899, 6210]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![-6089, -1734, 8730, 1899, 6210]] ![![-1, 6, -8, 3, 0]]
  ![![241, 0, 0, 0, 0]] where
 M := ![![![-1687, 1446, -482, 0, 0]]]
 hmul := by decide  
 g := ![![![![-7, 6, -2, 0, 0]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1, I241N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
    exact isPrimeI241N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0 ⊙ MulI241N1)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6505, 3041, -176, 527, -960]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![-6505, 3041, -176, 527, -960]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![29, 6, 245, 1, 0], ![235, 60, 239, 0, 1]] where
  M :=![![![-6505, 3041, -176, 527, -960], ![3840, -3707, 322, -446, 1242], ![-2484, 393, 19, 147, -96], ![-1728, 864, -56, 143, -276], ![-1672, 1366, -114, 176, -455]]]
  hmulB := by decide  
  f := ![![![-11, -11, 22, -9, -6]], ![![24, 5, -58, 68, -66]], ![![132, 117, -193, -93, 138]], ![![127, 112, -185, -91, 132]], ![![121, 102, -177, -80, 109]]]
  g := ![![![812, 229, 399, 527, -960], ![-1096, -301, -746, -446, 1242], ![63, 21, -52, 147, -96], ![235, 66, 123, 143, -276], ![399, 110, 261, 176, -455]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [238, 129, 180, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 126, 1], [22, 124, 250], [0, 1]]
 g := ![![[81, 10, 103], [69, 241, 67], [49, 84], [71, 137, 52], [134, 116, 20], [8, 241, 21], [1]], ![[27, 132, 48, 48], [172, 158, 170, 100], [240, 214], [115, 118, 67, 154], [222, 14, 91, 114], [250, 136, 63, 52], [156, 209, 198, 1]], ![[47, 177, 60, 182], [121, 151, 92, 32], [150, 155], [181, 116, 106, 242], [105, 123, 177, 226], [115, 109, 232, 236], [84, 36, 50, 250]]]
 h' := ![![[49, 126, 1], [144, 40, 75], [170, 212, 148], [170, 126, 109], [236, 58, 110], [104, 11, 32], [13, 122, 71], [0, 1]], ![[22, 124, 250], [124, 77, 53], [175, 98, 241], [103, 186, 88], [174, 213, 144], [250, 75, 214], [201, 125, 141], [49, 126, 1]], ![[0, 1], [38, 134, 123], [221, 192, 113], [167, 190, 54], [183, 231, 248], [183, 165, 5], [194, 4, 39], [22, 124, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 181], []]
 b := ![[], [147, 33, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [238, 129, 180, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11643100, -22759044, 76602018, -252184941, 49592370]
  a := ![7, -46, -24, 25, -119]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17247811, -5917098, 199240383, -252184941, 49592370]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 11, -22, 9, 6]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![11, 11, -22, 9, 6]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![61, 6, 1, 0, 0], ![136, 246, 0, 1, 0], ![147, 115, 0, 0, 1]] where
  M :=![![![11, 11, -22, 9, 6], ![-24, -5, 58, -68, 66], ![-132, -117, 193, 93, -138], ![288, 264, -560, 203, 108], ![32, 76, -10, -182, 253]]]
  hmulB := by decide  
  f := ![![![6505, -3041, 176, -527, 960]], ![![-3840, 3707, -322, 446, -1242]], ![![1499, -652, 35, -118, 204]], ![![-232, 1982, -220, 151, -696]], ![![2057, -88, -44, -105, -5]]]
  g := ![![![-3, -11, -22, 9, 6], ![-16, 35, 58, -68, 66], ![-17, -33, 193, 93, -138], ![-36, -234, -560, 203, 108], ![-47, 63, -10, -182, 253]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P1 : CertificateIrreducibleZModOfList' 251 2 2 7 [133, 173, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 250], [0, 1]]
 g := ![![[90, 17], [151, 17], [69], [62, 36], [209, 112], [76, 58], [78, 1]], ![[161, 234], [222, 234], [69], [109, 215], [160, 139], [82, 193], [156, 250]]]
 h' := ![![[78, 250], [248, 206], [224, 45], [37, 128], [64, 6], [183, 83], [168, 178], [0, 1]], ![[0, 1], [1, 45], [220, 206], [232, 123], [30, 245], [131, 168], [247, 73], [78, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117]]
 b := ![[], [103, 184]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N1 : CertifiedPrimeIdeal' SI251N1 251 where
  n := 2
  hpos := by decide
  P := [133, 173, 1]
  hirr := P251P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16613, -12904, 26472, 481, -5268]
  a := ![1, -12, -7, 9, -36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3675, 1258, 26472, 481, -5268]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N1 B_one_repr
lemma NI251N1 : Nat.card (O ⧸ I251N1) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![-6505, 3041, -176, 527, -960]] ![![11, 11, -22, 9, 6]]
  ![![251, 0, 0, 0, 0]] where
 M := ![![![-251, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0)


lemma PB1321I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB1321I5 : PrimesBelowBoundCertificateInterval O 197 251 1321 where
  m := 9
  g := ![2, 4, 2, 2, 1, 3, 2, 3, 2]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB1321I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1, I211N2, I211N3]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
    · exact ![I229N0]
    · exact ![I233N0, I233N1, I233N2]
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1, I241N2]
    · exact ![I251N0, I251N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![7880599, 39601]
    · exact ![44521, 211, 211, 211]
    · exact ![2472973441, 223]
    · exact ![11697083, 51529]
    · exact ![629763392149]
    · exact ![12649337, 233, 233]
    · exact ![3262808641, 239]
    · exact ![58081, 58081, 241]
    · exact ![15813251, 63001]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
      exact NI211N2
      exact NI211N3
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
      exact NI233N2
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
      exact NI241N2
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
  β := ![I211N1, I211N2, I211N3, I223N1, I233N1, I233N2, I239N1, I241N2]
  Il := ![[], [I211N1, I211N2, I211N3], [I223N1], [], [], [I233N1, I233N2], [I239N1], [I241N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
