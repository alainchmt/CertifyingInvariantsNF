
import IdealArithmetic.Examples.NF5_3_112500000_1.RI5_3_112500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![135, 16, -20, 0, 2]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![135, 16, -20, 0, 2]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![55, 65, 101, 1, 0], ![196, 8, 247, 0, 1]] where
  M :=![![![135, 16, -20, 0, 2], ![8, 173, -4, -112, 0], ![-4, -50, 169, 100, -112], ![-434, -140, -48, 9, 70], ![354, -100, -164, 52, 79]]]
  hmulB := by decide  
  f := ![![![3, -16, -12, -8, -10]], ![![-264, -83, -76, -96, -16]], ![![-268, -214, -175, -164, -96]], ![![-173, -109, -91, -91, -44]], ![![-266, -222, -181, -168, -101]]]
  g := ![![![-1, 0, -2, 0, 2], ![24, 29, 44, -112, 0], ![64, -22, 69, 100, -112], ![-57, -5, -71, 9, 70], ![-70, -16, -97, 52, 79]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [26, 98, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 214, 194], [128, 42, 63], [0, 1]]
 g := ![![[86, 199, 58], [228, 1], [251, 26], [125, 98], [166, 84], [42, 11], [205, 1], []], ![[206, 9, 120, 177], [48, 58], [153, 228], [208, 15], [112, 205], [221, 121], [203, 222], [4, 114]], ![[193, 18, 28, 186], [47, 236], [221, 137], [43, 158], [26, 34], [232, 153], [242, 50], [135, 114]]]
 h' := ![![[77, 214, 194], [127, 8, 217], [12, 140, 1], [65, 152, 138], [105, 10, 94], [56, 96, 37], [67, 187, 36], [0, 0, 1], [0, 1]], ![[128, 42, 63], [71, 169, 129], [169, 193, 217], [158, 188, 75], [244, 202, 234], [154, 107, 132], [62, 4, 11], [171, 45, 42], [77, 214, 194]], ![[0, 1], [191, 80, 168], [223, 181, 39], [217, 174, 44], [43, 45, 186], [125, 54, 88], [195, 66, 210], [24, 212, 214], [128, 42, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96, 252], []]
 b := ![[], [21, 15, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [26, 98, 52, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13144698, -6751800, -5936899, -6320578, -2399218]
  a := ![-9, -7, -7, -10, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3131260, 1647002, 4766725, -6320578, -2399218]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 16974593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-152, -10, -12, -38, 17]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![-152, -10, -12, -38, 17]] 
 ![![257, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![95, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![99, 0, 0, 0, 1]] where
  M :=![![![-152, -10, -12, -38, 17], ![384, -25, -10, 72, -76], ![-922, -109, -111, -254, 72], ![673, -34, -10, 131, -127], ![-1053, -186, -176, -320, 42]]]
  hmulB := by decide  
  f := ![![![-1282, -638, 84, 276, 55]], ![![-84, -47, 2, 20, 6]], ![![-452, -221, 27, 94, 21]], ![![-577, -286, 42, 125, 22]], ![![-527, -260, 40, 114, 19]]]
  g := ![![![15, -10, -12, -38, 17], ![4, -25, -10, 72, -76], ![131, -109, -111, -254, 72], ![-1, -34, -10, 131, -127], ![201, -186, -176, -320, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1

def I257N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12, 2, 0, 0, -1]] i)))

def SI257N2: IdealEqSpanCertificate' Table ![![12, 2, 0, 0, -1]] 
 ![![257, 0, 0, 0, 0], ![149, 1, 0, 0, 0], ![79, 0, 1, 0, 0], ![93, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![12, 2, 0, 0, -1], ![-24, 3, 2, -4, 0], ![2, -15, 5, 10, -4], ![-23, 0, -6, -5, 5], ![43, 10, -8, -6, 0]]]
  hmulB := by decide  
  f := ![![![-1958, -58, -88, -462, 277]], ![![-1110, -33, -50, -262, 157]], ![![-644, -19, -29, -152, 91]], ![![-665, -20, -30, -157, 94]], ![![-263, -8, -12, -62, 37]]]
  g := ![![![-1, 2, 0, 0, -1], ![-1, 3, 2, -4, 0], ![4, -15, 5, 10, -4], ![3, 0, -6, -5, 5], ![-1, 10, -8, -6, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N2 : Nat.card (O ⧸ I257N2) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N2)

lemma isPrimeI257N2 : Ideal.IsPrime I257N2 := prime_ideal_of_norm_prime hp257.out _ NI257N2
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![135, 16, -20, 0, 2]] ![![-152, -10, -12, -38, 17]]
  ![![1958, 58, 88, 462, -277]] where
 M := ![![![1958, 58, 88, 462, -277]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI257N1 : IdealMulLeCertificate' Table 
  ![![1958, 58, 88, 462, -277]] ![![12, 2, 0, 0, -1]]
  ![![257, 0, 0, 0, 0]] where
 M := ![![![-257, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1, I257N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
    exact isPrimeI257N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0 ⊙ MulI257N1)
instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30, 158, 28, -86, -23]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![30, 158, 28, -86, -23]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![73, 26, 114, 1, 0], ![206, 56, 190, 0, 1]] where
  M :=![![![30, 158, 28, -86, -23], ![-496, -291, 326, 248, -172], ![-1738, -1061, -137, 386, 248], ![1433, 422, -226, -159, 25], ![1755, 1430, -168, -752, -48]]]
  hmulB := by decide  
  f := ![![![-1168, -586, -500, -536, -203]], ![![-5872, -3031, -2578, -2740, -1072]], ![![-15442, -7841, -6681, -7138, -2740]], ![![-7631, -3878, -3304, -3529, -1356]], ![![-13429, -6824, -5814, -6210, -2386]]]
  g := ![![![42, 14, 54, -86, -23], ![64, 11, 18, 248, -172], ![-308, -95, -347, 386, 248], ![30, 12, 50, -159, 25], ![253, 90, 360, -752, -48]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [200, 17, 112, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 129, 197], [72, 133, 66], [0, 1]]
 g := ![![[43, 56, 70], [138, 221, 72], [104, 247, 1], [142, 133], [255, 198], [48, 204], [151, 1], []], ![[72, 64, 196, 141], [150, 67, 68, 199], [44, 160, 210, 219], [228, 143], [30, 99], [15, 32], [68, 68], [60, 148]], ![[203, 171, 154, 93], [157, 188, 22, 62], [79, 60, 260, 39], [197, 203], [55, 83], [118, 121], [184, 72], [191, 148]]]
 h' := ![![[79, 129, 197], [15, 8, 99], [240, 79, 134], [15, 215, 262], [96, 181, 213], [52, 232, 143], [45, 126, 166], [0, 0, 1], [0, 1]], ![[72, 133, 66], [164, 20, 15], [105, 113, 247], [141, 101, 142], [158, 44, 77], [149, 33, 25], [16, 209, 86], [27, 19, 133], [79, 129, 197]], ![[0, 1], [45, 235, 149], [184, 71, 145], [119, 210, 122], [190, 38, 236], [12, 261, 95], [176, 191, 11], [122, 244, 129], [72, 133, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [164, 154], []]
 b := ![[], [234, 8, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [200, 17, 112, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3741372870, -1936668236, -1680814364, -1785551276, -695158108]
  a := ![-53, -53, -57, -58, -104]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1025880002, 317173076, 1269779740, -1785551276, -695158108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 18191447 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1168, -586, -500, -536, -203]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![-1168, -586, -500, -536, -203]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![171, 185, 1, 0, 0], ![6, 218, 0, 1, 0], ![74, 262, 0, 0, 1]] where
  M :=![![![-1168, -586, -500, -536, -203], ![-5872, -3031, -2578, -2740, -1072], ![-15442, -7841, -6681, -7138, -2740], ![-8629, -4456, -3790, -4027, -1577], ![-28407, -14470, -12324, -13154, -5068]]]
  hmulB := by decide  
  f := ![![![30, 158, 28, -86, -23]], ![![-496, -291, 326, 248, -172]], ![![-336, -106, 247, 120, -135]], ![![-405, -236, 270, 203, -143]], ![![-479, -240, 332, 220, -178]]]
  g := ![![![390, 996, -500, -536, -203], ![2018, 5141, -2578, -2740, -1072], ![5219, 13316, -6681, -7138, -2740], ![2967, 7558, -3790, -4027, -1577], ![9631, 24566, -12324, -13154, -5068]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P1 : CertificateIrreducibleZModOfList' 263 2 2 8 [109, 201, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 262], [0, 1]]
 g := ![![[219, 111], [258, 187], [103, 108], [51], [145], [179], [162], [1]], ![[0, 152], [17, 76], [224, 155], [51], [145], [179], [162], [1]]]
 h' := ![![[62, 262], [19, 233], [82, 72], [143, 125], [210, 180], [32, 150], [9, 210], [154, 62], [0, 1]], ![[0, 1], [0, 30], [75, 191], [3, 138], [61, 83], [127, 113], [142, 53], [53, 201], [62, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [90, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N1 : CertifiedPrimeIdeal' SI263N1 263 where
  n := 2
  hpos := by decide
  P := [109, 201, 1]
  hirr := P263P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3310, 1495, 1318, 1152, -443]
  a := ![-4, -3, -4, -6, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-746, -1435, 1318, 1152, -443]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N1 B_one_repr
lemma NI263N1 : Nat.card (O ⧸ I263N1) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![30, 158, 28, -86, -23]] ![![-1168, -586, -500, -536, -203]]
  ![![263, 0, 0, 0, 0]] where
 M := ![![![263, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5509, 228, -380, -866, 648]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![-5509, 228, -380, -866, 648]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![220, 104, 113, 1, 0], ![266, 141, 221, 0, 1]] where
  M :=![![![-5509, 228, -380, -866, 648], ![14792, -163, 992, 2044, -1732], ![-19792, 128, -903, -2532, 2044], ![18774, -650, 1016, 2777, -2030], ![-11966, 564, -1144, -2034, 1613]]]
  hmulB := by decide  
  f := ![![![-1645, 16, -28, -354, 268]], ![![6376, 441, 512, 1612, -708]], ![![-7984, 552, 245, -1492, 1612]], ![![-2194, 418, 281, -283, 618]], ![![-4868, 705, 445, -734, 1225]]]
  g := ![![![47, -4, -170, -866, 648], ![96, 117, 568, 2044, -1732], ![-24, -92, -619, -2532, 2044], ![-194, -12, 505, 2777, -2030], ![24, -57, -475, -2034, 1613]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [231, 28, 222, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 6, 138], [261, 262, 131], [0, 1]]
 g := ![![[51, 54, 185], [43, 180], [55, 250, 224], [84, 102, 25], [82, 45], [104, 34], [47, 1], []], ![[132, 183, 10, 1], [253, 246], [130, 46, 107, 244], [5, 230, 202, 25], [226, 81], [87, 118], [54, 49], [147, 214]], ![[114, 22, 265, 11], [29, 54], [5, 140, 122, 143], [229, 63, 168, 67], [165, 47], [89, 96], [187, 36], [154, 214]]]
 h' := ![![[55, 6, 138], [98, 66, 67], [207, 110, 51], [233, 243, 208], [8, 188, 264], [180, 177, 109], [172, 67, 29], [0, 0, 1], [0, 1]], ![[261, 262, 131], [163, 34, 31], [223, 264, 28], [234, 17, 67], [111, 75, 155], [20, 184, 260], [178, 161, 166], [3, 103, 262], [55, 6, 138]], ![[0, 1], [243, 169, 171], [32, 164, 190], [25, 9, 263], [128, 6, 119], [160, 177, 169], [116, 41, 74], [267, 166, 6], [261, 262, 131]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 129], []]
 b := ![[], [190, 110, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [231, 28, 222, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![653475311, 346861142, 305569746, 325444291, 135046960]
  a := ![28, 32, 24, 19, 64]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-397274201, -195319578, -246524213, 325444291, 135046960]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1645, 16, -28, -354, 268]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![-1645, 16, -28, -354, 268]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![15, 200, 1, 0, 0], ![161, 142, 0, 1, 0], ![183, 68, 0, 0, 1]] where
  M :=![![![-1645, 16, -28, -354, 268], ![6376, 441, 512, 1612, -708], ![-7984, 552, 245, -1492, 1612], ![10802, 682, 816, 2701, -1242], ![-6474, 1216, 816, -842, 1813]]]
  hmulB := by decide  
  f := ![![![-5509, 228, -380, -866, 648]], ![![14792, -163, 992, 2044, -1732]], ![![10617, -108, 713, 1462, -1244]], ![![4581, 48, 300, 571, -534]], ![![-53, 116, -12, -80, 9]]]
  g := ![![![25, 140, -28, -354, 268], ![-488, -1051, 512, 1612, -708], ![-247, 200, 245, -1492, 1612], ![-777, -1716, 816, 2701, -1242], ![-799, -616, 816, -842, 1813]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P1 : CertificateIrreducibleZModOfList' 269 2 2 8 [175, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [200, 268], [0, 1]]
 g := ![![[191, 62], [21], [151, 143], [185, 154], [256], [143], [188], [1]], ![[217, 207], [21], [237, 126], [50, 115], [256], [143], [188], [1]]]
 h' := ![![[200, 268], [25, 84], [206, 212], [174, 120], [144, 31], [57, 16], [146, 149], [94, 200], [0, 1]], ![[0, 1], [147, 185], [104, 57], [233, 149], [157, 238], [29, 253], [87, 120], [13, 69], [200, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124]]
 b := ![[], [256, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N1 : CertifiedPrimeIdeal' SI269N1 269 where
  n := 2
  hpos := by decide
  P := [175, 69, 1]
  hirr := P269P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12311, 16065, 11570, 10252, 11174]
  a := ![-7, -18, -1, 12, -32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14337, -16779, 11570, 10252, 11174]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N1 B_one_repr
lemma NI269N1 : Nat.card (O ⧸ I269N1) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![-5509, 228, -380, -866, 648]] ![![-1645, 16, -28, -354, 268]]
  ![![269, 0, 0, 0, 0]] where
 M := ![![![269, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC269 : ContainsPrimesAboveP 269 ![I269N0, I269N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 269 (by decide) (𝕀 ⊙ MulI269N0)
instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5359, 799, -2860, -904, 1444]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![5359, 799, -2860, -904, 1444]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![0, 0, 0, 271, 0], ![249, 146, 248, 136, 1]] where
  M :=![![![5359, 799, -2860, -904, 1444], ![28936, 20311, -1234, -9576, -1808], ![-22930, 2161, 17269, 2258, -9576], ![-21868, -18289, -1724, 8085, 3162], ![-116, -20245, -17958, 5940, 12151]]]
  hmulB := by decide  
  f := ![![![-851, -23, -34, -204, 124]], ![![2908, 95, 134, 700, -408]], ![![-4762, -99, -179, -1114, 700]], ![![5096, 157, 234, 1215, -714]], ![![-1033, 18, -6, -224, 179]]]
  g := ![![![-1307, -775, -1332, -728, 1444], ![1768, 1049, 1650, 872, -1808], ![8714, 5167, 8827, 4814, -9576], ![-2986, -1771, -2900, -1557, 3162], ![-11165, -6621, -11186, -6076, 12151]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 4 2 8 [16, 15, 204, 132, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 186, 83, 19], [203, 207, 189, 160], [121, 148, 270, 92], [0, 1]]
 g := ![![[164, 246, 253, 252], [7, 14, 241, 185], [69, 77, 28, 41], [239, 178, 123, 250], [64, 255, 141], [35, 207, 80], [1], []], ![[217, 157, 158, 90, 258, 183], [256, 218, 225, 267, 270, 47], [193, 96, 217, 229, 192, 108], [73, 268, 95, 40, 189, 145], [19, 239, 164], [212, 259, 31], [137, 241, 2], [15, 217, 90]], ![[216, 211, 98, 251, 265, 124], [110, 185, 5, 110, 152, 164], [113, 248, 201, 221, 49, 241], [214, 85, 158, 53, 236, 128], [157, 203, 10], [39, 60, 98], [210, 135, 178], [188, 217, 126]], ![[139, 61, 52, 76, 167, 54], [74, 232, 104, 147, 166, 73], [167, 235, 217, 30, 235, 48], [53, 228, 259, 186, 193, 93], [152, 232, 128], [242, 254, 180], [230, 21, 28], [78, 172, 63]]]
 h' := ![![[86, 186, 83, 19], [159, 71, 135, 87], [251, 259, 0, 105], [241, 231, 167, 224], [65, 264, 68, 122], [238, 166, 106, 236], [255, 256, 67, 139], [0, 0, 1], [0, 1]], ![[203, 207, 189, 160], [252, 97, 161, 229], [177, 82, 54, 207], [214, 171, 216, 211], [130, 242, 146, 48], [200, 227, 58, 177], [152, 81, 269, 64], [110, 111, 196, 96], [86, 186, 83, 19]], ![[121, 148, 270, 92], [230, 191, 163, 52], [21, 210, 219, 89], [270, 221, 103, 82], [251, 31, 131, 230], [253, 250, 1, 84], [263, 108, 196, 141], [261, 244, 80, 146], [203, 207, 189, 160]], ![[0, 1], [215, 183, 83, 174], [5, 262, 269, 141], [264, 190, 56, 25], [249, 5, 197, 142], [28, 170, 106, 45], [102, 97, 10, 198], [114, 187, 265, 29], [121, 148, 270, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [42, 233, 64], []]
 b := ![[], [], [245, 73, 162, 108], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 4
  hpos := by decide
  P := [16, 15, 204, 132, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6588658724, -79151154, -4187218, -1526967498, 755127726]
  a := ![-12, 18, -14, -54, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-718138238, -407113650, -691054846, -384591654, 755127726]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 5393580481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-851, -23, -34, -204, 124]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![-851, -23, -34, -204, 124]] 
 ![![271, 0, 0, 0, 0], ![270, 1, 0, 0, 0], ![135, 0, 1, 0, 0], ![68, 0, 0, 1, 0], ![238, 0, 0, 0, 1]] where
  M :=![![![-851, -23, -34, -204, 124], ![2908, 95, 134, 700, -408], ![-4762, -99, -179, -1114, 700], ![5096, 157, 234, 1215, -714], ![-4692, -65, -156, -1076, 705]]]
  hmulB := by decide  
  f := ![![![5359, 799, -2860, -904, 1444]], ![![5446, 871, -2854, -936, 1432]], ![![2585, 406, -1361, -442, 684]], ![![1264, 133, -724, -197, 374]], ![![4706, 627, -2578, -772, 1313]]]
  g := ![![![-21, -23, -34, -204, 124], ![32, 95, 134, 700, -408], ![-165, -99, -179, -1114, 700], ![68, 157, 234, 1215, -714], ![-224, -65, -156, -1076, 705]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![5359, 799, -2860, -904, 1444]] ![![-851, -23, -34, -204, 124]]
  ![![271, 0, 0, 0, 0]] where
 M := ![![![271, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC271 : ContainsPrimesAboveP 271 ![I271N0, I271N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
    exact isPrimeI271N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 271 (by decide) (𝕀 ⊙ MulI271N0)
instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-352, -108, -110, -118, -29]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![-352, -108, -110, -118, -29]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![0, 0, 0, 277, 0], ![79, 147, 42, 176, 1]] where
  M :=![![![-352, -108, -110, -118, -29], ![-916, -621, -494, -540, -236], ![-3326, -1543, -1351, -1414, -540], ![-1537, -928, -740, -819, -321], ![-5671, -2870, -2482, -2592, -1022]]]
  hmulB := by decide  
  f := ![![![2, 0, -2, 0, 1]], ![![20, 13, -2, -8, 0]], ![![-2, 7, 11, 2, -8]], ![![-25, -14, 0, 3, 3]], ![![-5, -1, 0, -2, 1]]]
  g := ![![![7, 15, 4, 18, -29], ![64, 123, 34, 148, -236], ![142, 281, 77, 338, -540], ![86, 167, 46, 201, -321], ![271, 532, 146, 640, -1022]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 4 2 8 [35, 235, 87, 76, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 83, 69, 198], [136, 178, 93, 219], [5, 15, 115, 137], [0, 1]]
 g := ![![[117, 82, 82, 252], [42, 118, 52], [11, 257, 53, 141], [192, 191, 113], [231, 171, 12, 146], [271, 274, 236], [1], []], ![[127, 168, 156, 123, 64, 116], [264, 232, 81], [96, 95, 107, 42, 238, 147], [166, 189, 25], [70, 71, 233, 209, 80, 100], [97, 139, 185], [215, 78, 155], [22, 86, 147]], ![[23, 135, 173, 135, 172, 195], [73, 150, 34], [164, 235, 59, 252, 138, 77], [59, 129, 254], [137, 234, 109, 172, 84, 119], [207, 34, 71], [55, 188, 206], [23, 22, 40]], ![[100, 179, 187, 93, 86, 98], [227, 86, 19], [163, 28, 61, 42, 148, 99], [51, 24, 258], [24, 148, 202, 204, 143, 245], [13, 103, 4], [44, 86, 276], [55, 38, 210]]]
 h' := ![![[60, 83, 69, 198], [222, 43, 105, 23], [169, 262, 170, 69], [139, 221, 123, 153], [225, 123, 116, 125], [50, 237, 267, 54], [242, 42, 190, 201], [0, 0, 1], [0, 1]], ![[136, 178, 93, 219], [66, 178, 61, 33], [89, 3, 201, 9], [16, 164, 206, 72], [274, 263, 15, 5], [199, 11, 168, 54], [230, 239, 29, 49], [60, 118, 88, 102], [60, 83, 69, 198]], ![[5, 15, 115, 137], [249, 245, 187, 57], [158, 112, 63, 158], [192, 261, 81, 104], [128, 128, 50, 114], [238, 41, 238, 54], [275, 273, 164, 25], [240, 137, 211, 115], [136, 178, 93, 219]], ![[0, 1], [54, 88, 201, 164], [215, 177, 120, 41], [195, 185, 144, 225], [128, 40, 96, 33], [183, 265, 158, 115], [258, 0, 171, 2], [39, 22, 254, 60], [5, 15, 115, 137]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [197, 233, 149], []]
 b := ![[], [], [43, 116, 214, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 4
  hpos := by decide
  P := [35, 235, 87, 76, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![670286099513, 343419518973, 292988039493, 311222823939, 119734061934]
  a := ![34, 13, 25, 47, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-31728176149, -62301399225, -17096904555, -74952967785, 119734061934]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 5887339441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, -2, 0, 1]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![2, 0, -2, 0, 1]] 
 ![![277, 0, 0, 0, 0], ![202, 1, 0, 0, 0], ![96, 0, 1, 0, 0], ![94, 0, 0, 1, 0], ![194, 0, 0, 0, 1]] where
  M :=![![![2, 0, -2, 0, 1], ![20, 13, -2, -8, 0], ![-2, 7, 11, 2, -8], ![-25, -14, 0, 3, 3], ![1, -18, -10, 10, 6]]]
  hmulB := by decide  
  f := ![![![-352, -108, -110, -118, -29]], ![![-260, -81, -82, -88, -22]], ![![-134, -43, -43, -46, -12]], ![![-125, -40, -40, -43, -11]], ![![-267, -86, -86, -92, -24]]]
  g := ![![![0, 0, -2, 0, 1], ![-6, 13, -2, -8, 0], ![-4, 7, 11, 2, -8], ![7, -14, 0, 3, 3], ![9, -18, -10, 10, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![-352, -108, -110, -118, -29]] ![![2, 0, -2, 0, 1]]
  ![![277, 0, 0, 0, 0]] where
 M := ![![![277, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC277 : ContainsPrimesAboveP 277 ![I277N0, I277N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
    exact isPrimeI277N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 277 (by decide) (𝕀 ⊙ MulI277N0)
instance hp281 : Fact (Nat.Prime 281) := {out := by norm_num}

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52, -30, -24, -18, -3]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![-52, -30, -24, -18, -3]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![216, 123, 195, 1, 0], ![220, 115, 243, 0, 1]] where
  M :=![![![-52, -30, -24, -18, -3], ![-120, -73, -114, -120, -36], ![-546, -225, -223, -294, -120], ![-375, -210, -126, -121, -63], ![-1197, -642, -468, -444, -166]]]
  hmulB := by decide  
  f := ![![![-422, 6, -24, -72, 51]], ![![1176, -11, 66, 204, -144]], ![![-1662, 9, -89, -294, 204]], ![![-957, 6, -51, -169, 117]], ![![-1291, 8, -69, -228, 158]]]
  g := ![![![16, 9, 15, -18, -3], ![120, 67, 114, -120, -36], ![318, 177, 307, -294, -120], ![141, 78, 138, -121, -63], ![467, 260, 450, -444, -166]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 3 2 8 [219, 253, 275, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 78, 31], [174, 202, 250], [0, 1]]
 g := ![![[97, 122, 236], [166, 163], [256, 201], [220, 149, 170], [255, 86, 68], [64, 162], [6, 1], []], ![[41, 32, 53, 218], [239, 125], [183, 80], [77, 239, 255, 249], [164, 18, 47, 246], [187, 209], [94, 59], [205, 118]], ![[12, 36, 248, 56], [55, 223], [223, 50], [255, 252, 245, 90], [229, 123, 115, 34], [244, 17], [105, 183], [267, 118]]]
 h' := ![![[113, 78, 31], [40, 45, 123], [198, 114, 238], [152, 80, 117], [74, 126, 156], [166, 25, 61], [91, 230, 64], [0, 0, 1], [0, 1]], ![[174, 202, 250], [272, 159, 108], [176, 64, 187], [114, 30, 262], [241, 143, 12], [189, 247, 171], [242, 104, 107], [189, 55, 202], [113, 78, 31]], ![[0, 1], [154, 77, 50], [39, 103, 137], [194, 171, 183], [122, 12, 113], [4, 9, 49], [183, 228, 110], [184, 226, 78], [174, 202, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [186, 62], []]
 b := ![[], [20, 156, 279], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 3
  hpos := by decide
  P := [219, 253, 275, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![74096, 70039, 102424, 81261, 24089]
  a := ![-4, 0, -4, -9, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-81060, -45179, -76858, 81261, 24089]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 22188041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85, 2, 4, 20, -12]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![85, 2, 4, 20, -12]] 
 ![![281, 0, 0, 0, 0], ![253, 1, 0, 0, 0], ![170, 0, 1, 0, 0], ![264, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![85, 2, 4, 20, -12], ![-280, -7, -12, -64, 40], ![468, 14, 21, 108, -64], ![-480, -10, -20, -111, 68], ![456, 14, 24, 108, -63]]]
  hmulB := by decide  
  f := ![![![-2027, 62, -108, -292, 220]], ![![-1807, 55, -96, -260, 196]], ![![-1250, 38, -67, -180, 136]], ![![-1880, 58, -100, -271, 204]], ![![-304, 10, -16, -44, 33]]]
  g := ![![![-21, 2, 4, 20, -12], ![67, -7, -12, -64, 40], ![-116, 14, 21, 108, -64], ![114, -10, -20, -111, 68], ![-118, 14, 24, 108, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N1 : Nat.card (O ⧸ I281N1) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N1)

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := prime_ideal_of_norm_prime hp281.out _ NI281N1

def I281N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1178, -32, 72, 172, -133]] i)))

def SI281N2: IdealEqSpanCertificate' Table ![![1178, -32, 72, 172, -133]] 
 ![![281, 0, 0, 0, 0], ![265, 1, 0, 0, 0], ![153, 0, 1, 0, 0], ![261, 0, 0, 1, 0], ![109, 0, 0, 0, 1]] where
  M :=![![![1178, -32, 72, 172, -133], ![-3048, 81, -186, -444, 344], ![3942, -105, 239, 574, -444], ![-3911, 106, -238, -571, 441], ![2667, -72, 164, 390, -302]]]
  hmulB := by decide  
  f := ![![![20, -92, -64, -38, -75]], ![![12, -89, -62, -38, -71]], ![![6, -55, -39, -24, -43]], ![![9, -88, -62, -39, -70]], ![![-5, -44, -32, -22, -33]]]
  g := ![![![-113, -32, 72, 172, -133], ![293, 81, -186, -444, 344], ![-378, -105, 239, 574, -444], ![375, 106, -238, -571, 441], ![-257, -72, 164, 390, -302]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N2 : Nat.card (O ⧸ I281N2) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N2)

lemma isPrimeI281N2 : Ideal.IsPrime I281N2 := prime_ideal_of_norm_prime hp281.out _ NI281N2
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![-52, -30, -24, -18, -3]] ![![85, 2, 4, 20, -12]]
  ![![20, -92, -64, -38, -75]] where
 M := ![![![20, -92, -64, -38, -75]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI281N1 : IdealMulLeCertificate' Table 
  ![![20, -92, -64, -38, -75]] ![![1178, -32, 72, 172, -133]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![281, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC281 : ContainsPrimesAboveP 281 ![I281N0, I281N1, I281N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI281N0
    exact isPrimeI281N1
    exact isPrimeI281N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 281 (by decide) (𝕀 ⊙ MulI281N0 ⊙ MulI281N1)
instance hp283 : Fact (Nat.Prime 283) := {out := by norm_num}

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -16, 8, 12, -4]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![-19, -16, 8, 12, -4]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![77, 248, 1, 0, 0], ![24, 182, 0, 1, 0], ![160, 197, 0, 0, 1]] where
  M :=![![![-19, -16, 8, 12, -4], ![-80, -51, -24, 8, 24], ![264, 84, -51, -32, 8], ![-80, 28, 24, -27, -8], ![-112, -48, 80, 52, -47]]]
  hmulB := by decide  
  f := ![![![2279, -64, 136, 332, -260]], ![![-5968, 135, -376, -888, 664]], ![![-4583, 100, -291, -684, 508]], ![![-3672, 82, -232, -547, 408]], ![![-2848, 57, -184, -428, 313]]]
  g := ![![![-1, -12, 8, 12, -4], ![-8, -1, -24, 8, 24], ![13, 60, -51, -32, 8], ![0, 2, 24, -27, -8], ![0, -71, 80, 52, -47]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 2 2 8 [127, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [179, 282], [0, 1]]
 g := ![![[188, 78], [107, 216], [203], [258, 165], [239, 253], [60], [62], [1]], ![[0, 205], [0, 67], [203], [78, 118], [246, 30], [60], [62], [1]]]
 h' := ![![[179, 282], [278, 19], [137, 102], [62, 130], [211, 221], [61, 155], [48, 158], [156, 179], [0, 1]], ![[0, 1], [0, 264], [0, 181], [126, 153], [150, 62], [72, 128], [30, 125], [218, 104], [179, 282]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [18, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 2
  hpos := by decide
  P := [127, 104, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![53452, 37102, 33746, 33984, 24492]
  a := ![15, 17, 12, 6, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-25722, -68346, 33746, 33984, 24492]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 80089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 45, 24, -16, -18]] i)))

def SI283N1: IdealEqSpanCertificate' Table ![![23, 45, 24, -16, -18]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![140, 190, 1, 0, 0], ![143, 237, 0, 1, 0], ![74, 276, 0, 0, 1]] where
  M :=![![![23, 45, 24, -16, -18], ![-384, -179, 102, 104, -32], ![-282, -335, -109, 138, 104], ![402, 217, -68, -109, 12], ![670, 541, 42, -232, -81]]]
  hmulB := by decide  
  f := ![![![-5971, -109, -274, -1324, 822]], ![![19180, 377, 878, 4292, -2648]], ![![9814, 197, 449, 2202, -1356]], ![![13159, 263, 602, 2951, -1818]], ![![17040, 337, 780, 3816, -2353]]]
  g := ![![![1, 15, 24, -16, -18], ![-96, -125, 102, 104, -32], ![-44, -145, -109, 138, 104], ![87, 126, -68, -109, 12], ![120, 247, 42, -232, -81]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P1 : CertificateIrreducibleZModOfList' 283 2 2 8 [227, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [225, 282], [0, 1]]
 g := ![![[191, 96], [253, 44], [49], [27, 134], [23, 70], [92], [251], [1]], ![[0, 187], [248, 239], [49], [179, 149], [208, 213], [92], [251], [1]]]
 h' := ![![[225, 282], [18, 215], [267, 45], [97, 276], [156, 64], [5, 97], [212, 171], [56, 225], [0, 1]], ![[0, 1], [0, 68], [204, 238], [220, 7], [123, 219], [39, 186], [199, 112], [24, 58], [225, 282]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [112]]
 b := ![[], [209, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N1 : CertifiedPrimeIdeal' SI283N1 283 where
  n := 2
  hpos := by decide
  P := [227, 58, 1]
  hirr := P283P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10068, 9827, 7030, 6187, 7819]
  a := ![6, 12, 2, -5, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8613, -17492, 7030, 6187, 7819]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N1 B_one_repr
lemma NI283N1 : Nat.card (O ⧸ I283N1) = 80089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N1

def I283N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2399, 87, -154, -312, 258]] i)))

def SI283N2: IdealEqSpanCertificate' Table ![![-2399, 87, -154, -312, 258]] 
 ![![283, 0, 0, 0, 0], ![256, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-2399, 87, -154, -312, 258], ![5884, -235, 382, 732, -624], ![-7106, 309, -477, -834, 732], ![6918, -317, 462, 793, -712], ![-4106, 221, -296, -404, 393]]]
  hmulB := by decide  
  f := ![![![5595, -231, -3944, -636, 2154]], ![![5216, -109, -3582, -624, 1944]], ![![1118, -9, -755, -138, 408]], ![![72, -103, -140, 21, 88]], ![![275, -146, -314, 8, 187]]]
  g := ![![![-59, 87, -154, -312, 258], ![164, -235, 382, 732, -624], ![-218, 309, -477, -834, 732], ![228, -317, 462, 793, -712], ![-161, 221, -296, -404, 393]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N2 : Nat.card (O ⧸ I283N2) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N2)

lemma isPrimeI283N2 : Ideal.IsPrime I283N2 := prime_ideal_of_norm_prime hp283.out _ NI283N2
def MulI283N0 : IdealMulLeCertificate' Table 
  ![![-19, -16, 8, 12, -4]] ![![23, 45, 24, -16, -18]]
  ![![5595, -231, -3944, -636, 2154]] where
 M := ![![![5595, -231, -3944, -636, 2154]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI283N1 : IdealMulLeCertificate' Table 
  ![![5595, -231, -3944, -636, 2154]] ![![-2399, 87, -154, -312, 258]]
  ![![283, 0, 0, 0, 0]] where
 M := ![![![283, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC283 : ContainsPrimesAboveP 283 ![I283N0, I283N1, I283N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI283N0
    exact isPrimeI283N1
    exact isPrimeI283N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 283 (by decide) (𝕀 ⊙ MulI283N0 ⊙ MulI283N1)
instance hp293 : Fact (Nat.Prime 293) := {out := by norm_num}

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3076, 67, 134, 704, -433]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![3076, 67, 134, 704, -433]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![254, 150, 111, 1, 0], ![167, 82, 34, 0, 1]] where
  M :=![![![3076, 67, 134, 704, -433], ![-10124, -251, -464, -2336, 1408], ![16432, 338, 693, 3760, -2336], ![-17303, -431, -788, -3995, 2411], ![15903, 289, 636, 3626, -2288]]]
  hmulB := by decide  
  f := ![![![66, 19, -16, -10, 5]], ![![88, 117, 16, -56, -20]], ![![-224, -82, 113, 64, -56]], ![![17, 45, 37, -13, -27]], ![![37, 34, 8, -14, -9]]]
  g := ![![![-353, -239, -216, 704, -433], ![1188, 801, 720, -2336, 1408], ![-1872, -1270, -1151, 3760, -2336], ![2030, 1369, 1231, -3995, 2411], ![-1785, -1215, -1106, 3626, -2288]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 3 2 8 [285, 145, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [214, 5, 98], [26, 287, 195], [0, 1]]
 g := ![![[100, 287, 126], [238, 124], [270, 33, 229], [40, 60], [278, 167], [187, 280, 143], [240, 1], []], ![[239, 147, 83, 157], [192, 68], [183, 17, 279, 180], [215, 21], [79, 205], [84, 134, 223, 201], [87, 36], [30, 228]], ![[3, 96, 137, 52], [276, 95], [147, 123, 130, 219], [84, 239], [22, 239], [158, 180, 184, 264], [191, 25], [226, 228]]]
 h' := ![![[214, 5, 98], [14, 42, 205], [109, 119, 36], [6, 1, 225], [255, 196, 71], [31, 197, 131], [162, 75, 27], [0, 0, 1], [0, 1]], ![[26, 287, 195], [62, 190, 249], [172, 177, 19], [184, 176, 213], [148, 237, 30], [187, 229, 61], [163, 208, 156], [35, 200, 287], [214, 5, 98]], ![[0, 1], [213, 61, 132], [39, 290, 238], [181, 116, 148], [55, 153, 192], [53, 160, 101], [32, 10, 110], [140, 93, 5], [26, 287, 195]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 158], []]
 b := ![[], [51, 170, 112], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 3
  hpos := by decide
  P := [285, 145, 53, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18858073, 9672676, 8738210, 9369767, 3554517]
  a := ![12, 6, 8, 15, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10084188, -5758576, -3932285, 9369767, 3554517]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 25153757 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![66, 19, -16, -10, 5]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![66, 19, -16, -10, 5]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![85, 254, 1, 0, 0], ![198, 106, 0, 1, 0], ![271, 91, 0, 0, 1]] where
  M :=![![![66, 19, -16, -10, 5], ![88, 117, 16, -56, -20], ![-224, -82, 113, 64, -56], ![-119, -89, -38, 27, 35], ![219, -17, -138, -16, 72]]]
  hmulB := by decide  
  f := ![![![3076, 67, 134, 704, -433]], ![![-10124, -251, -464, -2336, 1408]], ![![-7828, -197, -361, -1808, 1087]], ![![-1643, -47, -80, -383, 225]], ![![-245, -15, -18, -62, 29]]]
  g := ![![![7, 16, -16, -10, 5], ![52, 13, 16, -56, -20], ![-25, -104, 113, 64, -56], ![-40, 12, -38, 27, 35], ![-15, 103, -138, -16, 72]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P1 : CertificateIrreducibleZModOfList' 293 2 2 8 [239, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [192, 292], [0, 1]]
 g := ![![[264, 255], [38], [], [], [], [117, 170], [239], [1]], ![[0, 38], [38], [], [], [], [234, 123], [239], [1]]]
 h' := ![![[192, 292], [1, 264], [0, 100], [283], [269], [165], [0, 113], [54, 192], [0, 1]], ![[0, 1], [0, 29], [155, 193], [283], [269], [165], [14, 180], [0, 101], [192, 292]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [88, 170]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N1 : CertifiedPrimeIdeal' SI293N1 293 where
  n := 2
  hpos := by decide
  P := [239, 101, 1]
  hirr := P293P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![131977, 70361, 67994, 69516, 23100]
  a := ![-25, -6, -33, -52, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-87617, -91027, 67994, 69516, 23100]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N1 B_one_repr
lemma NI293N1 : Nat.card (O ⧸ I293N1) = 85849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N1
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![3076, 67, 134, 704, -433]] ![![66, 19, -16, -10, 5]]
  ![![293, 0, 0, 0, 0]] where
 M := ![![![293, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC293 : ContainsPrimesAboveP 293 ![I293N0, I293N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI293N0
    exact isPrimeI293N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 293 (by decide) (𝕀 ⊙ MulI293N0)
instance hp307 : Fact (Nat.Prime 307) := {out := by norm_num}

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![721, 205, -40, -14, -46]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![721, 205, -40, -14, -46]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![54, 116, 80, 1, 0], ![68, 47, 110, 0, 1]] where
  M :=![![![721, 205, -40, -14, -46], ![-1184, 333, 238, -396, -28], ![-98, -1035, 543, 1054, -396], ![-1808, -193, -424, -485, 494], ![4288, 929, -666, -86, 23]]]
  hmulB := by decide  
  f := ![![![35359, -953, 2158, 5154, -3986]], ![![-91348, 2481, -5562, -13304, 10308]], ![![118134, -3159, 7227, 17234, -13304]], ![![2106, -43, 138, 315, -230]], ![![36436, -970, 2232, 5318, -4101]]]
  g := ![![![15, 13, 20, -14, -46], ![72, 155, 114, -396, -28], ![-98, -341, -131, 1054, -396], ![-30, 107, -52, -485, 494], ![24, 32, 12, -86, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 3 2 8 [227, 215, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [180, 274, 124], [101, 32, 183], [0, 1]]
 g := ![![[79, 270, 76], [60, 115, 170], [171, 287], [18, 17], [80, 182, 145], [61, 291, 77], [281, 1], []], ![[150, 269, 32, 226], [88, 167, 263, 198], [292, 144], [202, 275], [288, 193, 22, 147], [61, 106, 303, 131], [302, 103], [43, 26]], ![[215, 121, 43, 227], [105, 131, 186, 28], [288, 83], [61, 90], [34, 186, 45, 302], [199, 193, 122, 250], [125, 168], [291, 26]]]
 h' := ![![[180, 274, 124], [195, 301, 171], [169, 78, 279], [272, 192, 139], [260, 226, 289], [275, 190, 256], [69, 144, 154], [0, 0, 1], [0, 1]], ![[101, 32, 183], [35, 159, 123], [150, 190, 180], [212, 117, 12], [303, 108, 125], [129, 124, 131], [8, 1, 66], [228, 296, 32], [180, 274, 124]], ![[0, 1], [211, 154, 13], [175, 39, 155], [62, 305, 156], [44, 280, 200], [127, 300, 227], [193, 162, 87], [18, 11, 274], [101, 32, 183]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [210, 134], []]
 b := ![[], [20, 273, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 3
  hpos := by decide
  P := [227, 215, 26, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12853201, -6644024, -5715970, -6002374, -2269434]
  a := ![-10, -3, -10, -18, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1516601, 2593794, 2358670, -6002374, -2269434]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 28934443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![153, 2, 6, 34, -22]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![153, 2, 6, 34, -22]] 
 ![![307, 0, 0, 0, 0], ![215, 1, 0, 0, 0], ![66, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![128, 0, 0, 0, 1]] where
  M :=![![![153, 2, 6, 34, -22], ![-516, -17, -28, -120, 68], ![788, 2, 23, 172, -120], ![-872, -28, -46, -203, 116], ![732, -12, 10, 154, -121]]]
  hmulB := by decide  
  f := ![![![723, 506, 50, -210, -98]], ![![499, 353, 38, -146, -70]], ![![142, 98, 11, -40, -20]], ![![134, 92, 6, -39, -16]], ![![324, 224, 18, -94, -41]]]
  g := ![![![1, 2, 6, 34, -22], ![9, -17, -28, -120, 68], ![16, 2, 23, 172, -120], ![14, -28, -46, -203, 116], ![32, -12, 10, 154, -121]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N1 : Nat.card (O ⧸ I307N1) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N1)

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := prime_ideal_of_norm_prime hp307.out _ NI307N1

def I307N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1096, -27, 66, 164, -125]] i)))

def SI307N2: IdealEqSpanCertificate' Table ![![1096, -27, 66, 164, -125]] 
 ![![307, 0, 0, 0, 0], ![228, 1, 0, 0, 0], ![103, 0, 1, 0, 0], ![81, 0, 0, 1, 0], ![250, 0, 0, 0, 1]] where
  M :=![![![1096, -27, 66, 164, -125], ![-2868, 69, -172, -432, 328], ![3764, -88, 225, 572, -432], ![-3751, 87, -224, -571, 431], ![2631, -57, 156, 406, -304]]]
  hmulB := by decide  
  f := ![![![-230, -177, 60, 150, 31]], ![![-168, -131, 44, 112, 24]], ![![-66, -53, 21, 50, 11]], ![![-61, -46, 18, 41, 8]], ![![-189, -145, 54, 128, 26]]]
  g := ![![![60, -27, 66, 164, -125], ![-156, 69, -172, -432, 328], ![203, -88, 225, 572, -432], ![-202, 87, -224, -571, 431], ![139, -57, 156, 406, -304]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N2 : Nat.card (O ⧸ I307N2) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N2)

lemma isPrimeI307N2 : Ideal.IsPrime I307N2 := prime_ideal_of_norm_prime hp307.out _ NI307N2
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![721, 205, -40, -14, -46]] ![![153, 2, 6, 34, -22]]
  ![![-48451, -1179, -2150, -11208, 6820]] where
 M := ![![![-48451, -1179, -2150, -11208, 6820]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI307N1 : IdealMulLeCertificate' Table 
  ![![-48451, -1179, -2150, -11208, 6820]] ![![1096, -27, 66, 164, -125]]
  ![![307, 0, 0, 0, 0]] where
 M := ![![![2171104, 52190, 95784, 502252, -305465]]]
 hmul := by decide  
 g := ![![![![7072, 170, 312, 1636, -995]]]]
 hle2 := by decide  


def PBC307 : ContainsPrimesAboveP 307 ![I307N0, I307N1, I307N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI307N0
    exact isPrimeI307N1
    exact isPrimeI307N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 307 (by decide) (𝕀 ⊙ MulI307N0 ⊙ MulI307N1)


lemma PB519I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB519I6 : PrimesBelowBoundCertificateInterval O 251 307 519 where
  m := 9
  g := ![3, 2, 2, 2, 2, 3, 3, 2, 3]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB519I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1, I257N2]
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1]
    · exact ![I271N0, I271N1]
    · exact ![I277N0, I277N1]
    · exact ![I281N0, I281N1, I281N2]
    · exact ![I283N0, I283N1, I283N2]
    · exact ![I293N0, I293N1]
    · exact ![I307N0, I307N1, I307N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC257
    · exact PBC263
    · exact PBC269
    · exact PBC271
    · exact PBC277
    · exact PBC281
    · exact PBC283
    · exact PBC293
    · exact PBC307
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![16974593, 257, 257]
    · exact ![18191447, 69169]
    · exact ![19465109, 72361]
    · exact ![5393580481, 271]
    · exact ![5887339441, 277]
    · exact ![22188041, 281, 281]
    · exact ![80089, 80089, 283]
    · exact ![25153757, 85849]
    · exact ![28934443, 307, 307]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
      exact NI257N2
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
      exact NI277N1
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
      exact NI281N1
      exact NI281N2
    · dsimp ; intro j
      fin_cases j
      exact NI283N0
      exact NI283N1
      exact NI283N2
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
      exact NI307N2
  β := ![I257N1, I257N2, I271N1, I277N1, I281N1, I281N2, I283N2, I307N1, I307N2]
  Il := ![[I257N1, I257N2], [], [], [I271N1], [I277N1], [I281N1, I281N2], [I283N2], [], [I307N1, I307N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
