
import IdealArithmetic.Examples.NF5_3_202500000_3.RI5_3_202500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6583, 4517, 5321, -3636, -9812]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![6583, 4517, 5321, -3636, -9812]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![51, 46, 3, 1, 0], ![47, 34, 33, 0, 1]] where
  M :=![![![6583, 4517, 5321, -3636, -9812], ![13152, 9364, 11145, -7590, -20528], ![26904, 18949, 22466, -15310, -41384], ![20700, 14621, 17305, -11779, -31852], ![9276, 6477, 7675, -5238, -14149]]]
  hmulB := by decide  
  f := ![![![-35, 45, -145, 76, 212]], ![![-192, -120, 17, 22, 208]], ![![1704, -11, 2218, -1342, -4632]], ![![-135, -33, -102, 71, 280]], ![![749, -41, 1054, -628, -2129]]]
  g := ![![![9749, 7543, 5075, -3636, -9812], ![20374, 15768, 10617, -7590, -20528], ![41086, 31795, 21404, -15310, -41384], ![31619, 24469, 16474, -11779, -31852], ![14051, 10873, 7318, -5238, -14149]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [33, 34, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 51, 53], [50, 15, 14], [0, 1]]
 g := ![![[45, 52, 6], [18, 5, 14], [41, 35], [0, 35], [39, 1], []], ![[55, 22, 12, 63], [31, 33, 8, 7], [33, 36], [24, 64], [55, 24], [52, 62]], ![[8, 47, 2, 23], [3, 7, 37, 14], [33, 26], [52, 25], [35, 55], [24, 62]]]
 h' := ![![[56, 51, 53], [9, 37, 41], [12, 63, 9], [62, 47, 13], [53, 48, 13], [0, 0, 1], [0, 1]], ![[50, 15, 14], [1, 42, 30], [39, 61, 57], [49, 3, 6], [29, 54, 59], [13, 22, 15], [56, 51, 53]], ![[0, 1], [63, 55, 63], [42, 10, 1], [27, 17, 48], [1, 32, 62], [33, 45, 51], [50, 15, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 6], []]
 b := ![[], [16, 32, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [33, 34, 28, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![178869606, 50730600, 169858687, -143617658, -370701511]
  a := ![153, 6, 189, -140, -391]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![372034943, 287477526, 191550172, -143617658, -370701511]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, -45, 145, -76, -212]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![35, -45, 145, -76, -212]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![64, 61, 1, 0, 0], ![58, 48, 0, 1, 0], ![56, 38, 0, 0, 1]] where
  M :=![![![35, -45, 145, -76, -212], ![192, 120, -17, -22, -208], ![-1704, 11, -2218, 1342, 4632], ![3540, -1047, 6875, -3895, -12276], ![-2124, 419, -3661, 2110, 6823]]]
  hmulB := by decide  
  f := ![![![-6583, -4517, -5321, 3636, 9812]], ![![-13152, -9364, -11145, 7590, 20528]], ![![-18664, -13123, -15565, 10612, 28680]], ![![-15430, -10837, -12849, 8761, 23676]], ![![-13100, -9183, -10883, 7422, 20055]]]
  g := ![![![105, 42, 145, -76, -212], ![212, 151, -17, -22, -208], ![-2940, -1569, -2218, 1342, 4632], ![7118, 3478, 6875, -3895, -12276], ![-4064, -2042, -3661, 2110, 6823]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [54, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 66], [0, 1]]
 g := ![![[64, 36], [49, 15], [21], [17], [47], [1]], ![[0, 31], [0, 52], [21], [17], [47], [1]]]
 h' := ![![[28, 66], [34, 61], [54, 22], [60, 50], [43, 34], [13, 28], [0, 1]], ![[0, 1], [0, 6], [0, 45], [53, 17], [57, 33], [60, 39], [28, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [26, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [54, 39, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-304212, 169574, -850701, 537349, 1287194]
  a := ![-183, -72, -226, 103, 468]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-732962, -337967, -850701, 537349, 1287194]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![6583, 4517, 5321, -3636, -9812]] ![![35, -45, 145, -76, -212]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![-67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-533, -407, -443, 288, 790]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-533, -407, -443, 288, 790]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![67, 10, 6, 32, 1]] where
  M :=![![![-533, -407, -443, 288, 790], ![-888, -762, -727, 430, 1216], ![-888, -1259, -656, 146, 648], ![1704, -213, 1633, -1775, -4260], ![-1116, -689, -953, 692, 1841]]]
  hmulB := by decide  
  f := ![![![29, -19, -33, 20, 58]], ![![-24, 14, 9, -6, -16]], ![![24, -19, 28, -14, -40]], ![![24, 13, -19, 7, 4]], ![![37, -12, -36, 20, 51]]]
  g := ![![![-753, -117, -73, -352, 790], ![-1160, -182, -113, -542, 1216], ![-624, -109, -64, -290, 648], ![4044, 597, 383, 1895, -4260], ![-1753, -269, -169, -820, 1841]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [22, 45, 70, 50, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 5, 56, 35], [21, 5, 7, 7], [60, 60, 8, 29], [0, 1]]
 g := ![![[35, 15, 20, 12], [52, 55, 64, 19], [0, 42, 36, 19], [14, 2, 15], [1], []], ![[50, 47, 58, 31, 15, 26], [36, 32, 24, 37, 45, 22], [38, 40, 27, 65, 45, 23], [68, 69, 1], [18, 47, 45], [42, 38, 18]], ![[38, 13, 63, 49, 35, 35], [8, 3, 57, 21, 43, 21], [55, 44, 44, 22, 57, 21], [16, 55, 38], [45, 34, 6], [50, 62, 49]], ![[53, 4, 49, 56, 48, 20], [3, 26, 0, 42, 39, 36], [68, 59, 61, 53, 53, 38], [35, 21, 40], [39, 2, 1], [48, 20, 60]]]
 h' := ![![[11, 5, 56, 35], [63, 0, 3, 56], [0, 19, 3, 27], [34, 28, 13, 27], [49, 26, 1, 21], [0, 0, 1], [0, 1]], ![[21, 5, 7, 7], [36, 52, 54, 44], [16, 37, 10, 58], [0, 50, 41, 5], [17, 15, 24, 1], [49, 11, 45, 20], [11, 5, 56, 35]], ![[60, 60, 8, 29], [44, 22, 70, 17], [38, 18, 52, 28], [61, 32, 57, 43], [49, 49, 51, 31], [51, 4, 51, 52], [21, 5, 7, 7]], ![[0, 1], [65, 68, 15, 25], [70, 68, 6, 29], [27, 32, 31, 67], [67, 52, 66, 18], [59, 56, 45, 70], [60, 60, 8, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [15, 55, 58], []]
 b := ![[], [], [8, 0, 2, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [22, 45, 70, 50, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2538595934, -812381874, -2264121736, 2003494506, 5043126562]
  a := ![38, -1, 47, -37, -97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4794761628, -721741514, -458068748, -2244740218, 5043126562]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, -19, -33, 20, 58]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![29, -19, -33, 20, 58]] 
 ![![71, 0, 0, 0, 0], ![70, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![29, -19, -33, 20, 58], ![-24, 14, 9, -6, -16], ![24, -19, 28, -14, -40], ![24, 13, -19, 7, 4], ![12, -21, 5, 0, 7]]]
  hmulB := by decide  
  f := ![![![-533, -407, -443, 288, 790]], ![![-538, -412, -447, 290, 796]], ![![-538, -419, -446, 286, 788]], ![![24, -3, 23, -25, -60]], ![![-316, -239, -263, 172, 471]]]
  g := ![![![19, -19, -33, 20, 58], ![-14, 14, 9, -6, -16], ![14, -19, 28, -14, -40], ![4, 13, -19, 7, 4], ![12, -21, 5, 0, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-533, -407, -443, 288, 790]] ![![29, -19, -33, 20, 58]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 18, 199, -115, -348]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![1, 18, 199, -115, -348]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![43, 44, 16, 19, 1]] where
  M :=![![![1, 18, 199, -115, -348], ![-36, 82, -375, 198, 556], ![-456, -251, 68, 26, 424], ![2094, -49, 2869, -1735, -5866], ![-1038, -69, -1067, 672, 2429]]]
  hmulB := by decide  
  f := ![![![547, 386, 459, -313, -846]], ![![1116, 786, 935, -638, -1724]], ![![2280, 1603, 1912, -1306, -3528]], ![![1782, 1245, 1495, -1025, -2766]], ![![1969, 1384, 1651, -1128, -3047]]]
  g := ![![![205, 210, 79, 89, -348], ![-328, -334, -127, -142, 556], ![-256, -259, -92, -110, 424], ![3484, 3535, 1325, 1503, -5866], ![-1445, -1465, -547, -623, 2429]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 4 2 6 [64, 36, 8, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 30, 5, 41], [6, 9, 6, 20], [59, 33, 62, 12], [0, 1]]
 g := ![![[57, 53, 72, 71], [4, 60, 71], [44, 5, 55], [39, 52, 26, 36], [1], []], ![[28, 50, 64, 59, 47, 6], [5, 65, 49], [38, 5, 70], [55, 23, 50, 1, 46, 71], [35, 55, 49], [8, 33, 2]], ![[23, 24, 10, 33, 41, 11], [44, 27, 1], [29, 58, 57], [58, 61, 33, 19, 55, 31], [71, 31, 57], [9, 30, 35]], ![[17, 58, 24, 53, 1, 23], [56, 54, 35], [55, 6, 32], [68, 62, 17, 48, 47, 71], [10, 57, 12], [32, 40, 71]]]
 h' := ![![[2, 30, 5, 41], [27, 17, 39, 12], [8, 63, 2, 12], [59, 21, 30, 36], [9, 37, 65, 67], [0, 0, 1], [0, 1]], ![[6, 9, 6, 20], [13, 58, 61, 59], [48, 23, 10, 7], [61, 23, 49, 17], [32, 9, 17, 55], [3, 56, 51, 7], [2, 30, 5, 41]], ![[59, 33, 62, 12], [30, 31, 19, 11], [46, 53, 53, 1], [2, 16, 36, 38], [20, 66, 26, 66], [44, 54, 46, 35], [6, 9, 6, 20]], ![[0, 1], [16, 40, 27, 64], [60, 7, 8, 53], [21, 13, 31, 55], [16, 34, 38, 31], [46, 36, 48, 31], [59, 33, 62, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [63, 57, 15], []]
 b := ![[], [], [46, 72, 2, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 4
  hpos := by decide
  P := [64, 36, 8, 6, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5331975339101, -1713028708500, -4744671785829, 4206004839072, 10576236426292]
  a := ![-259, 5, -320, 250, 662]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6302878653009, -6398183992676, -2383074720637, -2695102565212, 10576236426292]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 28398241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![547, 386, 459, -313, -846]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![547, 386, 459, -313, -846]] 
 ![![73, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![547, 386, 459, -313, -846], ![1116, 786, 935, -638, -1724], ![2280, 1603, 1912, -1306, -3528], ![1782, 1245, 1495, -1025, -2766], ![774, 547, 649, -442, -1195]]]
  hmulB := by decide  
  f := ![![![1, 18, 199, -115, -348]], ![![0, 10, 93, -54, -164]], ![![-6, 1, 50, -28, -80]], ![![29, 5, 102, -60, -190]], ![![-14, 3, 29, -16, -43]]]
  g := ![![![-12, 386, 459, -313, -846], ![-24, 786, 935, -638, -1724], ![-46, 1603, 1912, -1306, -3528], ![-29, 1245, 1495, -1025, -2766], ![-18, 547, 649, -442, -1195]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![1, 18, 199, -115, -348]] ![![547, 386, 459, -313, -846]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22847, 16721, 20065, -13636, -36936]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![22847, 16721, 20065, -13636, -36936]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![18, 19, 68, 25, 1]] where
  M :=![![![22847, 16721, 20065, -13636, -36936], ![47664, 33248, 39365, -26862, -72560], ![96312, 68193, 81078, -55254, -149384], ![74436, 52633, 62557, -42635, -115260], ![32844, 23477, 27987, -19058, -51553]]]
  hmulB := by decide  
  f := ![![![-7, 5, -21, 12, 32]], ![![-48, -20, -23, 22, 80]], ![![168, -35, 270, -142, -536]], ![![-636, 103, -1099, 667, 2004]], ![![-66, -2, -119, 93, 187]]]
  g := ![![![8705, 9095, 32047, 11516, -36936], ![17136, 17872, 62955, 22622, -72560], ![35256, 36791, 129610, 46574, -149384], ![27204, 28387, 100003, 35935, -115260], ![12162, 12696, 44729, 16073, -51553]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 4 2 6 [55, 14, 21, 14, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 40, 65, 50], [21, 48, 25, 54], [19, 69, 68, 54], [0, 1]]
 g := ![![[57, 7, 57, 44], [73, 42, 75, 49], [43, 78, 32, 46], [4, 41, 56, 38], [1], []], ![[1, 22, 36, 10, 41, 11], [16, 45, 72, 10, 5, 16], [40, 33, 17, 42, 51, 65], [75, 15, 35, 65, 44, 44], [3, 66, 10], [15, 19, 51]], ![[46, 38, 3, 1, 5, 14], [0, 46, 19, 14, 43, 34], [12, 27, 27, 25, 23, 33], [43, 23, 13, 46, 68, 34], [34, 5, 25], [43, 33, 72]], ![[72, 32, 70, 37, 43, 70], [66, 36, 60, 53, 71, 29], [17, 38, 58, 44, 7, 74], [68, 14, 30, 8, 32, 6], [37, 54, 18], [70, 16, 72]]]
 h' := ![![[25, 40, 65, 50], [14, 11, 22, 53], [5, 58, 60, 7], [17, 3, 14, 58], [24, 65, 58, 65], [0, 0, 1], [0, 1]], ![[21, 48, 25, 54], [38, 19, 21, 12], [33, 35, 41, 51], [2, 62, 17, 5], [19, 29, 41, 55], [37, 34, 42, 57], [25, 40, 65, 50]], ![[19, 69, 68, 54], [1, 75, 38, 45], [8, 28, 0, 12], [31, 59, 66, 20], [20, 59, 23, 12], [51, 73, 4, 74], [21, 48, 25, 54]], ![[0, 1], [48, 53, 77, 48], [51, 37, 57, 9], [9, 34, 61, 75], [30, 5, 36, 26], [66, 51, 32, 27], [19, 69, 68, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [13, 13, 9], []]
 b := ![[], [], [45, 71, 47, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 4
  hpos := by decide
  P := [55, 14, 21, 14, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2489864660181, -780174469456, -2364893436956, 2104964659924, 5028287448658]
  a := ![385, 23, 476, -339, -984]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1177203021975, -1219210582202, -4358081518300, -1564585082994, 5028287448658]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 38950081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 5, -21, 12, 32]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-7, 5, -21, 12, 32]] 
 ![![79, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![68, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-7, 5, -21, 12, 32], ![-48, -20, -23, 22, 80], ![168, -35, 270, -142, -536], ![-636, 103, -1099, 667, 2004], ![300, -63, 529, -306, -975]]]
  hmulB := by decide  
  f := ![![![22847, 16721, 20065, -13636, -36936]], ![![7255, 5289, 6340, -4310, -11672]], ![![8160, 5943, 7122, -4842, -13112]], ![![20608, 15059, 18063, -12277, -33252]], ![![6489, 4742, 5688, -3866, -10471]]]
  g := ![![![-14, 5, -21, 12, 32], ![-28, -20, -23, 22, 80], ![195, -35, 270, -142, -536], ![-811, 103, -1099, 667, 2004], ![384, -63, 529, -306, -975]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![22847, 16721, 20065, -13636, -36936]] ![![-7, 5, -21, 12, 32]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 138, 135, -95, -252]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![179, 138, 135, -95, -252]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![55, 36, 39, 1, 0], ![80, 59, 48, 0, 1]] where
  M :=![![![179, 138, 135, -95, -252], ![396, 252, 381, -250, -676], ![888, 601, 686, -478, -1368], ![198, 455, -79, 3, 238], ![474, 199, 469, -304, -945]]]
  hmulB := by decide  
  f := ![![![91, -82, -159, 101, 290]], ![![-156, 20, 13, 14, 12]], ![![-360, -159, -418, 354, 904]], ![![-187, -124, -306, 248, 644]], ![![-230, -157, -386, 312, 811]]]
  g := ![![![308, 222, 192, -95, -252], ![822, 592, 513, -250, -676], ![1646, 1187, 1024, -478, -1368], ![-229, -165, -140, 3, 238], ![1118, 806, 695, -304, -945]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [32, 41, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 71, 47], [71, 11, 36], [0, 1]]
 g := ![![[10, 28, 75], [75, 50, 31], [53, 59], [67, 28], [42, 0, 1], []], ![[37, 30, 27, 5], [67, 55, 74, 35], [2, 63], [22, 11], [73, 30, 21, 43], [34, 51]], ![[23, 16, 81, 77], [14, 71, 52, 9], [57, 10], [63, 69], [61, 0, 45, 38], [45, 51]]]
 h' := ![![[12, 71, 47], [7, 73, 65], [73, 48, 23], [21, 1, 68], [67, 21, 51], [0, 0, 1], [0, 1]], ![[71, 11, 36], [30, 12, 79], [19, 60, 19], [0, 64, 48], [66, 54, 54], [52, 6, 11], [12, 71, 47]], ![[0, 1], [49, 81, 22], [67, 58, 41], [27, 18, 50], [36, 8, 61], [32, 77, 71], [71, 11, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 21], []]
 b := ![[], [51, 66, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [32, 41, 0, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13269830, -62365434, 154448408, -77021514, -197110506]
  a := ![-162, -18, -200, 126, 414]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![241184260, 172770228, 152043274, -77021514, -197110506]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91, -82, -159, 101, 290]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![91, -82, -159, 101, 290]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![22, 5, 1, 0, 0], ![28, 82, 0, 1, 0], ![55, 32, 0, 0, 1]] where
  M :=![![![91, -82, -159, 101, 290], ![-156, 20, 13, 14, 12], ![-360, -159, -418, 354, 904], ![-870, -301, -819, 719, 1814], ![114, -19, -21, -2, 13]]]
  hmulB := by decide  
  f := ![![![179, 138, 135, -95, -252]], ![![396, 252, 381, -250, -676]], ![![82, 59, 67, -46, -124]], ![![454, 301, 421, -279, -750]], ![![277, 191, 242, -163, -439]]]
  g := ![![![-183, -203, -159, 101, 290], ![-18, -19, 13, 14, 12], ![-612, -675, -418, 354, 904], ![-1238, -1364, -819, 719, 1814], ![-1, -2, -21, -2, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [66, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 82], [0, 1]]
 g := ![![[77, 63], [4, 78], [59], [51], [48, 29], [1]], ![[42, 20], [16, 5], [59], [51], [78, 54], [1]]]
 h' := ![![[64, 82], [68, 35], [14, 59], [67, 15], [69, 36], [17, 64], [0, 1]], ![[0, 1], [67, 48], [55, 24], [31, 68], [49, 47], [46, 19], [64, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [52, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [66, 19, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-565710, -164071, -522641, 452018, 1157294]
  a := ![-163, 3, -201, 170, 418]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-787654, -863250, -522641, 452018, 1157294]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![179, 138, 135, -95, -252]] ![![91, -82, -159, 101, 290]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
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


def P89P0 : CertificateIrreducibleZModOfList' 89 5 2 6 [43, 12, 12, 69, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 48, 83, 31, 87], [41, 22, 43, 62, 3], [20, 61, 32, 43, 23], [47, 46, 20, 42, 65], [0, 1]]
 g := ![![[46, 57, 22, 12, 72], [19, 10, 30, 42], [55, 31, 73, 45], [44, 7, 40, 48, 1], [1], []], ![[33, 24, 16, 84, 2, 2, 14, 73], [8, 74, 1, 53], [1, 34, 78, 11], [36, 36, 29, 82, 88, 15, 73, 57], [32, 47, 34, 10, 45, 26, 72, 78], [85, 36, 50, 4]], ![[47, 38, 40, 10, 31, 60, 77, 26], [38, 85, 26, 20], [76, 49, 84, 18], [34, 55, 12, 76, 51, 75, 23, 28], [86, 23, 1, 3, 78, 81, 23, 3], [64, 3, 7, 9]], ![[74, 2, 67, 74, 15, 58, 58, 56], [67, 52, 66, 44], [1, 73, 20, 18], [86, 24, 33, 62, 35, 3, 41, 56], [88, 13, 27, 12, 58, 82, 71, 37], [74, 81, 25, 84]], ![[54, 33, 40, 56, 58, 52, 13, 13], [19, 66, 71, 78], [46, 13, 16, 18], [29, 13, 15, 0, 81, 50, 14, 70], [21, 57, 18, 35, 63, 57, 31, 61], [30, 53, 78, 42]]]
 h' := ![![[69, 48, 83, 31, 87], [5, 4, 47, 43, 61], [33, 37, 83, 43, 65], [66, 41, 35, 51, 57], [46, 77, 77, 20, 88], [0, 0, 1], [0, 1]], ![[41, 22, 43, 62, 3], [85, 61, 23, 21, 39], [47, 27, 82, 25, 26], [1, 83, 41, 0, 79], [4, 67, 64, 34, 4], [38, 51, 10, 15, 53], [69, 48, 83, 31, 87]], ![[20, 61, 32, 43, 23], [73, 12, 35, 30, 35], [4, 37, 24, 72, 51], [54, 25, 36, 10, 14], [53, 47, 48, 65, 22], [86, 17, 57, 6, 88], [41, 22, 43, 62, 3]], ![[47, 46, 20, 42, 65], [35, 71, 29, 88, 57], [54, 56, 61, 25, 20], [50, 65, 15, 84, 14], [32, 29, 62, 42, 57], [66, 27, 19, 84, 41], [20, 61, 32, 43, 23]], ![[0, 1], [56, 30, 44, 85, 75], [61, 21, 17, 13, 16], [9, 53, 51, 33, 14], [87, 47, 16, 17, 7], [29, 83, 2, 73, 85], [47, 46, 20, 42, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 47, 73, 76], [], [], []]
 b := ![[], [24, 14, 14, 85, 38], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 5
  hpos := by decide
  P := [43, 12, 12, 69, 1, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![519507141210, -102673487410, 895858966565, -516243515660, -1669419158960]
  a := ![-47, -7, -58, 36, 120]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5837158890, -1153634690, 10065831085, -5800488940, -18757518640]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![485, 115, 327, -304, -750]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![485, 115, 327, -304, -750]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![94, 45, 64, 1, 0], ![47, 12, 11, 0, 1]] where
  M :=![![![485, 115, 327, -304, -750], ![1944, 670, 1795, -1574, -3968], ![9048, 2919, 8012, -7098, -17832], ![19800, 6377, 17611, -15609, -39212], ![-1236, -411, -1155, 1020, 2567]]]
  hmulB := by decide  
  f := ![![![-43, 17, -93, 52, 162]], ![![72, -78, 269, -142, -400]], ![![312, 225, -88, -6, -264]], ![![182, 129, -44, -7, -160]], ![![31, 25, -14, 2, -19]]]
  g := ![![![663, 235, 289, -304, -750], ![3468, 1228, 1507, -1574, -3968], ![15612, 5529, 6788, -7098, -17832], ![34330, 12158, 14927, -15609, -39212], ![-2245, -795, -976, 1020, 2567]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [19, 51, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 6, 61], [38, 90, 36], [0, 1]]
 g := ![![[19, 24, 54], [36, 89], [17, 53], [92, 44], [81, 54], [1]], ![[28, 57, 56, 64], [83, 16], [7, 36], [78, 4], [13, 44], [96, 33, 16, 1]], ![[25, 18, 42, 62], [67, 86], [88, 50], [8, 43], [60, 81], [64, 13, 73, 96]]]
 h' := ![![[27, 6, 61], [49, 9, 65], [65, 66, 63], [0, 20, 21], [83, 79, 23], [78, 46, 65], [0, 1]], ![[38, 90, 36], [50, 5, 94], [50, 59, 93], [38, 40, 6], [68, 3, 2], [11, 33, 23], [27, 6, 61]], ![[0, 1], [35, 83, 35], [85, 69, 38], [60, 37, 70], [55, 15, 72], [15, 18, 9], [38, 90, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 8], []]
 b := ![[], [77, 29, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [19, 51, 32, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-240287699, -70426724, -224093290, 191642822, 492401306]
  a := ![-165, -7, -203, 151, 422]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-426779117, -150548138, -184594312, 191642822, 492401306]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, -17, 93, -52, -162]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![43, -17, 93, -52, -162]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![81, 66, 1, 0, 0], ![43, 94, 0, 1, 0], ![48, 18, 0, 0, 1]] where
  M :=![![![43, -17, 93, -52, -162], ![-72, 78, -269, 142, 400], ![-312, -225, 88, 6, 264], ![1512, -25, 1999, -1207, -4148], ![-732, -87, -753, 480, 1753]]]
  hmulB := by decide  
  f := ![![![-485, -115, -327, 304, 750]], ![![-1944, -670, -1795, 1574, 3968]], ![![-1821, -582, -1577, 1398, 3510]], ![![-2303, -766, -2066, 1821, 4582]], ![![-588, -177, -483, 432, 1081]]]
  g := ![![![26, 17, 93, -52, -162], ![-37, -28, -269, 142, 400], ![-210, -117, 88, 6, 264], ![934, 579, 1999, -1207, -4148], ![-459, -279, -753, 480, 1753]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [95, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 96], [0, 1]]
 g := ![![[69, 48], [75], [61], [3], [89], [41, 1]], ![[0, 49], [75], [61], [3], [89], [82, 96]]]
 h' := ![![[41, 96], [88, 57], [36, 47], [37, 35], [15, 10], [82, 34], [0, 1]], ![[0, 1], [0, 40], [23, 50], [17, 62], [37, 87], [21, 63], [41, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [18, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [95, 56, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-157712, -81826, -96695, 121780, 240664]
  a := ![-241, -13, -298, 214, 616]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-93957, -97724, -96695, 121780, 240664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![485, 115, 327, -304, -750]] ![![43, -17, 93, -52, -162]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![-97, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![493, 432, 537, -359, -982]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![493, 432, 537, -359, -982]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![27, 49, 62, 1, 0], ![68, 99, 53, 0, 1]] where
  M :=![![![493, 432, 537, -359, -982], ![1140, 766, 875, -594, -1604], ![2136, 1599, 1832, -1218, -3320], ![1434, 1159, 1207, -759, -2106], ![786, 587, 723, -494, -1337]]]
  hmulB := by decide  
  f := ![![![35, -12, 73, -41, -128]], ![![-60, 62, -215, 114, 324]], ![![-216, -179, 116, -22, 120]], ![![-141, -83, 1, 22, 166]], ![![-154, -42, -106, 76, 307]]]
  g := ![![![762, 1141, 741, -359, -982], ![1250, 1868, 1215, -594, -1604], ![2582, 3861, 2508, -1218, -3320], ![1635, 2444, 1583, -759, -2106], ![1040, 1556, 1012, -494, -1337]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [26, 8, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [100, 73, 73], [56, 27, 28], [0, 1]]
 g := ![![[35, 41, 6], [52, 76], [48, 16, 22], [80, 19], [57, 96], [1]], ![[45, 69, 8, 93], [55, 9], [3, 11, 30, 75], [31, 56], [96, 64], [89, 0, 91, 66]], ![[12, 20, 25, 90], [41, 88], [35, 54, 100, 99], [53, 43], [65, 88], [55, 26, 82, 35]]]
 h' := ![![[100, 73, 73], [45, 5, 62], [65, 13, 51], [45, 34, 27], [2, 90, 76], [75, 93, 55], [0, 1]], ![[56, 27, 28], [84, 14, 19], [10, 95, 3], [66, 99, 80], [93, 83, 37], [8, 12, 93], [100, 73, 73]], ![[0, 1], [90, 82, 20], [67, 94, 47], [14, 69, 95], [33, 29, 89], [62, 97, 54], [56, 27, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 11], []]
 b := ![[], [77, 97, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [26, 8, 46, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-191171055, -59536651, -173815429, 152475385, 383839813]
  a := ![-127, -3, -157, 121, 325]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-301080334, -450801703, -296740588, 152475385, 383839813]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, 12, -73, 41, 128]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-35, 12, -73, 41, 128]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![13, 78, 1, 0, 0], ![99, 96, 0, 1, 0], ![93, 88, 0, 0, 1]] where
  M :=![![![-35, 12, -73, 41, 128], ![60, -62, 215, -114, -324], ![216, 179, -116, 22, -120], ![-1146, -1, -1473, 893, 3094], ![546, 77, 533, -344, -1275]]]
  hmulB := by decide  
  f := ![![![-493, -432, -537, 359, 982]], ![![-1140, -766, -875, 594, 1604]], ![![-965, -663, -763, 517, 1398]], ![![-1581, -1163, -1370, 924, 2508]], ![![-1455, -1071, -1264, 853, 2315]]]
  g := ![![![-149, -94, -73, 41, 128], ![383, 224, 215, -114, -324], ![106, 175, -116, 22, -120], ![-3546, -2407, -1473, 893, 3094], ![1448, 1027, 533, -344, -1275]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [56, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 100], [0, 1]]
 g := ![![[2, 92], [65], [37, 79], [77], [84], [90, 1]], ![[0, 9], [65], [77, 22], [77], [84], [79, 100]]]
 h' := ![![[90, 100], [74, 71], [49, 41], [78, 33], [42, 73], [10, 65], [0, 1]], ![[0, 1], [0, 30], [2, 60], [18, 68], [47, 28], [2, 36], [90, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [56, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [56, 11, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26656, 8985, 14864, -11349, -48884]
  a := ![-85, -9, -108, 65, 218]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![54487, 41989, 14864, -11349, -48884]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![493, 432, 537, -359, -982]] ![![-35, 12, -73, 41, 128]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-301, 115, -660, 369, 1142]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-301, 115, -660, 369, 1142]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![18, 6, 14, 1, 0], ![64, 30, 5, 0, 1]] where
  M :=![![![-301, 115, -660, 369, 1142], ![420, -557, 1782, -932, -2596], ![2400, 1470, -153, -300, -2672], ![-10842, 366, -14782, 8873, 30250], ![5310, 482, 5772, -3632, -13087]]]
  hmulB := by decide  
  f := ![![![671, 239, 584, -507, -1280]], ![![2892, 989, 2574, -2256, -5684]], ![![13008, 4294, 11565, -10204, -25664]], ![![2328, 772, 2068, -1823, -4586]], ![![1874, 640, 1659, -1454, -3663]]]
  g := ![![![-777, -353, -112, 369, 1142], ![1780, 805, 270, -932, -2596], ![1736, 810, 169, -300, -2672], ![-20452, -9324, -2818, 8873, 30250], ![8818, 4028, 1185, -3632, -13087]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [87, 10, 84, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 89, 31], [83, 13, 72], [0, 1]]
 g := ![![[99, 60, 19], [77, 55, 18], [95, 85, 59], [100, 4], [93, 52], [1]], ![[85, 61, 40, 43], [84, 28, 100, 20], [95, 60, 98, 94], [46, 36], [6, 55], [76, 99, 58, 24]], ![[48, 54, 89, 56], [97, 86, 68, 28], [97, 0, 73, 64], [15, 64], [48, 82], [60, 43, 46, 79]]]
 h' := ![![[39, 89, 31], [99, 14, 15], [78, 102, 92], [1, 75, 70], [96, 97, 101], [16, 93, 19], [0, 1]], ![[83, 13, 72], [50, 61, 11], [29, 59, 32], [12, 12, 42], [10, 36, 97], [74, 81, 40], [39, 89, 31]], ![[0, 1], [70, 28, 77], [65, 45, 82], [50, 16, 94], [4, 73, 8], [67, 32, 44], [83, 13, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91, 14], []]
 b := ![[], [40, 11, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [87, 10, 84, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42448861, 12147633, 40221899, -34107515, -87759115]
  a := ![92, 5, 113, -85, -235]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![60902597, 27665691, 9286628, -34107515, -87759115]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3523, 2487, 2934, -1995, -5396]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![3523, 2487, 2934, -1995, -5396]] 
 ![![103, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![94, 0, 0, 1, 0], ![61, 0, 0, 0, 1]] where
  M :=![![![3523, 2487, 2934, -1995, -5396], ![7068, 5051, 5926, -4012, -10868], ![14016, 10150, 11703, -7852, -21328], ![9834, 7522, 8158, -5283, -14510], ![5142, 3584, 4306, -2954, -7969]]]
  hmulB := by decide  
  f := ![![![-7457, 2147, -14354, 8137, 25722]], ![![-2164, 547, -3998, 2280, 7268]], ![![-186, 512, -1369, 694, 1828]], ![![-8864, 1822, -15450, 8889, 28682]], ![![-3497, 1491, -7800, 4335, 13317]]]
  g := ![![![4107, 2487, 2934, -1995, -5396], ![8252, 5051, 5926, -4012, -10868], ![16098, 10150, 11703, -7852, -21328], ![10698, 7522, 8158, -5283, -14510], ![6101, 3584, 4306, -2954, -7969]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 0, -6, 4, 12]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![-5, 0, -6, 4, 12]] 
 ![![103, 0, 0, 0, 0], ![43, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![88, 0, 0, 0, 1]] where
  M :=![![![-5, 0, -6, 4, 12], ![0, -7, 12, -4, -16], ![-48, 4, -83, 56, 144], ![-144, -46, -112, 95, 280], ![24, 16, -2, -4, -25]]]
  hmulB := by decide  
  f := ![![![-2747, -1824, -2130, 1460, 3932]], ![![-1199, -799, -934, 640, 1724]], ![![-241, -164, -193, 132, 356]], ![![-2137, -1422, -1662, 1139, 3068]], ![![-2384, -1584, -1850, 1268, 3415]]]
  g := ![![![-13, 0, -6, 4, 12], ![19, -7, 12, -4, -16], ![-163, 4, -83, 56, 144], ![-287, -46, -112, 95, 280], ![18, 16, -2, -4, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-301, 115, -660, 369, 1142]] ![![3523, 2487, 2934, -1995, -5396]]
  ![![2747, 1824, 2130, -1460, -3932]] where
 M := ![![![2747, 1824, 2130, -1460, -3932]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![2747, 1824, 2130, -1460, -3932]] ![![-5, 0, -6, 4, 12]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![-103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)


lemma PB696I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB696I2 : PrimesBelowBoundCertificateInterval O 61 103 696 where
  m := 9
  g := ![2, 2, 2, 2, 2, 1, 2, 2, 3]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB696I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
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
    · exact ![300763, 4489]
    · exact ![25411681, 71]
    · exact ![28398241, 73]
    · exact ![38950081, 79]
    · exact ![571787, 6889]
    · exact ![5584059449]
    · exact ![912673, 9409]
    · exact ![1030301, 10201]
    · exact ![1092727, 103, 103]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
  β := ![I71N1, I73N1, I79N1, I103N1, I103N2]
  Il := ![[], [I71N1], [I73N1], [I79N1], [], [], [], [], [I103N1, I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
