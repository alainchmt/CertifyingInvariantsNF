
import IdealArithmetic.Examples.NF5_1_16200000_1.RI5_1_16200000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![136747, 443362, -326810, 186804, -593184]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![136747, 443362, -326810, 186804, -593184]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![12, 20, 27, 1, 0], ![9, 61, 2, 0, 1]] where
  M :=![![![136747, 443362, -326810, 186804, -593184], ![-1186368, -904507, 718654, -401272, 1517376], ![3034752, 823814, -766371, 408916, -2043648], ![-1450464, 1177062, -763854, 455623, -960816], ![-2119200, -581294, 539494, -288044, 1434523]]]
  hmulB := by decide  
  f := ![![![-10679, 27146, -17794, 12636, -50016]], ![![-100032, -66909, 16094, 1264, 53184]], ![![106368, -145970, 106547, -80500, 296256]], ![![16260, -69852, 43369, -29637, 122544]], ![![-89733, -59795, 14312, 1216, 47347]]]
  g := ![![![48265, 490918, -62450, 186804, -593184], ![-149664, -1275209, 127138, -401272, 1517376], ![246576, 1750866, -115221, 408916, -2043648], ![25812, 756334, -166329, 455623, -960816], ![-172737, -1228751, 81308, -288044, 1434523]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [36, 20, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 49, 55], [50, 17, 12], [0, 1]]
 g := ![![[47, 55, 17], [47, 44, 25], [6, 36], [51, 9], [33, 1], []], ![[49, 20, 47, 16], [6, 64, 30, 17], [12, 54], [59, 49], [33, 21], [25, 10]], ![[13, 31, 47, 57], [5, 48, 62, 2], [66, 21], [15, 33], [22, 56], [1, 10]]]
 h' := ![![[50, 49, 55], [50, 37, 33], [22, 9, 5], [29, 65, 61], [18, 41, 64], [0, 0, 1], [0, 1]], ![[50, 17, 12], [28, 61, 50], [30, 5, 44], [44, 50, 56], [15, 6, 60], [59, 20, 17], [50, 49, 55]], ![[0, 1], [65, 36, 51], [62, 53, 18], [19, 19, 17], [36, 20, 10], [52, 47, 49], [50, 17, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 16], []]
 b := ![[], [46, 12, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [36, 20, 34, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5352552, -1716442, -6948124, 737393, -9863362]
  a := ![0, 36, -63, 23, -131]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1112970, 8734340, -106433, 737393, -9863362]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10679, -27146, 17794, -12636, 50016]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![10679, -27146, 17794, -12636, 50016]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![63, 13, 1, 0, 0], ![26, 48, 0, 1, 0], ![32, 57, 0, 0, 1]] where
  M :=![![![10679, -27146, 17794, -12636, 50016], ![100032, 66909, -16094, -1264, -53184], ![-106368, 145970, -106547, 80500, -296256], ![-346272, -273534, 79398, -10909, 251952], ![26784, -122810, 75778, -51644, 214343]]]
  hmulB := by decide  
  f := ![![![-136747, -443362, 326810, -186804, 593184]], ![![1186368, 904507, -718654, 401272, -1517376]], ![![56313, -253687, 179297, -103896, 293856]], ![![818518, 458386, -376634, 208187, -842544]], ![![975616, 566427, -463356, 256460, -1029001]]]
  g := ![![![-35557, -37356, 17794, -12636, 50016], ![42518, 50273, -16094, -1264, -53184], ![208855, 217219, -106547, 80500, -296256], ![-195928, -226020, 79398, -10909, 251952], ![-153186, -161889, 75778, -51644, 214343]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [37, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 66], [0, 1]]
 g := ![![[44, 29], [47, 25], [62], [39], [65], [1]], ![[0, 38], [16, 42], [62], [39], [65], [1]]]
 h' := ![![[47, 66], [3, 37], [19, 62], [54, 53], [36, 46], [30, 47], [0, 1]], ![[0, 1], [0, 30], [52, 5], [66, 14], [54, 21], [28, 20], [47, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [18, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [37, 20, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2395274, -29572, 3920800, -592997, 6120664]
  a := ![3, 431, -805, 243, -1672]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6344156, -5543492, 3920800, -592997, 6120664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![136747, 443362, -326810, 186804, -593184]] ![![10679, -27146, 17794, -12636, 50016]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2967, 7180, -4996, 2910, -7852]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-2967, 7180, -4996, 2910, -7852]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![43, 70, 49, 1, 0], ![2, 37, 62, 0, 1]] where
  M :=![![![-2967, 7180, -4996, 2910, -7852], ![-15704, -20481, 15634, -8838, 30580], ![61160, 31216, -25959, 14298, -59212], ![-51360, 7404, -2388, 1927, 8256], ![-42624, -21884, 18184, -10018, 41425]]]
  hmulB := by decide  
  f := ![![![-209, 188, -180, 122, -460]], ![![-920, -783, 150, -50, 628]], ![![1256, -1048, 551, -706, 1940]], ![![-133, -1342, 397, -457, 1624]], ![![602, -1305, 544, -632, 1981]]]
  g := ![![![-1583, 1324, 4778, 2910, -7852], ![4270, -7511, -20384, -8838, 30580], ![-6130, 17200, 41473, 14298, -59212], ![-2123, -6098, -8573, 1927, 8256], ![4300, -12019, -29004, -10018, 41425]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [40, 55, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 66, 19], [18, 4, 52], [0, 1]]
 g := ![![[39, 2, 20], [6, 54, 60], [43, 19, 4], [21, 29], [20, 1], []], ![[33, 1, 23, 45], [49, 5, 31, 49], [31, 39, 15, 3], [8, 37], [1, 16], [1, 6]], ![[6, 59, 25, 59], [47, 48, 8, 46], [24, 63, 44, 34], [3, 43], [48, 25], [39, 6]]]
 h' := ![![[2, 66, 19], [44, 38, 34], [55, 39, 29], [18, 38, 2], [52, 67, 61], [0, 0, 1], [0, 1]], ![[18, 4, 52], [32, 34, 6], [12, 42, 5], [22, 32, 20], [49, 46, 26], [35, 40, 4], [2, 66, 19]], ![[0, 1], [26, 70, 31], [58, 61, 37], [5, 1, 49], [57, 29, 55], [42, 31, 66], [18, 4, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 16], []]
 b := ![[], [4, 3, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [40, 55, 51, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6640143, -2285942, -8775056, 833090, -12322533]
  a := ![1, 34, -62, 20, -129]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-250957, 5568049, 10061980, 833090, -12322533]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 20, -12, 8, -34]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-3, 20, -12, 8, -34]] 
 ![![71, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![-3, 20, -12, 8, -34], ![-68, -37, 6, 4, 22], ![44, -112, 73, -52, 206], ![240, 156, -36, -5, -120], ![0, 88, -50, 32, -143]]]
  hmulB := by decide  
  f := ![![![-221, -132, 88, -56, 206]], ![![-44, -29, 18, -12, 42]], ![![-96, -48, 29, -20, 74]], ![![-172, -108, 68, -45, 160]], ![![-117, -76, 50, -32, 115]]]
  g := ![![![13, 20, -12, 8, -34], ![-10, -37, 6, 4, 22], ![-78, -112, 73, -52, 206], ![52, 156, -36, -5, -120], ![55, 88, -50, 32, -143]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![75, 24, 92, -10, 130]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![75, 24, 92, -10, 130]] 
 ![![71, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![68, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![75, 24, 92, -10, 130], ![260, 107, 304, -26, 410], ![820, 336, 1051, -82, 1426], ![1296, 456, 1704, -157, 2376], ![168, 44, 206, -26, 299]]]
  hmulB := by decide  
  f := ![![![-763, -2464, 1816, -1038, 3298]], ![![-208, -901, 660, -378, 1182]], ![![-968, -2424, 1799, -1026, 3318]], ![![-188, -1064, 776, -445, 1376]], ![![-189, -1100, 802, -460, 1421]]]
  g := ![![![-153, 24, 92, -10, 130], ![-510, 107, 304, -26, 410], ![-1758, 336, 1051, -82, 1426], ![-2836, 456, 1704, -157, 2376], ![-341, 44, 206, -26, 299]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-2967, 7180, -4996, 2910, -7852]] ![![-3, 20, -12, 8, -34]]
  ![![-763, -2464, 1816, -1038, 3298]] where
 M := ![![![-763, -2464, 1816, -1038, 3298]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-763, -2464, 1816, -1038, 3298]] ![![75, 24, 92, -10, 130]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![217, 114, -93, 52, -213]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![217, 114, -93, 52, -213]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![24, 19, 21, 33, 1]] where
  M :=![![![217, 114, -93, 52, -213], ![-426, -27, 47, -20, 183], ![366, -422, 302, -172, 435], ![648, 732, -528, 307, -1068], ![-246, 298, -197, 118, -284]]]
  hmulB := by decide  
  f := ![![![1, 6, -3, 2, -9]], ![![-18, -7, 1, 2, 3]], ![![6, -34, 24, -14, 63]], ![![72, 36, 0, -5, -12]], ![![30, 7, 6, -5, 10]]]
  g := ![![![73, 57, 60, 97, -213], ![-66, -48, -52, -83, 183], ![-138, -119, -121, -199, 435], ![360, 288, 300, 487, -1068], ![90, 78, 79, 130, -284]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 4 2 6 [44, 5, 19, 25, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 30, 23, 5], [67, 0, 59, 13], [61, 42, 64, 55], [0, 1]]
 g := ![![[35, 63, 14, 57], [57, 19, 25], [60, 13, 50], [63, 28, 71, 41], [1], []], ![[26, 6, 19, 26, 3, 42], [8, 31, 4], [57, 1, 46], [25, 46, 31, 15, 62, 26], [52, 40, 9], [9, 43, 25]], ![[0, 44, 13, 13, 59, 60], [15, 43, 38], [13, 33, 8], [11, 39, 27, 35, 12, 17], [45, 39, 71], [20, 10, 23]], ![[40, 43, 11, 15, 28, 61], [11, 31, 2], [1, 24, 72], [15, 3, 72, 46, 64, 1], [68, 18, 6], [6, 35, 32]]]
 h' := ![![[66, 30, 23, 5], [38, 53, 7, 35], [65, 27, 67, 68], [2, 24, 67, 59], [29, 68, 54, 48], [0, 0, 1], [0, 1]], ![[67, 0, 59, 13], [51, 57, 51, 60], [44, 39, 51, 2], [17, 28, 12, 51], [7, 71, 41, 7], [18, 52, 41, 70], [66, 30, 23, 5]], ![[61, 42, 64, 55], [32, 15, 63, 46], [53, 49, 37, 44], [25, 43, 17, 9], [66, 72, 30, 20], [32, 44, 40, 61], [67, 0, 59, 13]], ![[0, 1], [11, 21, 25, 5], [35, 31, 64, 32], [15, 51, 50, 27], [20, 8, 21, 71], [26, 50, 64, 15], [61, 42, 64, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [26, 69, 57], []]
 b := ![[], [], [8, 64, 54, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 4
  hpos := by decide
  P := [44, 5, 19, 25, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2401865666912, 867990661486, 3054573402165, -283071331718, 4236663356947]
  a := ![1, -178, 320, -109, 665]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1359973354792, -1090802919459, -1176922699914, -1919081672753, 4236663356947]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 28398241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 6, -3, 2, -9]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![1, 6, -3, 2, -9]] 
 ![![73, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![1, 6, -3, 2, -9], ![-18, -7, 1, 2, 3], ![6, -34, 24, -14, 63], ![72, 36, 0, -5, -12], ![6, 26, -13, 8, -38]]]
  hmulB := by decide  
  f := ![![![217, 114, -93, 52, -213]], ![![12, 9, -7, 4, -15]], ![![115, 52, -43, 24, -102]], ![![104, 60, -48, 27, -108]], ![![65, 40, -32, 18, -71]]]
  g := ![![![3, 6, -3, 2, -9], ![-2, -7, 1, 2, 3], ![-23, -34, 24, -14, 63], ![4, 36, 0, -5, -12], ![13, 26, -13, 8, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![217, 114, -93, 52, -213]] ![![1, 6, -3, 2, -9]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1269, 479, 1593, -142, 2192]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![1269, 479, 1593, -142, 2192]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![6, 30, 25, 1, 0], ![48, 4, 47, 0, 1]] where
  M :=![![![1269, 479, 1593, -142, 2192], ![4384, 1664, 5493, -488, 7552], ![15104, 5741, 18952, -1678, 26048], ![23856, 9045, 29967, -2657, 41208], ![2760, 1039, 3469, -310, 4777]]]
  hmulB := by decide  
  f := ![![![83, 45, -37, 20, -80]], ![![-160, -14, 25, -14, 80]], ![![160, -117, 72, -40, 64]], ![![-2, -36, 27, -15, 40]], ![![136, -42, 21, -12, -7]]]
  g := ![![![-1305, -51, -1239, -142, 2192], ![-4496, -176, -4269, -488, 7552], ![-15508, -609, -14726, -1678, 26048], ![-24534, -963, -23296, -2657, 41208], ![-2844, -111, -2700, -310, 4777]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [19, 5, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 33, 56], [32, 45, 23], [0, 1]]
 g := ![![[24, 77, 20], [71, 5, 16], [54, 0, 1], [35, 77, 62], [50, 1], []], ![[15, 63, 33, 14], [53, 32, 77, 63], [5, 15, 44, 6], [38, 14, 45, 47], [66, 50], [47, 55]], ![[16, 76, 22, 23], [36, 62, 49, 46], [78, 69, 70, 18], [57, 67, 26, 50], [8, 62], [1, 55]]]
 h' := ![![[18, 33, 56], [73, 25, 40], [1, 29, 4], [46, 25, 78], [77, 47, 46], [0, 0, 1], [0, 1]], ![[32, 45, 23], [41, 68, 40], [64, 36, 66], [38, 48, 12], [29, 5, 41], [63, 66, 45], [18, 33, 56]], ![[0, 1], [72, 65, 78], [51, 14, 9], [78, 6, 68], [16, 27, 71], [57, 13, 33], [32, 45, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 19], []]
 b := ![[], [43, 40, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [19, 5, 29, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12672854, -4751978, -13326147, 1774449, -18177288]
  a := ![-1, 70, -111, 53, -232]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10749244, 186376, 10084116, 1774449, -18177288]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, -13, -44, 4, -61]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-33, -13, -44, 4, -61]] 
 ![![79, 0, 0, 0, 0], ![53, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![73, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-33, -13, -44, 4, -61], ![-122, -44, -152, 14, -209], ![-418, -163, -517, 44, -709], ![-648, -245, -827, 75, -1140], ![-74, -25, -98, 10, -136]]]
  hmulB := by decide  
  f := ![![![-103, -195, 78, -36, 241]], ![![-63, -131, 54, -26, 166]], ![![-37, -70, 27, -12, 84]], ![![-121, -182, 67, -27, 211]], ![![-32, -55, 22, -10, 68]]]
  g := ![![![38, -13, -44, 4, -61], ![130, -44, -152, 14, -209], ![454, -163, -517, 44, -709], ![713, -245, -827, 75, -1140], ![81, -25, -98, 10, -136]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-145, 56, -32, 20, -20]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-145, 56, -32, 20, -20]] 
 ![![79, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![56, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-145, 56, -32, 20, -20], ![-40, -297, 216, -124, 380], ![760, 664, -521, 292, -1076], ![-1056, -216, 216, -113, 624], ![-528, -464, 364, -204, 751]]]
  hmulB := by decide  
  f := ![![![417, 216, 16, -28, -52]], ![![289, 159, 8, -16, -48]], ![![272, 136, 23, -20, -12]], ![![300, 120, 40, -33, 32]], ![![111, 56, 4, -8, -13]]]
  g := ![![![-27, 56, -32, 20, -20], ![53, -297, 216, -124, 380], ![-44, 664, -521, 292, -1076], ![-76, -216, 216, -113, 624], ![31, -464, 364, -204, 751]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![1269, 479, 1593, -142, 2192]] ![![-33, -13, -44, 4, -61]]
  ![![-836381, -317242, -1049607, 93144, -1443189]] where
 M := ![![![-836381, -317242, -1049607, 93144, -1443189]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-836381, -317242, -1049607, 93144, -1443189]] ![![-145, 56, -32, 20, -20]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-92667, -34918, -116525, 10428, -160291]]]
 hmul := by decide  
 g := ![![![![-1173, -442, -1475, 132, -2029]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9559, 2733, -1419, 920, -134]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-9559, 2733, -1419, 920, -134]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![67, 5, 62, 8, 1]] where
  M :=![![![-9559, 2733, -1419, 920, -134], ![-268, -17284, 12451, -7170, 21410], ![42820, 40963, -31924, 17932, -65030], ![-64896, -16157, 15337, -8139, 41904], ![-29732, -28619, 22293, -12524, 45371]]]
  hmulB := by decide  
  f := ![![![-117, -53, -121, 10, -158]], ![![-316, -150, -417, 24, -550]], ![![-1100, -351, -1536, 146, -2174]], ![![-2016, -667, -2425, 261, -3408]], ![![-1133, -380, -1507, 144, -2117]]]
  g := ![![![-7, 41, 83, 24, -134], ![-17286, -1498, -15843, -2150, 21410], ![53010, 4411, 48192, 6484, -65030], ![-34608, -2719, -31117, -4137, 41904], ![-36983, -3078, -33623, -4524, 45371]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [48, 16, 66, 27, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 69, 82, 66], [54, 54, 6, 24], [23, 42, 78, 76], [0, 1]]
 g := ![![[16, 66, 48, 40], [55, 21, 49, 28], [57, 50, 21], [6, 10, 1], [56, 1], []], ![[21, 45, 55, 2, 36, 73], [32, 45, 5, 52, 5, 80], [75, 58, 23], [23, 25, 63], [77, 63, 4, 81, 74, 20], [17, 33, 40]], ![[46, 36, 19, 49, 46, 53], [25, 51, 48, 61, 3, 42], [70, 49, 25], [4, 27, 3], [68, 28, 13, 37, 29, 58], [3, 8, 78]], ![[38, 37, 32, 66, 37, 47], [71, 36, 10, 16, 5, 58], [47, 45, 9], [6, 33, 77], [70, 43, 63, 16, 61, 47], [71, 75, 49]]]
 h' := ![![[62, 69, 82, 66], [16, 42, 82, 17], [41, 74, 45, 32], [72, 80, 47, 41], [51, 52, 23, 82], [0, 0, 1], [0, 1]], ![[54, 54, 6, 24], [20, 15, 73, 5], [82, 7, 73, 7], [69, 62, 78, 40], [54, 32, 37, 48], [40, 60, 71, 38], [62, 69, 82, 66]], ![[23, 42, 78, 76], [7, 49, 23, 71], [53, 73, 48, 8], [33, 60, 6, 5], [15, 75, 15, 70], [33, 5, 75, 55], [54, 54, 6, 24]], ![[0, 1], [6, 60, 71, 73], [36, 12, 0, 36], [47, 47, 35, 80], [70, 7, 8, 49], [26, 18, 19, 73], [23, 42, 78, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [71, 19, 39], []]
 b := ![[], [], [3, 16, 69, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [48, 16, 66, 27, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-649100624, -384130312, 122012872, -18014592, 396664768]
  a := ![0, -42, 54, -42, 112]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-328019760, -28523544, -294833768, -38449792, 396664768]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-117, -53, -121, 10, -158]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-117, -53, -121, 10, -158]] 
 ![![83, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![58, 0, 0, 0, 1]] where
  M :=![![![-117, -53, -121, 10, -158], ![-316, -150, -417, 24, -550], ![-1100, -351, -1536, 146, -2174], ![-2016, -667, -2425, 261, -3408], ![-292, -141, -257, 22, -323]]]
  hmulB := by decide  
  f := ![![![-9559, 2733, -1419, 920, -134]], ![![-5992, 1504, -739, 490, 174]], ![![-3515, 1646, -983, 604, -840]], ![![-7692, 1781, -841, 567, 408]], ![![-7038, 1565, -723, 492, 453]]]
  g := ![![![186, -53, -121, 10, -158], ![633, -150, -417, 24, -550], ![2268, -351, -1536, 146, -2174], ![3609, -667, -2425, 261, -3408], ![403, -141, -257, 22, -323]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-9559, 2733, -1419, 920, -134]] ![![-117, -53, -121, 10, -158]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, -1286, 587, -490, 1901]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![79, -1286, 587, -490, 1901]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![18, 14, 1, 0, 0], ![52, 45, 0, 1, 0], ![43, 75, 0, 0, 1]] where
  M :=![![![79, -1286, 587, -490, 1901], ![3802, 2195, -973, -178, -2255], ![-4510, 6330, -6528, 3454, -15547], ![-17448, -10932, -672, 473, 3708], ![-150, -5586, 2793, -2000, 8486]]]
  hmulB := by decide  
  f := ![![![145383, 22110, -24227, 12396, -76495]], ![![-152990, 110879, -71019, 42556, -84971]], ![![3428, 17004, -12430, 7124, -22135]], ![![15150, 73143, -53491, 30653, -95351]], ![![-57375, 107541, -74089, 43298, -113226]]]
  g := ![![![-750, -1461, 587, -490, 1901], ![1433, 2168, -973, -178, -2255], ![6763, 12453, -6528, 3454, -15547], ![-2128, -3381, -672, 473, 3708], ![-3498, -6642, 2793, -2000, 8486]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [24, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 88], [0, 1]]
 g := ![![[39, 72], [8], [49], [45, 80], [13, 69], [1]], ![[20, 17], [8], [49], [14, 9], [43, 20], [1]]]
 h' := ![![[43, 88], [36, 28], [36, 50], [77, 82], [44, 13], [65, 43], [0, 1]], ![[0, 1], [83, 61], [50, 39], [43, 7], [69, 76], [45, 46], [43, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [5, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [24, 46, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![37955, 12568, 17894, -1267, 22148]
  a := ![13, 62, -101, 45, -211]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13153, -20697, 17894, -1267, 22148]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -34, 15, -8, 45]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-17, -34, 15, -8, 45]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![22, 24, 1, 0, 0], ![3, 35, 0, 1, 0], ![66, 39, 0, 0, 1]] where
  M :=![![![-17, -34, 15, -8, 45], ![90, 9, 13, -20, 33], ![66, 210, -112, 60, -315], ![-360, -80, -44, 63, -84], ![-86, -142, 61, -30, 182]]]
  hmulB := by decide  
  f := ![![![71, -86, 57, -34, 81]], ![![162, 285, -217, 122, -411]], ![![52, 50, -40, 22, -81]], ![![75, 109, -84, 47, -162]], ![![130, 65, -56, 30, -127]]]
  g := ![![![-37, -21, 15, -8, 45], ![-26, -10, 13, -20, 33], ![260, 147, -112, 60, -315], ![67, 23, -44, 63, -84], ![-150, -86, 61, -30, 182]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [23, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 88], [0, 1]]
 g := ![![[35, 45], [21], [10], [57, 34], [31, 16], [1]], ![[33, 44], [21], [10], [10, 55], [56, 73], [1]]]
 h' := ![![[85, 88], [62, 57], [79, 33], [24, 59], [88, 37], [66, 85], [0, 1]], ![[0, 1], [12, 32], [36, 56], [55, 30], [29, 52], [82, 4], [85, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [75, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [23, 4, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![572, 466, 2631, -53, 3696]
  a := ![-1, 4, -12, -1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3383, -2303, 2631, -53, 3696]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4027, 2011, -2043, 1766, -5520]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![-4027, 2011, -2043, 1766, -5520]] 
 ![![89, 0, 0, 0, 0], ![51, 1, 0, 0, 0], ![69, 0, 1, 0, 0], ![84, 0, 0, 1, 0], ![67, 0, 0, 0, 1]] where
  M :=![![![-4027, 2011, -2043, 1766, -5520], ![-11040, -12912, 4877, -1876, 14784], ![29568, -7815, 10804, -10434, 28896], ![34416, 48713, -20389, 8931, -60360], ![-14632, 10459, -9199, 7566, -25151]]]
  hmulB := by decide  
  f := ![![![1114981, 914879, -722031, 403984, -1506000]], ![![605079, 513819, -404302, 226418, -838656]], ![![913089, 696108, -553079, 308820, -1167792]], ![![1069044, 911825, -717205, 401697, -1486680]], ![![805231, 697772, -548104, 307112, -1133327]]]
  g := ![![![2875, 2011, -2043, 1766, -5520], ![-5865, -12912, 4877, -1876, 14784], ![-15471, -7815, 10804, -10434, 28896], ![25290, 48713, -20389, 8931, -60360], ![12767, 10459, -9199, 7566, -25151]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![79, -1286, 587, -490, 1901]] ![![-17, -34, 15, -8, 45]]
  ![![-65427, -121732, 56244, -27592, 163354]] where
 M := ![![![-65427, -121732, 56244, -27592, 163354]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![-65427, -121732, 56244, -27592, 163354]] ![![-4027, 2011, -2043, 1766, -5520]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![-69383599, 1365113417, -792479585, 515487466, -2256365558]]]
 hmul := by decide  
 g := ![![![![-779591, 15338353, -8904265, 5791994, -25352422]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![457, 180, 561, -46, 767]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![457, 180, 561, -46, 767]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![57, 77, 67, 59, 1]] where
  M :=![![![457, 180, 561, -46, 767], ![1534, 573, 1975, -182, 2731], ![5462, 2052, 6764, -602, 9287], ![8520, 3290, 10658, -927, 14628], ![938, 372, 1237, -108, 1708]]]
  hmulB := by decide  
  f := ![![![9, 4, -1, 0, -5]], ![![-10, 13, -11, 8, -25]], ![![-50, -52, 26, -12, 67]], ![![72, -10, 14, -15, 36]], ![![7, -29, 17, -11, 45]]]
  g := ![![![-446, -607, -524, -467, 767], ![-1589, -2162, -1866, -1663, 2731], ![-5401, -7351, -6345, -5655, 9287], ![-8508, -11578, -9994, -8907, 14628], ![-994, -1352, -1167, -1040, 1708]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [52, 15, 16, 72, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 56, 27, 12], [42, 41, 48, 91], [85, 96, 22, 91], [0, 1]]
 g := ![![[43, 89, 10, 95], [78, 70, 96], [2, 95, 72], [58, 71, 88], [27, 25, 1], []], ![[69, 11, 88, 33, 2, 9], [60, 71, 70], [79, 82, 16], [87, 20, 72], [17, 5, 86], [48, 65, 35, 13, 59, 79]], ![[53, 56, 8, 29, 79, 81], [61, 94, 49], [72, 6, 64], [86, 92, 65], [82, 33, 9], [75, 42, 7, 6, 75, 75]], ![[51, 52, 39, 34, 81, 36], [76, 20, 3], [91, 3, 95], [5, 17, 31], [64, 37, 18], [14, 45, 75, 31, 80, 75]]]
 h' := ![![[92, 56, 27, 12], [24, 1, 61, 80], [43, 30, 22, 22], [70, 8, 32, 84], [51, 41, 14, 66], [0, 0, 0, 1], [0, 1]], ![[42, 41, 48, 91], [70, 41, 20, 5], [38, 75, 11, 78], [84, 86, 33, 4], [90, 55, 61, 84], [95, 3, 19, 38], [92, 56, 27, 12]], ![[85, 96, 22, 91], [18, 60, 78, 36], [38, 58, 37, 7], [75, 42, 39, 89], [52, 70, 2, 29], [57, 69, 65, 3], [42, 41, 48, 91]], ![[0, 1], [78, 92, 35, 73], [21, 31, 27, 87], [0, 58, 90, 17], [58, 28, 20, 15], [66, 25, 13, 55], [85, 96, 22, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [70, 72, 86], []]
 b := ![[], [], [45, 37, 27, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [52, 15, 16, 72, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14800986, 10444838, 15707900, -12512, 16987296]
  a := ![3, -18, 28, -15, 56]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9829638, -13377082, -11571556, -10332608, 16987296]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -4, 1, 0, 5]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-9, -4, 1, 0, 5]] 
 ![![97, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![41, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![-9, -4, 1, 0, 5], ![10, -13, 11, -8, 25], ![50, 52, -26, 12, -67], ![-72, 10, -14, 15, -36], ![-38, -32, 15, -6, 38]]]
  hmulB := by decide  
  f := ![![![-457, -180, -561, 46, -767]], ![![-176, -69, -217, 18, -297]], ![![-94, -36, -116, 10, -159]], ![![-281, -110, -347, 29, -475]], ![![-396, -156, -487, 40, -666]]]
  g := ![![![-3, -4, 1, 0, 5], ![-14, -13, 11, -8, 25], ![36, 52, -26, 12, -67], ![21, 10, -14, 15, -36], ![-20, -32, 15, -6, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![457, 180, 561, -46, 767]] ![![-9, -4, 1, 0, 5]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0, 0, 0]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]] where
  M :=![![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 5 2 6 [60, 17, 32, 85, 21, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 37, 64, 74, 10], [48, 8, 50, 50, 11], [91, 31, 54, 7, 21], [86, 24, 34, 71, 59], [0, 1]]
 g := ![![[95, 88, 43, 79, 82], [27, 1, 86, 96], [34, 12, 12, 33, 30], [29, 87, 74, 82], [80, 1], []], ![[37, 39, 32, 5, 97, 81, 62, 38], [85, 26, 98, 82], [78, 95, 25, 1, 98, 23, 60, 60], [69, 4, 84, 68], [19, 0, 13, 58], [14, 38, 68, 85, 32, 55, 89, 91]], ![[95, 61, 72, 73, 71, 51, 53, 34], [44, 36, 86, 14], [11, 77, 95, 28, 87, 87, 81, 40], [30, 27, 82, 37], [77, 94, 51, 31], [46, 18, 61, 63, 13, 22, 97, 18]], ![[71, 27, 48, 89, 23, 82, 45, 71], [94, 16, 27, 9], [25, 75, 77, 10, 65, 63, 63, 81], [68, 88, 23, 1], [62, 72, 41, 24], [58, 61, 42, 26, 20, 9, 14, 70]], ![[19, 49, 22, 78, 64, 69, 56, 28], [84, 6, 0, 47], [88, 33, 17, 37, 20, 58, 18, 91], [100, 17, 77, 97], [26, 82, 77, 1], [72, 7, 59, 69, 36, 34, 56, 46]]]
 h' := ![![[57, 37, 64, 74, 10], [93, 31, 87, 37, 53], [81, 62, 54, 54, 55], [59, 74, 14, 26, 38], [48, 95, 49, 36, 53], [0, 0, 0, 1], [0, 1]], ![[48, 8, 50, 50, 11], [28, 17, 88, 38, 78], [52, 31, 97, 61, 53], [83, 31, 42, 12, 39], [48, 95, 91, 4, 88], [28, 76, 91, 50, 82], [57, 37, 64, 74, 10]], ![[91, 31, 54, 7, 21], [42, 15, 42, 54, 7], [37, 90, 40, 88, 32], [99, 32, 18, 57, 27], [9, 64, 19, 6, 80], [65, 5, 19, 34, 43], [48, 8, 50, 50, 11]], ![[86, 24, 34, 71, 59], [38, 80, 5, 24, 35], [74, 11, 76, 36, 3], [61, 28, 79, 76, 50], [0, 9, 86, 22, 1], [65, 8, 36, 65, 78], [91, 31, 54, 7, 21]], ![[0, 1], [5, 59, 81, 49, 29], [46, 8, 36, 64, 59], [27, 37, 49, 31, 48], [13, 40, 58, 33, 81], [82, 12, 56, 52, 100], [86, 24, 34, 71, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 92, 8, 92], [], [], []]
 b := ![[], [29, 53, 93, 68, 11], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 5
  hpos := by decide
  P := [60, 17, 32, 85, 21, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1167553940000, 451130387702, 1428622840095, -127354207548, 1955540334389]
  a := ![1, -48, 78, -35, 163]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11559940000, 4466637502, 14144780595, -1260932748, 19361785489]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5481, 3118, -3090, 2542, -8264]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-5481, 3118, -3090, 2542, -8264]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![100, 53, 1, 0, 0], ![28, 88, 0, 1, 0], ![74, 101, 0, 0, 1]] where
  M :=![![![-5481, 3118, -3090, 2542, -8264], ![-16528, -18101, 6288, -2362, 19688], ![39376, -13394, 14981, -14990, 41752], ![50016, 67818, -29658, 11885, -85344], ![-19560, 15926, -13606, 10822, -37069]]]
  hmulB := by decide  
  f := ![![![553009, 5454, -35570, 14554, -193960]], ![![-387920, 609521, -416332, 244010, -620504]], ![![325244, 300565, -234859, 131808, -480864]], ![![-152476, 534422, -375774, 218117, -607584]], ![![25246, 614417, -443498, 255224, -766429]]]
  g := ![![![8193, 7552, -3090, 2542, -8264], ![-19768, -20699, 6288, -2362, 19688], ![-40084, -35973, 14981, -14990, 41752], ![87364, 89452, -29658, 11885, -85344], ![36710, 34259, -13606, 10822, -37069]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [44, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 102], [0, 1]]
 g := ![![[9, 60], [71, 19], [99, 19], [82], [36], [16, 1]], ![[42, 43], [66, 84], [94, 84], [82], [36], [32, 102]]]
 h' := ![![[16, 102], [69, 67], [73, 88], [79, 15], [44, 59], [17, 6], [0, 1]], ![[0, 1], [8, 36], [39, 15], [10, 88], [61, 44], [10, 97], [16, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [62, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [44, 87, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![440, 395, -445, 322, -912]
  a := ![4, 3, -4, 3, -8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1004, 852, -445, 322, -912]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-407, 1123, -695, 514, -2002]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-407, 1123, -695, 514, -2002]] 
 ![![103, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![46, 0, 0, 1, 0], ![86, 0, 0, 0, 1]] where
  M :=![![![-407, 1123, -695, 514, -2002], ![-4004, -2698, 771, 44, 2326], ![4652, -5867, 4764, -3330, 12686], ![14688, 11369, -2605, 381, -9408], ![-1024, 5055, -3029, 2106, -8675]]]
  hmulB := by decide  
  f := ![![![499455, -118527, 56695, -38024, -22898]], ![![38348, -1000, -1475, 438, -11750]], ![![169171, -64970, 37063, -23168, 22864]], ![![254814, -44281, 17277, -12689, -31652]], ![![430862, -84931, 36449, -25624, -41115]]]
  g := ![![![1614, 1123, -695, 514, -2002], ![-2083, -2698, 771, 44, 2326], ![-10408, -5867, 4764, -3330, 12686], ![7931, 11369, -2605, 381, -9408], ![7047, 5055, -3029, 2106, -8675]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![76255, 12297, -13211, 6792, -40986]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![76255, 12297, -13211, 6792, -40986]] 
 ![![103, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![53, 0, 1, 0, 0], ![83, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![76255, 12297, -13211, 6792, -40986], ![-81972, 56486, -35949, 21590, -41922], ![-83844, -227129, 168210, -96004, 308550], ![349536, 195679, -160787, 88875, -359712], ![57364, 158273, -117155, 66876, -214651]]]
  hmulB := by decide  
  f := ![![![-6071, -5021, -16141, -370, -20442]], ![![-1340, -772, -3191, 44, -4254]], ![![-5281, -3296, -10417, 92, -13476]], ![![-7651, -5694, -15904, -209, -19938]], ![![-639, -668, -2020, -92, -2497]]]
  g := ![![![4532, 12297, -13211, 6792, -40986], ![-3993, 56486, -35949, 21590, -41922], ![-7676, -227129, 168210, -96004, 308550], ![22530, 195679, -160787, 88875, -359712], ![5288, 158273, -117155, 66876, -214651]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2

def I103N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29439, 16716, -10342, 6274, -10652]] i)))

def SI103N3: IdealEqSpanCertificate' Table ![![-29439, 16716, -10342, 6274, -10652]] 
 ![![103, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![-29439, 16716, -10342, 6274, -10652], ![-21304, -73047, 53774, -30750, 97316], ![194632, 150404, -119349, 66666, -251420], ![-240768, -33456, 37848, -19219, 122784], ![-135348, -105176, 83416, -46602, 175559]]]
  hmulB := by decide  
  f := ![![![37351, 146740, -75322, 43918, -217660]], ![![5202, 35801, -19238, 11718, -55276]], ![![15653, 55568, -28195, 16244, -81592]], ![![22868, 34688, -14720, 6781, -43664]], ![![20703, 78716, -40258, 23388, -116389]]]
  g := ![![![4069, 16716, -10342, 6274, -10652], ![-47476, -73047, 53774, -30750, 97316], ![127611, 150404, -119349, 66666, -251420], ![-67492, -33456, 37848, -19219, 122784], ![-89087, -105176, 83416, -46602, 175559]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N3 : Nat.card (O ⧸ I103N3) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N3)

lemma isPrimeI103N3 : Ideal.IsPrime I103N3 := prime_ideal_of_norm_prime hp103.out _ NI103N3
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-5481, 3118, -3090, 2542, -8264]] ![![-407, 1123, -695, 514, -2002]]
  ![![21170847, -9313019, 9902259, -8825824, 26800754]] where
 M := ![![![21170847, -9313019, 9902259, -8825824, 26800754]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![21170847, -9313019, 9902259, -8825824, 26800754]] ![![76255, 12297, -13211, 6792, -40986]]
  ![![-37351, -146740, 75322, -43918, 217660]] where
 M := ![![![-37351, -146740, 75322, -43918, 217660]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N2 : IdealMulLeCertificate' Table 
  ![![-37351, -146740, 75322, -43918, 217660]] ![![-29439, 16716, -10342, 6274, -10652]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![-103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2, I103N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
    exact isPrimeI103N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1 ⊙ MulI103N2)


lemma PB251I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB251I2 : PrimesBelowBoundCertificateInterval O 61 103 251 where
  m := 9
  g := ![2, 3, 2, 3, 2, 3, 2, 1, 4]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB251I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1, I103N2, I103N3]
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
    · exact ![357911, 71, 71]
    · exact ![28398241, 73]
    · exact ![493039, 79, 79]
    · exact ![47458321, 83]
    · exact ![7921, 7921, 89]
    · exact ![88529281, 97]
    · exact ![10510100501]
    · exact ![10609, 103, 103, 103]
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
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
      exact NI103N3
  β := ![I71N1, I71N2, I73N1, I79N1, I79N2, I83N1, I89N2, I97N1, I103N1, I103N2, I103N3]
  Il := ![[], [I71N1, I71N2], [I73N1], [I79N1, I79N2], [I83N1], [I89N2], [I97N1], [], [I103N1, I103N2, I103N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
