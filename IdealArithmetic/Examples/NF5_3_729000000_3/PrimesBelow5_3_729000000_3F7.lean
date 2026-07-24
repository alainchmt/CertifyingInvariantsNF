
import IdealArithmetic.Examples.NF5_3_729000000_3.RI5_3_729000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18685, -11277, 796, -1693, 3656]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![18685, -11277, 796, -1693, 3656]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![140, 162, 1, 0, 0], ![23, 106, 0, 1, 0], ![37, 69, 0, 0, 1]] where
  M :=![![![18685, -11277, 796, -1693, 3656], ![-14624, 8783, -618, 1322, -2846], ![5692, -3453, 245, -517, 1120], ![5072, -3060, 216, -459, 992], ![5904, -3550, 250, -534, 1151]]]
  hmulB := by decide  
  f := ![![![-21, -5, 14, 31, 14]], ![![-56, 27, 74, -48, 214]], ![![-40, 11, 47, -11, 118]], ![![-21, 9, 26, -12, 74]], ![![-15, 6, 18, -7, 51]]]
  g := ![![![-608, -685, 796, -1693, 3656], ![472, 531, -618, 1322, -2846], ![-187, -211, 245, -517, 1120], ![-165, -186, 216, -459, 992], ![-191, -215, 250, -534, 1151]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 2 2 8 [281, 218, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 310], [0, 1]]
 g := ![![[283, 7], [292, 52], [249, 267], [224], [244, 104], [11, 252], [252], [1]], ![[1, 304], [152, 259], [200, 44], [224], [275, 207], [122, 59], [252], [1]]]
 h' := ![![[93, 310], [52, 140], [6, 36], [88, 189], [167, 49], [19, 112], [63, 93], [30, 93], [0, 1]], ![[0, 1], [10, 171], [244, 275], [249, 122], [59, 262], [172, 199], [4, 218], [282, 218], [93, 310]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [78, 209]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 2
  hpos := by decide
  P := [281, 218, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3655, -3797, 5841, -359, -1913]
  a := ![0, -8, -3, 2, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2387, -2508, 5841, -359, -1913]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 96721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12995, -6517, 402, -1084, 2074]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![12995, -6517, 402, -1084, 2074]] 
 ![![311, 0, 0, 0, 0], ![193, 1, 0, 0, 0], ![191, 0, 1, 0, 0], ![132, 0, 0, 1, 0], ![295, 0, 0, 0, 1]] where
  M :=![![![12995, -6517, 402, -1084, 2074], ![-8296, 7081, -590, 898, -2356], ![4712, -1189, 13, -310, 338], ![3472, -1826, 120, -295, 586], ![3532, -2664, 214, -357, 881]]]
  hmulB := by decide  
  f := ![![![5325, 4009, -11048, 6732, -2054]], ![![3331, 2526, -6870, 4070, -1158]], ![![3037, 2244, -6397, 4170, -1468]], ![![2660, 2002, -5520, 3367, -1030]], ![![5281, 4041, -10810, 6171, -1583]]]
  g := ![![![2332, -6517, 402, -1084, 2074], ![-2205, 7081, -590, 898, -2356], ![556, -1189, 13, -310, 338], ![640, -1826, 120, -295, 586], ![849, -2664, 214, -357, 881]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N1 : Nat.card (O ⧸ I311N1) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N1)

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := prime_ideal_of_norm_prime hp311.out _ NI311N1

def I311N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![490719, 121620, -673280, -148362, -475180]] i)))

def SI311N2: IdealEqSpanCertificate' Table ![![490719, 121620, -673280, -148362, -475180]] 
 ![![311, 0, 0, 0, 0], ![194, 1, 0, 0, 0], ![153, 0, 1, 0, 0], ![301, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![490719, 121620, -673280, -148362, -475180], ![1900720, 471075, -2607840, -574656, -1840532], ![3681064, 912316, -5050521, -1112918, -3564500], ![6178640, 1531316, -8477264, -1868025, -5982988], ![5414632, 1341964, -7429024, -1637038, -5243173]]]
  hmulB := by decide  
  f := ![![![-983, 3788, -352, 430, -1492]], ![![-594, 2371, -224, 268, -932]], ![![-481, 1872, -169, 208, -736]], ![![-957, 3664, -336, 425, -1456]], ![![-152, 588, -64, 70, -229]]]
  g := ![![![473871, 121620, -673280, -148362, -475180], ![1835462, 471075, -2607840, -574656, -1840532], ![3554681, 912316, -5050521, -1112918, -3564500], ![5966507, 1531316, -8477264, -1868025, -5982988], ![5228730, 1341964, -7429024, -1637038, -5243173]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N2 : Nat.card (O ⧸ I311N2) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N2)

lemma isPrimeI311N2 : Ideal.IsPrime I311N2 := prime_ideal_of_norm_prime hp311.out _ NI311N2

def I311N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2339, -579, 3208, 707, 2264]] i)))

def SI311N3: IdealEqSpanCertificate' Table ![![-2339, -579, 3208, 707, 2264]] 
 ![![311, 0, 0, 0, 0], ![222, 1, 0, 0, 0], ![238, 0, 1, 0, 0], ![217, 0, 0, 1, 0], ![159, 0, 0, 0, 1]] where
  M :=![![![-2339, -579, 3208, 707, 2264], ![-9056, -2245, 12426, 2738, 8770], ![-17540, -4347, 24065, 5303, 16984], ![-29440, -7296, 40392, 8901, 28508], ![-25800, -6394, 35398, 7800, 24983]]]
  hmulB := by decide  
  f := ![![![-5925, -6071, 866, -125, 2222]], ![![-4258, -4365, 622, -90, 1598]], ![![-4558, -4671, 667, -97, 1710]], ![![-4139, -4241, 606, -86, 1550]], ![![-3021, -3095, 440, -63, 1133]]]
  g := ![![![-3700, -579, 3208, 707, 2264], ![-14330, -2245, 12426, 2738, 8770], ![-27753, -4347, 24065, 5303, 16984], ![-46583, -7296, 40392, 8901, 28508], ![-40823, -6394, 35398, 7800, 24983]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N3 : Nat.card (O ⧸ I311N3) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N3)

lemma isPrimeI311N3 : Ideal.IsPrime I311N3 := prime_ideal_of_norm_prime hp311.out _ NI311N3
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![18685, -11277, 796, -1693, 3656]] ![![12995, -6517, 402, -1084, 2074]]
  ![![347151215, -209217192, 14754372, -31433803, 67819188]] where
 M := ![![![347151215, -209217192, 14754372, -31433803, 67819188]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI311N1 : IdealMulLeCertificate' Table 
  ![![347151215, -209217192, 14754372, -31433803, 67819188]] ![![490719, 121620, -673280, -148362, -475180]]
  ![![-23501951, 15022936, -2435252, 1912557, -5771716]] where
 M := ![![![-23501951, 15022936, -2435252, 1912557, -5771716]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI311N2 : IdealMulLeCertificate' Table 
  ![![-23501951, 15022936, -2435252, 1912557, -5771716]] ![![-2339, -579, 3208, 707, 2264]]
  ![![311, 0, 0, 0, 0]] where
 M := ![![![54242269773, 13417514985, -74378796076, -16392936888, -52489194184]]]
 hmul := by decide  
 g := ![![![![174412443, 43143135, -239160116, -52710408, -168775544]]]]
 hle2 := by decide  


def PBC311 : ContainsPrimesAboveP 311 ![I311N0, I311N1, I311N2, I311N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI311N0
    exact isPrimeI311N1
    exact isPrimeI311N2
    exact isPrimeI311N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 311 (by decide) (𝕀 ⊙ MulI311N0 ⊙ MulI311N1 ⊙ MulI311N2)
instance hp313 : Fact (Nat.Prime 313) := {out := by norm_num}

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1495, 1090, -3180, 2161, -822]] i)))

def SI313N0: IdealEqSpanCertificate' Table ![![1495, 1090, -3180, 2161, -822]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![0, 0, 313, 0, 0], ![256, 72, 141, 1, 0], ![156, 306, 17, 0, 1]] where
  M :=![![![1495, 1090, -3180, 2161, -822], ![3288, 4281, -2752, -9860, 11322], ![-22644, -20914, 38247, 1447, -18258], ![34872, 25366, -74312, 50859, -19578], ![23580, 23934, -34976, -18221, 34033]]]
  hmulB := by decide  
  f := ![![![19015, -10912, 756, -1681, 3528]], ![![-14112, 9353, -656, 1346, -3030]], ![![6060, -3008, 263, -487, 1008]], ![![15052, -8138, 587, -1286, 2646]], ![![-3972, 3530, -249, 450, -1145]]]
  g := ![![![-1353, 310, -939, 2161, -822], ![2432, -8787, 3818, -9860, 11322], ![7844, 17450, 462, 1447, -18258], ![-31728, 7522, -22085, 50859, -19578], ![-1984, -29004, 6248, -18221, 34033]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P0 : CertificateIrreducibleZModOfList' 313 3 2 8 [38, 79, 249, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 168, 256], [273, 144, 57], [0, 1]]
 g := ![![[162, 228, 277], [165, 142], [42, 70], [271, 147, 216], [158, 121, 137], [89, 147, 200], [64, 1], []], ![[66, 46, 216, 192], [157, 12], [102, 196], [98, 177, 180, 185], [1, 194, 231, 64], [227, 286, 0, 157], [7, 78], [45, 119]], ![[183, 183, 187, 26], [151, 33], [62, 143], [273, 233, 257, 75], [247, 116, 300, 169], [62, 244, 177, 295], [247, 54], [244, 119]]]
 h' := ![![[104, 168, 256], [71, 46, 150], [304, 69, 237], [31, 42, 208], [256, 100, 290], [61, 79, 78], [72, 227, 261], [0, 0, 1], [0, 1]], ![[273, 144, 57], [128, 78, 198], [268, 131, 147], [102, 204, 14], [286, 132, 65], [210, 217, 156], [262, 98, 231], [29, 262, 144], [104, 168, 256]], ![[0, 1], [210, 189, 278], [1, 113, 242], [127, 67, 91], [249, 81, 271], [71, 17, 79], [251, 301, 134], [153, 51, 168], [273, 144, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [164, 218], []]
 b := ![[], [226, 101, 207], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N0 : CertifiedPrimeIdeal' SI313N0 313 where
  n := 3
  hpos := by decide
  P := [38, 79, 249, 1]
  hirr := P313P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21795873, -27738357, 75554756, -102240889, 16439207]
  a := ![3, -61, 2, -69, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![75358963, 7358493, 45405922, -102240889, 16439207]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N0 : Ideal.IsPrime I313N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N0 B_one_repr
lemma NI313N0 : Nat.card (O ⧸ I313N0) = 30664297 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N0

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![551, -52, -672, -167, -426]] i)))

def SI313N1: IdealEqSpanCertificate' Table ![![551, -52, -672, -167, -426]] 
 ![![313, 0, 0, 0, 0], ![124, 1, 0, 0, 0], ![137, 0, 1, 0, 0], ![208, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![551, -52, -672, -167, -426], ![1704, 397, -2660, -584, -1854], ![3708, 792, -5165, -1149, -3606], ![6360, 1530, -8696, -1921, -6126], ![5636, 1390, -7628, -1683, -5387]]]
  hmulB := by decide  
  f := ![![![3815, 1502, -10992, 15427, -11004]], ![![1652, 741, -4556, 5978, -4134]], ![![1219, 268, -3989, 6572, -4992]], ![![2816, 1106, -8120, 11409, -8142]], ![![685, 594, -1244, 256, 283]]]
  g := ![![![437, -52, -672, -167, -426], ![1442, 397, -2660, -584, -1854], ![2803, 792, -5165, -1149, -3606], ![4634, 1530, -8696, -1921, -6126], ![4045, 1390, -7628, -1683, -5387]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N1 : Nat.card (O ⧸ I313N1) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N1)

lemma isPrimeI313N1 : Ideal.IsPrime I313N1 := prime_ideal_of_norm_prime hp313.out _ NI313N1

def I313N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-89, 56, -4, 8, -18]] i)))

def SI313N2: IdealEqSpanCertificate' Table ![![-89, 56, -4, 8, -18]] 
 ![![313, 0, 0, 0, 0], ![220, 1, 0, 0, 0], ![214, 0, 1, 0, 0], ![138, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![-89, 56, -4, 8, -18], ![72, -41, 4, -6, 12], ![-24, 20, -5, 4, -6], ![-24, 16, 0, -3, 0], ![-32, 14, 4, 2, -7]]]
  hmulB := by decide  
  f := ![![![-833, -180, 1180, 260, 822]], ![![-596, -129, 844, 186, 588]], ![![-590, -128, 835, 184, 582]], ![![-402, -88, 568, 125, 396]], ![![-97, -22, 136, 30, 95]]]
  g := ![![![-39, 56, -4, 8, -18], ![28, -41, 4, -6, 12], ![-12, 20, -5, 4, -6], ![-10, 16, 0, -3, 0], ![-13, 14, 4, 2, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N2 : Nat.card (O ⧸ I313N2) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N2)

lemma isPrimeI313N2 : Ideal.IsPrime I313N2 := prime_ideal_of_norm_prime hp313.out _ NI313N2
def MulI313N0 : IdealMulLeCertificate' Table 
  ![![1495, 1090, -3180, 2161, -822]] ![![551, -52, -672, -167, -426]]
  ![![833, 180, -1180, -260, -822]] where
 M := ![![![833, 180, -1180, -260, -822]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI313N1 : IdealMulLeCertificate' Table 
  ![![833, 180, -1180, -260, -822]] ![![-89, 56, -4, 8, -18]]
  ![![313, 0, 0, 0, 0]] where
 M := ![![![-313, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC313 : ContainsPrimesAboveP 313 ![I313N0, I313N1, I313N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI313N0
    exact isPrimeI313N1
    exact isPrimeI313N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 313 (by decide) (𝕀 ⊙ MulI313N0 ⊙ MulI313N1)
instance hp317 : Fact (Nat.Prime 317) := {out := by norm_num}

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18803, -4644, 25772, 5681, 18186]] i)))

def SI317N0: IdealEqSpanCertificate' Table ![![-18803, -4644, 25772, 5681, 18186]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![0, 0, 317, 0, 0], ![80, 87, 39, 1, 0], ![149, 239, 169, 0, 1]] where
  M :=![![![-18803, -4644, 25772, 5681, 18186], ![-72744, -18041, 99828, 21996, 70458], ![-140916, -34920, 193333, 42603, 136446], ![-236520, -58614, 324504, 71509, 229026], ![-207276, -51366, 284380, 62665, 200707]]]
  hmulB := by decide  
  f := ![![![185, 210, -28, 11, -84]], ![![336, 347, -84, 6, -102]], ![![204, 234, 41, -39, -84]], ![![164, 177, -25, 0, -60]], ![![449, 485, -55, -11, -161]]]
  g := ![![![-10041, -15285, -10313, 5681, 18186], ![-38898, -59215, -39954, 21996, 70458], ![-75330, -114675, -77374, 42603, 136446], ![-126442, -192483, -129873, 71509, 229026], ![-110807, -168682, -113814, 62665, 200707]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P0 : CertificateIrreducibleZModOfList' 317 3 2 8 [3, 69, 159, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 302, 272], [140, 14, 45], [0, 1]]
 g := ![![[311, 45, 85], [287, 90], [23, 71, 36], [65, 281, 278], [280, 251, 53], [226, 12, 31], [158, 1], []], ![[151, 124, 275, 288], [131, 223], [253, 168, 74, 177], [308, 206, 173, 304], [266, 156, 10, 203], [150, 46, 110, 115], [146, 196], [179, 123]], ![[96, 41, 95, 178], [189, 256], [164, 157, 313, 35], [242, 167, 142, 166], [315, 171, 69, 118], [44, 147, 148, 27], [81, 225], [89, 123]]]
 h' := ![![[18, 302, 272], [96, 255, 269], [248, 87, 93], [122, 19, 311], [111, 249, 230], [273, 143, 170], [160, 190, 169], [0, 0, 1], [0, 1]], ![[140, 14, 45], [11, 240, 216], [74, 230, 240], [157, 25, 12], [300, 126, 257], [239, 61, 66], [234, 253, 156], [104, 54, 14], [18, 302, 272]], ![[0, 1], [167, 139, 149], [10, 0, 301], [270, 273, 311], [132, 259, 147], [276, 113, 81], [90, 191, 309], [313, 263, 302], [140, 14, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57], []]
 b := ![[], [61, 276], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N0 : CertifiedPrimeIdeal' SI317N0 317 where
  n := 3
  hpos := by decide
  P := [3, 69, 159, 1]
  hirr := P317P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39148, 49096, -64041, -2875, 66168]
  a := ![1, -6, -1, -3, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30252, -48943, -35124, -2875, 66168]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N0 : Ideal.IsPrime I317N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N0 B_one_repr
lemma NI317N0 : Nat.card (O ⧸ I317N0) = 31855013 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N0

def I317N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 224, -250, -351, 474]] i)))

def SI317N1: IdealEqSpanCertificate' Table ![![197, 224, -250, -351, 474]] 
 ![![317, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![69, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![276, 0, 0, 0, 1]] where
  M :=![![![197, 224, -250, -351, 474], ![-1896, -1703, 3292, -272, -1158], ![2316, 1584, -5177, 4143, -1974], ![4896, 5538, -5984, -8197, 11034], ![-5092, -4178, 9788, -3743, -455]]]
  hmulB := by decide  
  f := ![![![-685439, 455170, -99250, 51559, -191568]], ![![-88398, 59365, -13904, 6484, -25614]], ![![-148731, 99792, -23243, 10932, -42972]], ![![-247321, 165992, -38734, 18166, -71526]], ![![-595792, 397168, -88812, 44435, -168605]]]
  g := ![![![-260, 224, -250, -351, 474], ![610, -1703, 3292, -272, -1158], ![1140, 1584, -5177, 4143, -1974], ![-6049, 5538, -5984, -8197, 11034], ![161, -4178, 9788, -3743, -455]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI317N1 : Nat.card (O ⧸ I317N1) = 317 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI317N1)

lemma isPrimeI317N1 : Ideal.IsPrime I317N1 := prime_ideal_of_norm_prime hp317.out _ NI317N1

def I317N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25813, -15566, 1098, -2338, 5046]] i)))

def SI317N2: IdealEqSpanCertificate' Table ![![25813, -15566, 1098, -2338, 5046]] 
 ![![317, 0, 0, 0, 0], ![197, 1, 0, 0, 0], ![91, 0, 1, 0, 0], ![131, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![25813, -15566, 1098, -2338, 5046], ![-20184, 12143, -856, 1826, -3936], ![7872, -4758, 335, -714, 1542], ![7008, -4224, 296, -635, 1368], ![8152, -4906, 344, -738, 1589]]]
  hmulB := by decide  
  f := ![![![-151, -22, 522, -938, 726]], ![![-103, -23, 338, -576, 438]], ![![-17, 16, 101, -256, 216]], ![![-73, -10, 254, -457, 354]], ![![-66, -38, 164, -182, 113]]]
  g := ![![![9419, -15566, 1098, -2338, 5046], ![-7349, 12143, -856, 1826, -3936], ![2879, -4758, 335, -714, 1542], ![2557, -4224, 296, -635, 1368], ![2970, -4906, 344, -738, 1589]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI317N2 : Nat.card (O ⧸ I317N2) = 317 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI317N2)

lemma isPrimeI317N2 : Ideal.IsPrime I317N2 := prime_ideal_of_norm_prime hp317.out _ NI317N2
def MulI317N0 : IdealMulLeCertificate' Table 
  ![![-18803, -4644, 25772, 5681, 18186]] ![![197, 224, -250, -351, 474]]
  ![![-151, -22, 522, -938, 726]] where
 M := ![![![-151, -22, 522, -938, 726]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI317N1 : IdealMulLeCertificate' Table 
  ![![-151, -22, 522, -938, 726]] ![![25813, -15566, 1098, -2338, 5046]]
  ![![317, 0, 0, 0, 0]] where
 M := ![![![317, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC317 : ContainsPrimesAboveP 317 ![I317N0, I317N1, I317N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI317N0
    exact isPrimeI317N1
    exact isPrimeI317N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 317 (by decide) (𝕀 ⊙ MulI317N0 ⊙ MulI317N1)
instance hp331 : Fact (Nat.Prime 331) := {out := by norm_num}

def I331N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3787, -2835, 8114, -4669, 1150]] i)))

def SI331N0: IdealEqSpanCertificate' Table ![![-3787, -2835, 8114, -4669, 1150]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![0, 0, 331, 0, 0], ![0, 0, 0, 331, 0], ![134, 22, 311, 82, 1]] where
  M :=![![![-3787, -2835, 8114, -4669, 1150], ![-4600, -7311, 1230, 24416, -25714], ![51428, 48445, -84453, -10329, 47534], ![-92768, -70720, 190432, -110099, 29404], ![-48992, -51360, 68898, 50438, -81925]]]
  hmulB := by decide  
  f := ![![![-8025, 4465, 276, 819, -1060]], ![![4240, -3991, 2570, -26, 2794]], ![![-5588, 585, 4391, 1199, 2716]], ![![-7552, -120, 7448, 1847, 4916]], ![![-10110, 2063, 6273, 1919, 3539]]]
  g := ![![![-477, -85, -1056, -299, 1150], ![10396, 1687, 24164, 6444, -25714], ![-19088, -3013, -44917, -11807, 47534], ![-12184, -2168, -27052, -7617, 29404], ![33018, 5290, 77183, 20448, -81925]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P0 : CertificateIrreducibleZModOfList' 331 4 2 8 [174, 129, 98, 324, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [309, 228, 11, 330], [271, 299, 312, 254], [89, 134, 8, 78], [0, 1]]
 g := ![![[61, 127, 313, 161], [52, 218, 162, 214], [149, 85, 290], [190, 116, 177, 143], [199, 43, 45], [83, 25, 84], [7, 1], []], ![[127, 226, 120, 129, 196, 75], [178, 308, 124, 275, 31, 108], [242, 324, 313], [19, 298, 155, 168, 110, 32], [217, 117, 197], [162, 1, 76], [329, 216, 286, 25, 49, 162], [124, 316, 1]], ![[102, 169, 132, 6, 53, 48], [134, 10, 168, 310, 239, 90], [32, 315, 33], [50, 19, 168, 197, 110, 137], [167, 206, 130], [154, 49, 230], [293, 328, 56, 8, 29, 86], [50, 75, 302]], ![[200, 200, 157, 97, 300, 248], [256, 120, 6, 65, 275, 147], [114, 283, 189], [70, 24, 107, 11, 100, 208], [304, 45, 281], [132, 234, 118], [205, 203, 93, 25, 6, 59], [29, 144, 126]]]
 h' := ![![[309, 228, 11, 330], [220, 134, 245, 278], [168, 17, 69, 187], [40, 144, 30, 271], [22, 170, 30, 229], [104, 235, 281, 294], [106, 247, 178, 282], [0, 0, 1], [0, 1]], ![[271, 299, 312, 254], [296, 232, 150, 16], [313, 165, 231, 47], [265, 110, 1, 225], [85, 58, 164, 300], [42, 265, 196, 39], [162, 120, 76, 260], [92, 83, 65, 318], [309, 228, 11, 330]], ![[89, 134, 8, 78], [151, 305, 291, 65], [12, 59, 63, 226], [280, 314, 208, 258], [140, 324, 166, 304], [231, 11, 94, 285], [116, 121, 165, 237], [196, 228, 64, 246], [271, 299, 312, 254]], ![[0, 1], [81, 322, 307, 303], [239, 90, 299, 202], [154, 94, 92, 239], [178, 110, 302, 160], [86, 151, 91, 44], [154, 174, 243, 214], [227, 20, 201, 98], [89, 134, 8, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [181, 245], []]
 b := ![[], [], [67, 136, 274], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N0 : CertifiedPrimeIdeal' SI331N0 331 where
  n := 4
  hpos := by decide
  P := [174, 129, 98, 324, 1]
  hirr := P331P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6241143490, -2401173791, 9121050228, 1158664031, 4014360470]
  a := ![1, 26, 4, 10, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1644004370, -274069801, -3744244882, -990993639, 4014360470]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N0 : Ideal.IsPrime I331N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N0 B_one_repr
lemma NI331N0 : Nat.card (O ⧸ I331N0) = 12003612721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N0

def I331N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8025, 4465, 276, 819, -1060]] i)))

def SI331N1: IdealEqSpanCertificate' Table ![![-8025, 4465, 276, 819, -1060]] 
 ![![331, 0, 0, 0, 0], ![168, 1, 0, 0, 0], ![121, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![136, 0, 0, 0, 1]] where
  M :=![![![-8025, 4465, 276, 819, -1060], ![4240, -3991, 2570, -26, 2794], ![-5588, 585, 4391, 1199, 2716], ![-7552, -120, 7448, 1847, 4916], ![-7208, 250, 6502, 1672, 4193]]]
  hmulB := by decide  
  f := ![![![-3787, -2835, 8114, -4669, 1150]], ![![-1936, -1461, 4122, -2296, 506]], ![![-1229, -890, 2711, -1738, 564]], ![![-429, -325, 894, -516, 134]], ![![-1704, -1320, 3542, -1766, 225]]]
  g := ![![![-1988, 4465, 276, 819, -1060], ![-48, -3991, 2570, -26, 2794], ![-3082, 585, 4391, 1199, 2716], ![-4777, -120, 7448, 1847, 4916], ![-4314, 250, 6502, 1672, 4193]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI331N1 : Nat.card (O ⧸ I331N1) = 331 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI331N1)

lemma isPrimeI331N1 : Ideal.IsPrime I331N1 := prime_ideal_of_norm_prime hp331.out _ NI331N1
def MulI331N0 : IdealMulLeCertificate' Table 
  ![![-3787, -2835, 8114, -4669, 1150]] ![![-8025, 4465, 276, 819, -1060]]
  ![![331, 0, 0, 0, 0]] where
 M := ![![![331, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC331 : ContainsPrimesAboveP 331 ![I331N0, I331N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI331N0
    exact isPrimeI331N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 331 (by decide) (𝕀 ⊙ MulI331N0)
instance hp337 : Fact (Nat.Prime 337) := {out := by norm_num}

def I337N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45, -5047, 8410, 1262, 6916]] i)))

def SI337N0: IdealEqSpanCertificate' Table ![![-45, -5047, 8410, 1262, 6916]] 
 ![![337, 0, 0, 0, 0], ![0, 337, 0, 0, 0], ![246, 255, 1, 0, 0], ![289, 308, 0, 1, 0], ![3, 201, 0, 0, 1]] where
  M :=![![![-45, -5047, 8410, 1262, 6916], ![-27664, -2943, 31402, 7380, 21404], ![-42808, -12155, 61269, 13320, 43544], ![-73256, -19522, 102776, 22487, 72802], ![-63732, -17378, 90086, 19665, 63887]]]
  hmulB := by decide  
  f := ![![![-5957, -5655, 9712, 1562, -5860]], ![![23440, 18599, -46470, 22160, -2348]], ![![13402, 9984, -28039, 17708, -5864]], ![![15899, 11755, -33464, 21699, -7578]], ![![14037, 11108, -27896, 13503, -1615]]]
  g := ![![![-7283, -11657, 8410, 1262, 6916], ![-29524, -43281, 31402, 7380, 21404], ![-56662, -84542, 61269, 13320, 43544], ![-95173, -141800, 102776, 22487, 72802], ![-83382, -124295, 90086, 19665, 63887]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P0 : CertificateIrreducibleZModOfList' 337 2 2 8 [262, 233, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 336], [0, 1]]
 g := ![![[262, 328], [336], [336], [329], [73, 56], [13], [56, 32], [1]], ![[0, 9], [336], [336], [329], [168, 281], [13], [14, 305], [1]]]
 h' := ![![[104, 336], [7, 230], [115, 189], [223, 148], [83, 282], [36, 215], [156, 32], [75, 104], [0, 1]], ![[0, 1], [0, 107], [225, 148], [113, 189], [92, 55], [154, 122], [114, 305], [107, 233], [104, 336]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [203]]
 b := ![[], [114, 270]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N0 : CertifiedPrimeIdeal' SI337N0 337 where
  n := 2
  hpos := by decide
  P := [262, 233, 1]
  hirr := P337P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8322, -8523, 12282, 5626, -12004]
  a := ![-1, -6, -4, 13, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13708, -7301, 12282, 5626, -12004]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI337N0 : Ideal.IsPrime I337N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N0 B_one_repr
lemma NI337N0 : Nat.card (O ⧸ I337N0) = 113569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N0

def I337N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1029, -463, 80, 17, 182]] i)))

def SI337N1: IdealEqSpanCertificate' Table ![![-1029, -463, 80, 17, 182]] 
 ![![337, 0, 0, 0, 0], ![0, 337, 0, 0, 0], ![318, 143, 1, 0, 0], ![21, 99, 0, 1, 0], ![297, 92, 0, 0, 1]] where
  M :=![![![-1029, -463, 80, 17, 182], ![-728, -1279, 166, -56, 466], ![-932, -803, 119, -11, 298], ![-232, -76, 8, 9, 32], ![144, 356, -46, 16, -125]]]
  hmulB := by decide  
  f := ![![![-3973, -985, 5450, 1203, 3844]], ![![-15376, -3805, 21094, 4650, 14906]], ![![-10362, -2566, 14215, 3135, 10038]], ![![-4913, -1216, 6740, 1486, 4762]], ![![-7829, -1939, 10740, 2369, 7583]]]
  g := ![![![-240, -90, 80, 17, 182], ![-566, -185, 166, -56, 466], ![-377, -131, 119, -11, 298], ![-37, -15, 8, 9, 32], ![153, 50, -46, 16, -125]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P1 : CertificateIrreducibleZModOfList' 337 2 2 8 [30, 242, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [95, 336], [0, 1]]
 g := ![![[53, 323], [200], [311], [281], [29, 227], [328], [76, 263], [1]], ![[71, 14], [200], [311], [281], [26, 110], [328], [123, 74], [1]]]
 h' := ![![[95, 336], [164, 71], [155, 77], [330, 131], [141, 195], [108, 100], [79, 230], [307, 95], [0, 1]], ![[0, 1], [169, 266], [56, 260], [306, 206], [131, 142], [172, 237], [24, 107], [233, 242], [95, 336]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [205]]
 b := ![[], [102, 271]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N1 : CertifiedPrimeIdeal' SI337N1 337 where
  n := 2
  hpos := by decide
  P := [30, 242, 1]
  hirr := P337P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6274, -8024, 7528, 8384, -12312]
  a := ![0, -2, 4, -26, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3206, -2320, 7528, 8384, -12312]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI337N1 : Ideal.IsPrime I337N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N1 B_one_repr
lemma NI337N1 : Nat.card (O ⧸ I337N1) = 113569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N1

def I337N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1143, -984, 2092, -483, -422]] i)))

def SI337N2: IdealEqSpanCertificate' Table ![![-1143, -984, 2092, -483, -422]] 
 ![![337, 0, 0, 0, 0], ![215, 1, 0, 0, 0], ![309, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![152, 0, 0, 0, 1]] where
  M :=![![![-1143, -984, 2092, -483, -422], ![1688, 827, -4500, 5572, -3742], ![7484, 7908, -10399, -8201, 12974], ![-26792, -23046, 49080, -11471, -9758], ![-2988, -4814, 420, 16129, -16729]]]
  hmulB := by decide  
  f := ![![![-3414479, 2088902, -148652, 311371, -678028]], ![![-2170329, 1327981, -94512, 197931, -431050]], ![![-3133823, 1917292, -136443, 285784, -622328]], ![![-387770, 237222, -16880, 35361, -76998]], ![![-1543300, 944088, -67180, 140731, -306435]]]
  g := ![![![-1049, -984, 2092, -483, -422], ![4663, 827, -4500, 5572, -3742], ![-415, 7908, -10399, -8201, 12974], ![-24684, -23046, 49080, -11471, -9758], ![8404, -4814, 420, 16129, -16729]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI337N2 : Nat.card (O ⧸ I337N2) = 337 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI337N2)

lemma isPrimeI337N2 : Ideal.IsPrime I337N2 := prime_ideal_of_norm_prime hp337.out _ NI337N2
def MulI337N0 : IdealMulLeCertificate' Table 
  ![![-45, -5047, 8410, 1262, 6916]] ![![-1029, -463, 80, 17, 182]]
  ![![-3414479, 2088902, -148652, 311371, -678028]] where
 M := ![![![-3414479, 2088902, -148652, 311371, -678028]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI337N1 : IdealMulLeCertificate' Table 
  ![![-3414479, 2088902, -148652, 311371, -678028]] ![![-1143, -984, 2092, -483, -422]]
  ![![337, 0, 0, 0, 0]] where
 M := ![![![337, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC337 : ContainsPrimesAboveP 337 ![I337N0, I337N1, I337N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI337N0
    exact isPrimeI337N1
    exact isPrimeI337N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 337 (by decide) (𝕀 ⊙ MulI337N0 ⊙ MulI337N1)
instance hp347 : Fact (Nat.Prime 347) := {out := by norm_num}

def I347N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 26, 8, 4, -18]] i)))

def SI347N0: IdealEqSpanCertificate' Table ![![-13, 26, 8, 4, -18]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![0, 0, 347, 0, 0], ![172, 224, 156, 1, 0], ![251, 164, 227, 0, 1]] where
  M :=![![![-13, 26, 8, 4, -18], ![72, 39, -56, 26, -12], ![24, 46, 3, -76, 66], ![-168, -148, 272, 33, -156], ![24, 18, -96, 108, -67]]]
  hmulB := by decide  
  f := ![![![25, 14, -40, -8, -30]], ![![120, 29, -152, -34, -108]], ![![216, 58, -295, -64, -210]], ![![188, 52, -252, -55, -180]], ![![217, 62, -295, -64, -211]]]
  g := ![![![11, 6, 10, 4, -18], ![-4, -11, -4, 26, -12], ![-10, 18, -9, -76, 66], ![96, 52, 88, 33, -156], ![-5, -38, -5, 108, -67]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P0 : CertificateIrreducibleZModOfList' 347 3 2 8 [55, 36, 218, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 93, 140], [25, 253, 207], [0, 1]]
 g := ![![[200, 131, 212], [178, 224, 27], [120, 16], [142, 174, 107], [164, 263, 105], [173, 87], [296, 129, 1], []], ![[193, 146, 290, 109], [250, 137, 54, 267], [276, 114], [237, 2, 22, 224], [175, 292, 110, 256], [333, 67], [164, 333, 144, 332], [173, 168]], ![[320, 141, 267, 170], [61, 87, 333, 47], [315, 133], [123, 81, 206, 218], [143, 202, 316, 223], [303, 33], [289, 24, 275, 170], [106, 168]]]
 h' := ![![[104, 93, 140], [273, 119, 307], [86, 178, 62], [171, 243, 343], [2, 105, 178], [1, 82, 211], [29, 293, 173], [0, 0, 1], [0, 1]], ![[25, 253, 207], [167, 32, 294], [18, 86, 7], [113, 155, 43], [294, 141, 50], [235, 296, 321], [182, 327, 121], [260, 59, 253], [104, 93, 140]], ![[0, 1], [125, 196, 93], [25, 83, 278], [0, 296, 308], [198, 101, 119], [316, 316, 162], [67, 74, 53], [0, 288, 93], [25, 253, 207]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 320], []]
 b := ![[], [105, 91, 196], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N0 : CertifiedPrimeIdeal' SI347N0 347 where
  n := 3
  hpos := by decide
  P := [55, 36, 218, 1]
  hirr := P347P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2173450, -1871261, 3996685, -848243, -756927]
  a := ![13, -6, -3, 8, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![961709, 899917, 888026, -848243, -756927]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N0 : Ideal.IsPrime I347N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N0 B_one_repr
lemma NI347N0 : Nat.card (O ⧸ I347N0) = 41781923 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N0

def I347N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 14, -40, -8, -30]] i)))

def SI347N1: IdealEqSpanCertificate' Table ![![25, 14, -40, -8, -30]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![339, 191, 1, 0, 0], ![140, 124, 0, 1, 0], ![146, 267, 0, 0, 1]] where
  M :=![![![25, 14, -40, -8, -30], ![120, 29, -152, -34, -108], ![216, 58, -295, -64, -210], ![360, 92, -496, -109, -348], ![312, 78, -432, -96, -305]]]
  hmulB := by decide  
  f := ![![![-13, 26, 8, 4, -18]], ![![72, 39, -56, 26, -12]], ![![27, 47, -23, 18, -24]], ![![20, 24, -16, 11, -12]], ![![50, 41, -40, 22, -17]]]
  g := ![![![55, 48, -40, -8, -30], ![208, 179, -152, -34, -108], ![403, 347, -295, -64, -210], ![676, 580, -496, -109, -348], ![590, 507, -432, -96, -305]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P1 : CertificateIrreducibleZModOfList' 347 2 2 8 [112, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [346, 346], [0, 1]]
 g := ![![[189, 300], [333, 341], [225], [126, 120], [9, 172], [279], [223, 1], [1]], ![[236, 47], [339, 6], [225], [6, 227], [184, 175], [279], [222, 346], [1]]]
 h' := ![![[346, 346], [180, 91], [170, 102], [115, 15], [33, 193], [46, 51], [8, 64], [235, 346], [0, 1]], ![[0, 1], [89, 256], [68, 245], [100, 332], [187, 154], [342, 296], [291, 283], [236, 1], [346, 346]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [236]]
 b := ![[], [59, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N1 : CertifiedPrimeIdeal' SI347N1 347 where
  n := 2
  hpos := by decide
  P := [112, 1, 1]
  hirr := P347P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1352, -1467, 2128, 1275, -2142]
  a := ![-1, 0, 2, -8, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1696, 17, 2128, 1275, -2142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N1 : Ideal.IsPrime I347N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N1 B_one_repr
lemma NI347N1 : Nat.card (O ⧸ I347N1) = 120409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N1
def MulI347N0 : IdealMulLeCertificate' Table 
  ![![-13, 26, 8, 4, -18]] ![![25, 14, -40, -8, -30]]
  ![![347, 0, 0, 0, 0]] where
 M := ![![![347, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC347 : ContainsPrimesAboveP 347 ![I347N0, I347N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI347N0
    exact isPrimeI347N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 347 (by decide) (𝕀 ⊙ MulI347N0)
instance hp349 : Fact (Nat.Prime 349) := {out := by norm_num}

def I349N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32775, -8415, 44534, 9792, 31534]] i)))

def SI349N0: IdealEqSpanCertificate' Table ![![-32775, -8415, 44534, 9792, 31534]] 
 ![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![0, 0, 349, 0, 0], ![147, 47, 97, 1, 0], ![182, 282, 169, 0, 1]] where
  M :=![![![-32775, -8415, 44534, 9792, 31534], ![-126136, -31725, 172374, 37950, 121820], ![-243640, -60751, 333735, 73514, 235670], ![-408272, -101246, 560072, 123411, 395302], ![-357580, -88504, 490786, 108157, 346339]]]
  hmulB := by decide  
  f := ![![![-971, 593, -40, 64, -166]], ![![664, -551, 190, -42, 52]], ![![-104, 333, -395, 206, -74]], ![![-349, 269, -101, 77, -82]], ![![-22, 25, -57, 99, -81]]]
  g := ![![![-20663, -26823, -17864, 9792, 31534], ![-79874, -103635, -69044, 37950, 121820], ![-154562, -200501, -133597, 73514, 235670], ![-259297, -336323, -224117, 123411, 395302], ![-227193, -294669, -196366, 108157, 346339]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P0 : CertificateIrreducibleZModOfList' 349 3 2 8 [28, 252, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 204, 291], [175, 144, 58], [0, 1]]
 g := ![![[346, 39, 42], [129, 116], [241, 238, 210], [314, 24, 289], [111, 10, 326], [69, 180], [170, 259, 1], []], ![[93, 330, 109, 187], [58, 124], [69, 180, 293, 63], [269, 290, 102, 236], [306, 51, 64, 59], [175, 93], [258, 50, 74, 315], [240, 223]], ![[124, 318, 137, 156], [107, 335], [219, 81, 118, 90], [150, 283, 168, 244], [265, 58, 142, 156], [305, 206], [315, 282, 244, 44], [124, 223]]]
 h' := ![![[84, 204, 291], [305, 307, 316], [232, 262, 198], [282, 163, 48], [33, 273, 17], [333, 54, 317], [126, 164, 23], [0, 0, 1], [0, 1]], ![[175, 144, 58], [347, 341, 127], [122, 343, 54], [88, 337, 250], [59, 286, 225], [50, 37, 287], [341, 67, 82], [336, 5, 144], [84, 204, 291]], ![[0, 1], [118, 50, 255], [312, 93, 97], [18, 198, 51], [218, 139, 107], [125, 258, 94], [17, 118, 244], [280, 344, 204], [175, 144, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 67], []]
 b := ![[], [173, 3, 296], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N0 : CertifiedPrimeIdeal' SI349N0 349 where
  n := 3
  hpos := by decide
  P := [28, 252, 90, 1]
  hirr := P349P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4532561, 4355271, -9879141, 6191598, 657861]
  a := ![3, 10, 7, -15, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2938003, -1352913, -2067744, 6191598, 657861]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI349N0 : Ideal.IsPrime I349N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N0 B_one_repr
lemma NI349N0 : Nat.card (O ⧸ I349N0) = 42508549 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N0

def I349N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63105, -38031, 2682, -5714, 12328]] i)))

def SI349N1: IdealEqSpanCertificate' Table ![![63105, -38031, 2682, -5714, 12328]] 
 ![![349, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![170, 0, 1, 0, 0], ![267, 0, 0, 1, 0], ![129, 0, 0, 0, 1]] where
  M :=![![![63105, -38031, 2682, -5714, 12328], ![-49312, 29703, -2094, 4464, -9628], ![19256, -11611, 819, -1744, 3764], ![17128, -10322, 728, -1551, 3346], ![19916, -11998, 846, -1803, 3889]]]
  hmulB := by decide  
  f := ![![![973, 221, -1316, -390, -928]], ![![19, 4, -26, -6, -20]], ![![498, 115, -675, -196, -472]], ![![779, 177, -1052, -315, -742]], ![![389, 87, -526, -153, -377]]]
  g := ![![![-984, -38031, 2682, -5714, 12328], ![767, 29703, -2094, 4464, -9628], ![-301, -11611, 819, -1744, 3764], ![-267, -10322, 728, -1551, 3346], ![-310, -11998, 846, -1803, 3889]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI349N1 : Nat.card (O ⧸ I349N1) = 349 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI349N1)

lemma isPrimeI349N1 : Ideal.IsPrime I349N1 := prime_ideal_of_norm_prime hp349.out _ NI349N1

def I349N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -38, -14, 160, -158]] i)))

def SI349N2: IdealEqSpanCertificate' Table ![![-19, -38, -14, 160, -158]] 
 ![![349, 0, 0, 0, 0], ![152, 1, 0, 0, 0], ![314, 0, 1, 0, 0], ![141, 0, 0, 1, 0], ![147, 0, 0, 0, 1]] where
  M :=![![![-19, -38, -14, 160, -158], ![632, 603, -1024, -190, 644], ![-1288, -1030, 2535, -1156, 74], ![-464, -908, -296, 3749, -3716], ![2112, 1858, -3776, 584, 1057]]]
  hmulB := by decide  
  f := ![![![-10671, 13050, -1854, 1300, -4846]], ![![-4592, 5683, -816, 562, -2116]], ![![-9590, 11766, -1685, 1168, -4378]], ![![-4303, 5286, -774, 521, -1978]], ![![-4497, 5504, -802, 544, -2057]]]
  g := ![![![31, -38, -14, 160, -158], ![466, 603, -1024, -190, 644], ![-1400, -1030, 2535, -1156, 74], ![711, -908, -296, 3749, -3716], ![1913, 1858, -3776, 584, 1057]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI349N2 : Nat.card (O ⧸ I349N2) = 349 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI349N2)

lemma isPrimeI349N2 : Ideal.IsPrime I349N2 := prime_ideal_of_norm_prime hp349.out _ NI349N2
def MulI349N0 : IdealMulLeCertificate' Table 
  ![![-32775, -8415, 44534, 9792, 31534]] ![![63105, -38031, 2682, -5714, 12328]]
  ![![-10671, 13050, -1854, 1300, -4846]] where
 M := ![![![-10671, 13050, -1854, 1300, -4846]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI349N1 : IdealMulLeCertificate' Table 
  ![![-10671, 13050, -1854, 1300, -4846]] ![![-19, -38, -14, 160, -158]]
  ![![349, 0, 0, 0, 0]] where
 M := ![![![349, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC349 : ContainsPrimesAboveP 349 ![I349N0, I349N1, I349N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI349N0
    exact isPrimeI349N1
    exact isPrimeI349N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 349 (by decide) (𝕀 ⊙ MulI349N0 ⊙ MulI349N1)
instance hp353 : Fact (Nat.Prime 353) := {out := by norm_num}

def I353N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![353, 0, 0, 0, 0]] i)))

def SI353N0: IdealEqSpanCertificate' Table ![![353, 0, 0, 0, 0]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![0, 0, 353, 0, 0], ![0, 0, 0, 353, 0], ![0, 0, 0, 0, 353]] where
  M :=![![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![0, 0, 353, 0, 0], ![0, 0, 0, 353, 0], ![0, 0, 0, 0, 353]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P0 : CertificateIrreducibleZModOfList' 353 5 2 8 [182, 84, 70, 161, 225, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [201, 156, 208, 48, 117], [3, 171, 120, 92, 15], [131, 121, 20, 313, 186], [146, 257, 5, 253, 35], [0, 1]]
 g := ![![[156, 50, 266, 117, 306], [301, 148, 219, 98], [215, 310, 67, 146], [127, 119, 265, 84], [295, 194, 285, 334], [128, 19, 100, 64, 146], [1], []], ![[104, 331, 219, 352, 20, 137, 274, 48], [211, 344, 127, 319], [325, 312, 245, 91], [93, 70, 172, 36], [134, 319, 144, 293], [293, 302, 332, 245, 169, 166, 208, 161], [309, 142, 202, 214, 59, 176, 258, 243], [84, 182, 189, 275]], ![[169, 279, 44, 302, 98, 55, 126, 189], [218, 84, 104, 295], [284, 307, 306, 304], [265, 53, 307, 64], [119, 278, 208, 177], [15, 90, 173, 64, 345, 85, 61, 176], [292, 23, 341, 62, 29, 285, 270, 309], [162, 144, 143, 225]], ![[247, 4, 126, 262, 283, 216, 48, 136], [191, 8, 202, 186], [293, 55, 170, 232], [187, 166, 296, 176], [223, 224, 65, 39], [85, 320, 246, 38, 2, 236, 215, 318], [198, 102, 133, 166, 214, 319, 256, 39], [71, 333, 202, 2]], ![[131, 323, 352, 150, 20, 173, 270, 306], [229, 27, 312, 58], [273, 11, 255, 255], [91, 50, 125, 213], [0, 183, 58, 172], [58, 115, 66, 258, 215, 253, 60, 29], [106, 228, 191, 77, 303, 219, 54, 351], [259, 8, 128, 166]]]
 h' := ![![[201, 156, 208, 48, 117], [11, 330, 294, 68, 219], [325, 108, 242, 48, 243], [25, 108, 103, 232, 128], [323, 36, 25, 268, 43], [2, 205, 55, 81, 263], [171, 269, 283, 192, 128], [0, 0, 1], [0, 1]], ![[3, 171, 120, 92, 15], [158, 20, 173, 145, 77], [275, 28, 266, 273, 111], [342, 156, 51, 80, 306], [18, 183, 128, 101, 6], [7, 249, 213, 63, 247], [70, 227, 257, 165, 239], [50, 293, 142, 121, 268], [201, 156, 208, 48, 117]], ![[131, 121, 20, 313, 186], [260, 159, 2, 167, 171], [333, 65, 107, 203, 182], [302, 294, 306, 319, 59], [44, 45, 247, 206, 345], [340, 261, 289, 22, 260], [248, 130, 49, 282, 258], [177, 40, 267, 123, 123], [3, 171, 120, 92, 15]], ![[146, 257, 5, 253, 35], [50, 241, 2, 190, 106], [194, 285, 79, 188, 48], [131, 175, 57, 48, 244], [180, 231, 161, 192, 23], [44, 57, 298, 341, 220], [90, 100, 56, 338, 236], [3, 79, 301, 179, 34], [131, 121, 20, 313, 186]], ![[0, 1], [97, 309, 235, 136, 133], [342, 220, 12, 347, 122], [31, 326, 189, 27, 322], [186, 211, 145, 292, 289], [305, 287, 204, 199, 69], [51, 333, 61, 82, 198], [300, 294, 348, 283, 281], [146, 257, 5, 253, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [222, 111, 218, 144], [], [], []]
 b := ![[], [296, 14, 124, 233, 216], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N0 : CertifiedPrimeIdeal' SI353N0 353 where
  n := 5
  hpos := by decide
  P := [182, 84, 70, 161, 225, 1]
  hirr := P353P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22538433309, -18972113139, 39659617070, -5230419709, -9407546369]
  a := ![1, 4, 2, -6, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-63848253, -53745363, 112350190, -14817053, -26650273]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N0 : Ideal.IsPrime I353N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N0 B_one_repr
lemma NI353N0 : Nat.card (O ⧸ I353N0) = 5481173216993 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N0

def PBC353 : ContainsPrimesAboveP 353 ![I353N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI353N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![353, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 353 (by decide) 𝕀

instance hp359 : Fact (Nat.Prime 359) := {out := by norm_num}

def I359N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18297, -4536, 25102, 5532, 17716]] i)))

def SI359N0: IdealEqSpanCertificate' Table ![![-18297, -4536, 25102, 5532, 17716]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![0, 0, 359, 0, 0], ![270, 232, 142, 1, 0], ![234, 294, 344, 0, 1]] where
  M :=![![![-18297, -4536, 25102, 5532, 17716], ![-70864, -17563, 97224, 21424, 68624], ![-137248, -34020, 188309, 41488, 132896], ![-230360, -57096, 316056, 69661, 223048], ![-201864, -50024, 276960, 61036, 195485]]]
  hmulB := by decide  
  f := ![![![-2911, 1696, -118, 260, -548]], ![![2192, -1413, 104, -208, 464]], ![![-928, 476, -21, 80, -160]], ![![-1142, 552, -30, 93, -176]], ![![-994, 406, -12, 76, -131]]]
  g := ![![![-15759, -18096, -19094, 5532, 17716], ![-61040, -70093, -73960, 21424, 68624], ![-118208, -135740, -143229, 41488, 132896], ![-198418, -227840, -240402, 69661, 223048], ![-173886, -199674, -210688, 61036, 195485]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P0 : CertificateIrreducibleZModOfList' 359 3 2 8 [247, 4, 149, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [147, 49, 195], [63, 309, 164], [0, 1]]
 g := ![![[293, 48, 136], [54, 306, 302], [16, 346, 162], [11, 298], [150, 169], [162, 167, 46], [298, 210, 1], []], ![[219, 200, 30, 156], [243, 118, 141, 252], [340, 301, 195, 310], [176, 99], [3, 164], [139, 209, 265, 267], [123, 343, 31, 337], [96, 330]], ![[201, 9, 139, 245], [4, 14, 337, 292], [38, 333, 209, 144], [103, 54], [307, 11], [287, 52, 348, 12], [283, 24, 4, 300], [127, 330]]]
 h' := ![![[147, 49, 195], [304, 319, 141], [356, 60, 210], [347, 321, 188], [227, 140, 124], [194, 227, 346], [348, 70, 104], [0, 0, 1], [0, 1]], ![[63, 309, 164], [179, 40, 228], [141, 190, 123], [41, 326, 63], [206, 176, 278], [231, 301, 40], [146, 256, 193], [51, 4, 309], [147, 49, 195]], ![[0, 1], [96, 0, 349], [239, 109, 26], [198, 71, 108], [48, 43, 316], [207, 190, 332], [233, 33, 62], [243, 355, 49], [63, 309, 164]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 160], []]
 b := ![[], [61, 235, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N0 : CertifiedPrimeIdeal' SI359N0 359 where
  n := 3
  hpos := by decide
  P := [247, 4, 149, 1]
  hirr := P359P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-85177, -80696, 142312, 22168, -79076]
  a := ![4, -1, -1, 3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![34633, 50208, 67400, 22168, -79076]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N0 : Ideal.IsPrime I359N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N0 B_one_repr
lemma NI359N0 : Nat.card (O ⧸ I359N0) = 46268279 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N0

def I359N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2911, 1696, -118, 260, -548]] i)))

def SI359N1: IdealEqSpanCertificate' Table ![![-2911, 1696, -118, 260, -548]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![16, 217, 1, 0, 0], ![118, 128, 0, 1, 0], ![314, 138, 0, 0, 1]] where
  M :=![![![-2911, 1696, -118, 260, -548], ![2192, -1413, 104, -208, 464], ![-928, 476, -21, 80, -160], ![-776, 472, -56, 83, -152], ![-888, 568, -48, 76, -173]]]
  hmulB := by decide  
  f := ![![![-18297, -4536, 25102, 5532, 17716]], ![![-70864, -17563, 97224, 21424, 68624]], ![![-44032, -10913, 60411, 13312, 42640]], ![![-31922, -7912, 43796, 9651, 30912]], ![![-43806, -10858, 60100, 13244, 42419]]]
  g := ![![![391, 194, -118, 260, -548], ![-336, -171, 104, -208, 464], ![112, 47, -21, 80, -160], ![106, 64, -56, 83, -152], ![126, 70, -48, 76, -173]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P1 : CertificateIrreducibleZModOfList' 359 2 2 8 [288, 272, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 358], [0, 1]]
 g := ![![[340, 91], [329, 301], [277, 270], [51], [23], [25, 188], [245, 30], [1]], ![[0, 268], [309, 58], [73, 89], [51], [23], [226, 171], [342, 329], [1]]]
 h' := ![![[87, 358], [24, 74], [281, 244], [312, 98], [238, 236], [339, 89], [163, 125], [71, 87], [0, 1]], ![[0, 1], [0, 285], [328, 115], [222, 261], [307, 123], [184, 270], [268, 234], [101, 272], [87, 358]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [22, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N1 : CertifiedPrimeIdeal' SI359N1 359 where
  n := 2
  hpos := by decide
  P := [288, 272, 1]
  hirr := P359P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-187087, -126949, 303334, -11567, 305]
  a := ![7, -46, -24, 25, -119]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10505, -179699, 303334, -11567, 305]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N1 : Ideal.IsPrime I359N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N1 B_one_repr
lemma NI359N1 : Nat.card (O ⧸ I359N1) = 128881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N1
def MulI359N0 : IdealMulLeCertificate' Table 
  ![![-18297, -4536, 25102, 5532, 17716]] ![![-2911, 1696, -118, 260, -548]]
  ![![359, 0, 0, 0, 0]] where
 M := ![![![359, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC359 : ContainsPrimesAboveP 359 ![I359N0, I359N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI359N0
    exact isPrimeI359N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 359 (by decide) (𝕀 ⊙ MulI359N0)


lemma PB1321I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313, 317, 331, 337, 347, 349, 353, 359] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 359 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 359 (by omega)

def PB1321I7 : PrimesBelowBoundCertificateInterval O 307 359 1321 where
  m := 9
  g := ![4, 3, 3, 2, 3, 2, 3, 1, 2]
  P := ![311, 313, 317, 331, 337, 347, 349, 353, 359]
  hP := PB1321I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1, I311N2, I311N3]
    · exact ![I313N0, I313N1, I313N2]
    · exact ![I317N0, I317N1, I317N2]
    · exact ![I331N0, I331N1]
    · exact ![I337N0, I337N1, I337N2]
    · exact ![I347N0, I347N1]
    · exact ![I349N0, I349N1, I349N2]
    · exact ![I353N0]
    · exact ![I359N0, I359N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC311
    · exact PBC313
    · exact PBC317
    · exact PBC331
    · exact PBC337
    · exact PBC347
    · exact PBC349
    · exact PBC353
    · exact PBC359
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![96721, 311, 311, 311]
    · exact ![30664297, 313, 313]
    · exact ![31855013, 317, 317]
    · exact ![12003612721, 331]
    · exact ![113569, 113569, 337]
    · exact ![41781923, 120409]
    · exact ![42508549, 349, 349]
    · exact ![5481173216993]
    · exact ![46268279, 128881]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI311N0
      exact NI311N1
      exact NI311N2
      exact NI311N3
    · dsimp ; intro j
      fin_cases j
      exact NI313N0
      exact NI313N1
      exact NI313N2
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
      exact NI317N1
      exact NI317N2
    · dsimp ; intro j
      fin_cases j
      exact NI331N0
      exact NI331N1
    · dsimp ; intro j
      fin_cases j
      exact NI337N0
      exact NI337N1
      exact NI337N2
    · dsimp ; intro j
      fin_cases j
      exact NI347N0
      exact NI347N1
    · dsimp ; intro j
      fin_cases j
      exact NI349N0
      exact NI349N1
      exact NI349N2
    · dsimp ; intro j
      fin_cases j
      exact NI353N0
    · dsimp ; intro j
      fin_cases j
      exact NI359N0
      exact NI359N1
  β := ![I311N1, I311N2, I311N3, I313N1, I313N2, I317N1, I317N2, I331N1, I337N2, I349N1, I349N2]
  Il := ![[I311N1, I311N2, I311N3], [I313N1, I313N2], [I317N1, I317N2], [I331N1], [I337N2], [], [I349N1, I349N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
