
import IdealArithmetic.Examples.NF5_3_729000000_1.RI5_3_729000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1173461, 364379, 76055, 96936, -209084]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![1173461, 364379, 76055, 96936, -209084]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![39, 5, 1, 0, 0], ![14, 22, 0, 1, 0], ![24, 35, 0, 0, 1]] where
  M :=![![![1173461, 364379, 76055, 96936, -209084], ![-2090840, -649252, -135513, -172722, 372532], ![3725320, 1156725, 241446, 307720, -663800], ![381620, 118473, 24733, 31515, -68014], ![2161380, 671091, 140083, 178526, -385145]]]
  hmulB := by decide  
  f := ![![![-3393, -1575, -223, -482, 788]], ![![7880, 3678, 659, 1404, -2104]], ![![-1701, -800, -120, -224, 396]], ![![1914, 899, 173, 353, -530]], ![![2724, 1273, 250, 536, -773]]]
  g := ![![![27884, 77156, 76055, 96936, -209084], ![-49679, -137469, -135513, -172722, 372532], ![88538, 244965, 241446, 307720, -663800], ![9077, 25104, 24733, 31515, -68014], ![51377, 142137, 140083, 178526, -385145]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [18, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 66], [0, 1]]
 g := ![![[65, 4], [56, 35], [33], [1], [23], [1]], ![[8, 63], [43, 32], [33], [1], [23], [1]]]
 h' := ![![[36, 66], [64, 2], [31, 13], [42, 57], [44, 1], [49, 36], [0, 1]], ![[0, 1], [2, 65], [30, 54], [17, 10], [13, 66], [5, 31], [36, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [2, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [18, 31, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25698, 28381, -1611, 3391, 15627]
  a := ![0, -9, 16, 2, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4985, -8733, -1611, 3391, 15627]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4353, -1350, -282, -359, 775]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-4353, -1350, -282, -359, 775]] 
 ![![67, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![65, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![-4353, -1350, -282, -359, 775], ![7750, 2403, 502, 639, -1379], ![-13790, -4270, -893, -1135, 2455], ![-1420, -440, -92, -117, 254], ![-8000, -2476, -518, -658, 1425]]]
  hmulB := by decide  
  f := ![![![181, 118, 32, -47, -31]], ![![44, 31, 12, -9, -13]], ![![-17, -16, -11, 4, 12]], ![![195, 122, 24, -58, -19]], ![![172, 112, 30, -44, -29]]]
  g := ![![![-48, -1350, -282, -359, 775], ![85, 2403, 502, 639, -1379], ![-156, -4270, -893, -1135, 2455], ![-17, -440, -92, -117, 254], ![-92, -2476, -518, -658, 1425]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26623, 12323, 2039, 3615, -6363]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![26623, 12323, 2039, 3615, -6363]] 
 ![![67, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![61, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![26623, 12323, 2039, 3615, -6363], ![-63630, -29560, -4885, -8677, 15327], ![153270, 71865, 11798, 21135, -36735], ![-4920, -2289, -385, -671, 1344], ![88660, 41689, 6827, 12268, -21145]]]
  hmulB := by decide  
  f := ![![![-51491, -36511, -13289, 14261, 13023]], ![![-40325, -29381, -11898, 10288, 12162]], ![![-29091, -19296, -4987, 9546, 4038]], ![![-54893, -36910, -10356, 17454, 8865]], ![![-38483, -27242, -9846, 10709, 9620]]]
  g := ![![![-9901, 12323, 2039, 3615, -6363], ![23705, -29560, -4885, -8677, 15327], ![-58023, 71865, 11798, 21135, -36735], ![1721, -2289, -385, -671, 1344], ![-33781, 41689, 6827, 12268, -21145]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2

def I67N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 17, 29, 16, -38]] i)))

def SI67N3: IdealEqSpanCertificate' Table ![![3, 17, 29, 16, -38]] 
 ![![67, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![3, 17, 29, 16, -38], ![-380, -254, -69, 122, 58], ![580, 35, -562, -580, 790], ![980, 715, 291, -249, -298], ![20, -3, -27, -24, 37]]]
  hmulB := by decide  
  f := ![![![-13271, -4045, -853, -1070, 2306]], ![![-10748, -3280, -691, -868, 1866]], ![![-3189, -980, -205, -260, 544]], ![![-11960, -3653, -769, -967, 2074]], ![![-8087, -2476, -520, -656, 1395]]]
  g := ![![![-12, 17, 29, 16, -38], ![77, -254, -69, 122, 58], ![148, 35, -562, -580, 790], ![-243, 715, 291, -249, -298], ![8, -3, -27, -24, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N3 : Nat.card (O ⧸ I67N3) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N3)

lemma isPrimeI67N3 : Ideal.IsPrime I67N3 := prime_ideal_of_norm_prime hp67.out _ NI67N3
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![1173461, 364379, 76055, 96936, -209084]] ![![-4353, -1350, -282, -359, 775]]
  ![![-1797914053, -558284319, -116527459, -148520983, 320345703]] where
 M := ![![![-1797914053, -558284319, -116527459, -148520983, 320345703]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![-1797914053, -558284319, -116527459, -148520983, 320345703]] ![![26623, 12323, 2039, 3615, -6363]]
  ![![-1069824991639, -332199704060, -69338124198, -88375447600, 190617477204]] where
 M := ![![![-1069824991639, -332199704060, -69338124198, -88375447600, 190617477204]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N2 : IdealMulLeCertificate' Table 
  ![![-1069824991639, -332199704060, -69338124198, -88375447600, 190617477204]] ![![3, 17, 29, 16, -38]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![14711429123, 4568160835, 953485777, 1215272800, -2621228270]]]
 hmul := by decide  
 g := ![![![![219573569, 68181505, 14231131, 18138400, -39122810]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2, I67N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
    exact isPrimeI67N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1 ⊙ MulI67N2)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14629, -9087, -1333, 5501, 481]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-14629, -9087, -1333, 5501, 481]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![49, 31, 70, 60, 1]] where
  M :=![![![-14629, -9087, -1333, 5501, 481], ![4810, -10502, -25109, -16907, 33487], ![334870, 230715, 73706, -100235, -67955], ![-70360, -9183, 58901, 65001, -83680], ![15440, 10355, 2877, -4918, -2451]]]
  hmulB := by decide  
  f := ![![![-3099, -1313, -237, -377, 895]], ![![8950, 5184, 713, 1587, -1367]], ![![-13670, -935, -944, 75, 8155]], ![![3680, 4547, 343, 1517, 1544]], ![![-8671, 4326, -497, 1808, 9455]]]
  g := ![![![-538, -338, -493, -329, 481], ![-23043, -14769, -33369, -28537, 33487], ![51615, 32920, 68036, 56015, -67955], ![56760, 36407, 83331, 71631, -83680], ![1909, 1216, 2457, 2002, -2451]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [8, 18, 18, 10, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 3, 11, 8], [61, 34, 52, 32], [66, 33, 8, 31], [0, 1]]
 g := ![![[26, 64, 55, 38], [48, 56, 55, 19], [58, 70, 53, 16], [30, 70, 29], [1], []], ![[57, 11, 25, 50, 5, 24], [43, 39, 13, 70, 46, 36], [51, 18, 64, 65, 55, 24], [48, 27, 50], [45, 0, 3], [36, 33, 64]], ![[21, 16, 18, 31, 6, 49], [33, 46, 69, 11, 12, 1], [30, 56, 50, 23, 10, 43], [1, 40, 57], [31, 22, 9], [46, 46, 30]], ![[47, 52, 46, 12, 13, 22], [23, 10, 56, 25, 62, 67], [10, 40, 4, 20, 5, 17], [33, 68, 37], [28, 29, 38], [53, 45, 38]]]
 h' := ![![[5, 3, 11, 8], [42, 61, 70, 31], [33, 49, 19, 27], [37, 40, 0, 4], [63, 53, 53, 61], [0, 0, 1], [0, 1]], ![[61, 34, 52, 32], [69, 0, 42, 43], [18, 3, 27, 18], [0, 49, 70, 28], [10, 60, 53, 11], [21, 41, 69, 28], [5, 3, 11, 8]], ![[66, 33, 8, 31], [54, 18, 21, 25], [66, 51, 18, 34], [56, 35, 10, 24], [8, 10, 69, 25], [16, 41, 66, 3], [61, 34, 52, 32]], ![[0, 1], [9, 63, 9, 43], [69, 39, 7, 63], [13, 18, 62, 15], [8, 19, 38, 45], [27, 60, 6, 40], [66, 33, 8, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 39, 33], []]
 b := ![[], [], [52, 52, 47, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [8, 18, 18, 10, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![138813809274615, 195993786512380, 11243109139406, 63816006637167, 83582452339550]
  a := ![3, -125, 119, -69, -298]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-55728540216385, -33733270929770, -82246881051114, -69734241320223, 83582452339550]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3099, -1313, -237, -377, 895]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-3099, -1313, -237, -377, 895]] 
 ![![71, 0, 0, 0, 0], ![65, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-3099, -1313, -237, -377, 895], ![8950, 5184, 713, 1587, -1367], ![-13670, -935, -944, 75, 8155], ![3680, 4547, 343, 1517, 1544], ![-5140, 3409, -277, 1374, 6337]]]
  hmulB := by decide  
  f := ![![![-14629, -9087, -1333, 5501, 481]], ![![-13325, -8467, -1574, 4798, 912]], ![![-2495, -1230, 381, 1300, -720]], ![![-5936, -3201, 379, 2775, -1016]], ![![-2049, -1262, -166, 783, 40]]]
  g := ![![![1264, -1313, -237, -377, 895], ![-5296, 5184, 713, 1587, -1367], ![-160, -935, -944, 75, 8155], ![-5032, 4547, 343, 1517, 1544], ![-4503, 3409, -277, 1374, 6337]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-14629, -9087, -1333, 5501, 481]] ![![-3099, -1313, -237, -377, 895]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0, 0, 0]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]] where
  M :=![![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 5 2 6 [50, 1, 55, 62, 70, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 48, 35, 35, 25], [72, 12, 13, 24, 49], [57, 31, 11, 72, 46], [19, 54, 14, 15, 26], [0, 1]]
 g := ![![[54, 36, 69, 28, 37], [32, 40, 35, 55], [41, 10, 27, 71], [22, 38, 20, 3, 1], [], []], ![[17, 45, 2, 14, 22, 51, 62, 24], [37, 24, 50, 67], [40, 18, 27, 32], [71, 53, 32, 57, 10, 3, 11, 54], [8, 42, 38, 50], [36, 66, 48, 41]], ![[50, 57, 70, 70, 62, 36, 5, 71], [3, 71, 0, 35], [27, 1, 4, 57], [32, 16, 18, 52, 15, 55, 46, 9], [12, 66, 3, 38], [66, 59, 65, 65]], ![[65, 52, 31, 58, 41, 64, 31, 49], [55, 35, 71, 16], [64, 53, 70, 12], [6, 40, 42, 50, 29, 14, 69, 3], [32, 24, 60, 3], [49, 60, 51, 72]], ![[54, 23, 53, 54, 36, 50, 45, 10], [42, 32, 25, 35], [28, 22, 37, 4], [72, 3, 71, 19, 7, 36, 31, 39], [57, 55, 40, 36], [71, 23, 34, 19]]]
 h' := ![![[1, 48, 35, 35, 25], [2, 35, 33, 14, 57], [19, 64, 23, 16, 37], [68, 49, 15, 26, 61], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[72, 12, 13, 24, 49], [51, 10, 50, 31, 67], [52, 52, 12, 41, 40], [64, 26, 9, 65, 18], [57, 13, 12, 31, 9], [26, 45, 45, 69, 14], [1, 48, 35, 35, 25]], ![[57, 31, 11, 72, 46], [12, 32, 4, 56, 40], [69, 72, 34, 30, 53], [18, 67, 63, 66, 38], [34, 48, 39, 48, 10], [59, 26, 41, 51, 44], [72, 12, 13, 24, 49]], ![[19, 54, 14, 15, 26], [72, 11, 11, 7, 70], [62, 17, 44, 61, 69], [59, 25, 8, 50, 31], [22, 71, 26, 29, 9], [69, 47, 49, 69, 21], [57, 31, 11, 72, 46]], ![[0, 1], [13, 58, 48, 38, 58], [19, 14, 33, 71, 20], [18, 52, 51, 12, 71], [15, 14, 69, 38, 44], [23, 28, 10, 30, 67], [19, 54, 14, 15, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 46, 9, 37], [], [], []]
 b := ![[], [29, 8, 71, 19, 54], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 5
  hpos := by decide
  P := [50, 1, 55, 62, 70, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3970819027381, -5629748075158, -384061747444, -1852100033966, -2301086559954]
  a := ![1, -9, 11, -3, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-54394781197, -77119836646, -5261119828, -25371233342, -31521733698]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 2073071593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12701, 3934, 816, 1075, -2267]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![12701, 3934, 816, 1075, -2267]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![19, 52, 34, 2, 1]] where
  M :=![![![12701, 3934, 816, 1075, -2267], ![-22670, -7081, -1558, -1983, 4183], ![41830, 13570, 3051, 3135, -7715], ![3620, 1076, 424, 643, -982], ![23660, 7408, 1550, 1950, -4239]]]
  hmulB := by decide  
  f := ![![![-1581, -2270, -154, -765, -937]], ![![-9370, -13423, -912, -4523, -5527]], ![![-55270, -79250, -5381, -26705, -32665]], ![![-27980, -40108, -2724, -13515, -16526]], ![![-31781, -45562, -3094, -15353, -18776]]]
  g := ![![![706, 1542, 986, 71, -2267], ![-1293, -2843, -1820, -131, 4183], ![2385, 5250, 3359, 235, -7715], ![282, 660, 428, 33, -982], ![1319, 2884, 1844, 132, -4239]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 4 2 6 [27, 4, 63, 67, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 53, 36, 69], [2, 60, 69, 17], [49, 44, 53, 72], [0, 1]]
 g := ![![[19, 62, 67, 11], [61, 26, 74, 65], [33, 41, 48, 55], [50, 0, 58, 65], [1], []], ![[57, 52, 12, 19, 19, 29], [16, 21, 39, 76, 37, 61], [72, 62, 8, 45, 12, 57], [40, 32, 41, 69, 61, 41], [10, 76, 65], [12, 6, 21]], ![[60, 62, 2, 19, 65, 53], [8, 40, 8, 21, 25, 61], [72, 32, 34, 27, 57, 30], [69, 75, 48, 2, 20, 78], [18, 31, 44], [60, 47, 52]], ![[70, 12, 70, 37, 13, 10], [66, 29, 3, 23, 16, 25], [50, 41, 43, 4, 6, 65], [33, 70, 76, 77, 33, 5], [58, 56, 38], [23, 4, 49]]]
 h' := ![![[40, 53, 36, 69], [12, 12, 42, 66], [57, 74, 36, 67], [72, 55, 3, 56], [52, 75, 16, 12], [0, 0, 1], [0, 1]], ![[2, 60, 69, 17], [78, 20, 7, 20], [25, 63, 68, 67], [64, 28, 20, 27], [32, 65, 5, 15], [12, 1, 76, 12], [40, 53, 36, 69]], ![[49, 44, 53, 72], [59, 1, 53, 49], [16, 65, 50, 8], [43, 57, 68, 5], [20, 4, 63, 67], [43, 74, 5, 53], [2, 60, 69, 17]], ![[0, 1], [75, 46, 56, 23], [74, 35, 4, 16], [10, 18, 67, 70], [40, 14, 74, 64], [42, 4, 76, 14], [49, 44, 53, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [57, 13, 78], []]
 b := ![[], [], [21, 39, 30, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 4
  hpos := by decide
  P := [27, 4, 63, 67, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4434735851202, 6102266125766, 383968866244, 1871364363414, 2503064355111]
  a := ![1, 45, -57, 10, 141]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-545866922733, -1570342789114, -1072407838070, -39680561352, 2503064355111]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 38950081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1581, -2270, -154, -765, -937]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-1581, -2270, -154, -765, -937]] 
 ![![79, 0, 0, 0, 0], ![66, 1, 0, 0, 0], ![68, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![68, 0, 0, 0, 1]] where
  M :=![![![-1581, -2270, -154, -765, -937], ![-9370, -13423, -912, -4523, -5527], ![-55270, -79250, -5381, -26705, -32665], ![-27980, -40108, -2724, -13515, -16526], ![-58280, -83556, -5674, -28156, -34435]]]
  hmulB := by decide  
  f := ![![![12701, 3934, 816, 1075, -2267]], ![![10324, 3197, 662, 873, -1841]], ![![11462, 3558, 741, 965, -2049]], ![![1332, 412, 88, 117, -242]], ![![11232, 3480, 722, 950, -2005]]]
  g := ![![![2893, -2270, -154, -765, -937], ![17096, -13423, -912, -4523, -5527], ![100962, -79250, -5381, -26705, -32665], ![51092, -40108, -2724, -13515, -16526], ![106444, -83556, -5674, -28156, -34435]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![12701, 3934, 816, 1075, -2267]] ![![-1581, -2270, -154, -765, -937]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1403, -423, -93, -139, 261]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-1403, -423, -93, -139, 261]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![59, 13, 7, 1, 0], ![27, 60, 18, 0, 1]] where
  M :=![![![-1403, -423, -93, -139, 261], ![2610, 864, 255, 253, -573], ![-5730, -2165, -468, 5, 945], ![-360, -199, -251, -217, 384], ![-2720, -861, -179, -202, 479]]]
  hmulB := by decide  
  f := ![![![959, 491, 75, 147, -201]], ![![-2010, -730, -151, -201, 681]], ![![6810, 4525, 554, 1415, -525]], ![![947, 627, 77, 196, -75]], ![![391, 656, 40, 223, 314]]]
  g := ![![![-3, -172, -46, -139, 261], ![38, 385, 106, 253, -573], ![-380, -710, -211, 5, 945], ![25, -246, -68, -217, 384], ![-45, -325, -89, -202, 479]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [74, 44, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 74, 73], [70, 8, 10], [0, 1]]
 g := ![![[43, 68, 70], [53, 66, 11], [80, 38], [53, 40], [60, 42, 1], []], ![[65, 33, 35, 14], [55, 46, 45, 46], [11, 59], [17, 30], [70, 15, 11, 24], [64, 17]], ![[46, 61, 33, 37], [28, 62, 20, 7], [16, 12], [7, 48], [61, 63, 43, 63], [44, 17]]]
 h' := ![![[55, 74, 73], [62, 70, 53], [56, 59, 29], [0, 82, 11], [42, 62, 17], [0, 0, 1], [0, 1]], ![[70, 8, 10], [47, 64, 56], [79, 21, 57], [48, 81, 15], [12, 6, 14], [32, 82, 8], [55, 74, 73]], ![[0, 1], [47, 32, 57], [70, 3, 80], [3, 3, 57], [43, 15, 52], [67, 1, 74], [70, 8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 61], []]
 b := ![[], [62, 67, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [74, 44, 41, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-29197170, -32841686, -4648982, -4640582, -7083448]
  a := ![-1, -6, 21, 13, -50]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5251208, 5451720, 1871532, -4640582, -7083448]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![959, 491, 75, 147, -201]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![959, 491, 75, 147, -201]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![44, 13, 1, 0, 0], ![59, 71, 0, 1, 0], ![23, 82, 0, 0, 1]] where
  M :=![![![959, 491, 75, 147, -201], ![-2010, -730, -151, -201, 681], ![6810, 4525, 554, 1415, -525], ![480, 887, 51, 303, 456], ![4580, 3541, 383, 1130, 79]]]
  hmulB := by decide  
  f := ![![![-1403, -423, -93, -139, 261]], ![![2610, 864, 255, 253, -573]], ![![-404, -115, -15, -34, 60]], ![![1231, 436, 149, 115, -300]], ![![2157, 726, 224, 209, -488]]]
  g := ![![![-77, 67, 75, 147, -201], ![10, -486, -151, -201, 681], ![-1072, -724, 554, 1415, -525], ![-363, -707, 51, 303, 456], ![-973, -1062, 383, 1130, 79]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [38, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 82], [0, 1]]
 g := ![![[19, 59], [36, 36], [75], [78], [30, 44], [1]], ![[0, 24], [23, 47], [75], [78], [51, 39], [1]]]
 h' := ![![[25, 82], [43, 68], [72, 77], [10, 18], [22, 24], [45, 25], [0, 1]], ![[0, 1], [0, 15], [5, 6], [45, 65], [41, 59], [6, 58], [25, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [82, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [38, 58, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![31558, 26348, 4436, -8768, 3072]
  a := ![0, -2, -18, -26, 44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3410, 4088, 4436, -8768, 3072]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-1403, -423, -93, -139, 261]] ![![959, 491, 75, 147, -201]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 5 2 6 [47, 61, 36, 38, 80, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 37, 67, 42, 28], [49, 40, 74, 12, 9], [51, 62, 48, 24, 35], [17, 38, 78, 11, 17], [0, 1]]
 g := ![![[61, 8, 3, 68, 55], [15, 58, 80, 71], [47, 15, 35, 84], [36, 55, 81, 45, 81], [1], []], ![[81, 64, 80, 46, 14, 39, 3, 12], [72, 25, 75, 85], [17, 70, 17, 5], [25, 75, 34, 60, 17, 83, 83, 19], [55, 74, 68, 52, 86, 78, 65, 41], [85, 54, 63, 72]], ![[16, 64, 58, 3, 48, 31, 88, 42], [40, 19, 11, 22], [16, 61, 63, 8], [54, 83, 23, 26, 79, 2, 35, 32], [68, 60, 43, 38, 74, 59, 23, 68], [76, 50, 55, 81]], ![[48, 48, 69, 50, 26, 73, 68, 59], [74, 61, 63, 79], [5, 2, 18, 85], [26, 42, 40, 84, 25, 35, 77, 14], [10, 3, 27, 25, 56, 3, 54, 56], [21, 86, 67, 68]], ![[5, 40, 40, 45, 77, 45, 80, 2], [41, 1, 64, 88], [65, 59, 9, 42], [88, 17, 19, 34, 22, 54, 73, 25], [36, 48, 51, 39, 84, 4, 3, 5], [12, 54, 38, 22]]]
 h' := ![![[70, 37, 67, 42, 28], [29, 56, 79, 66, 77], [17, 59, 31, 65, 58], [88, 9, 35, 83, 23], [42, 28, 53, 51, 9], [0, 0, 1], [0, 1]], ![[49, 40, 74, 12, 9], [53, 35, 6, 41, 81], [12, 48, 15, 9, 21], [30, 21, 6, 18, 19], [82, 35, 11, 81, 24], [15, 38, 10, 39, 10], [70, 37, 67, 42, 28]], ![[51, 62, 48, 24, 35], [29, 67, 11, 73, 8], [29, 31, 22, 39, 17], [43, 14, 12, 72, 50], [0, 38, 83, 58, 63], [75, 49, 36, 52, 71], [49, 40, 74, 12, 9]], ![[17, 38, 78, 11, 17], [43, 52, 52, 1, 36], [36, 13, 33, 60, 48], [87, 75, 43, 14, 21], [21, 39, 6, 65, 6], [12, 22, 34, 71, 12], [51, 62, 48, 24, 35]], ![[0, 1], [29, 57, 30, 86, 65], [40, 27, 77, 5, 34], [43, 59, 82, 80, 65], [19, 38, 25, 12, 76], [81, 69, 8, 16, 85], [17, 38, 78, 11, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 37, 37, 3], [], [], []]
 b := ![[], [16, 17, 57, 30, 73], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 5
  hpos := by decide
  P := [47, 61, 36, 38, 80, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8669867566747, -12728346211686, -1187614359908, -4516204182491, -4761287577559]
  a := ![13, -7, 18, 8, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-97414242323, -143015125974, -13343981572, -50743867219, -53497613231]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -35, -1, -10, -18]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-23, -35, -1, -10, -18]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![31, 74, 39, 1, 0], ![11, 74, 70, 0, 1]] where
  M :=![![![-23, -35, -1, -10, -18], ![-180, -236, -23, -72, -78], ![-780, -1225, -98, -470, -510], ![-420, -617, -21, -219, -294], ![-920, -1339, -91, -454, -559]]]
  hmulB := by decide  
  f := ![![![-1199, -363, -77, -96, 210]], ![![2100, 630, 135, 166, -366]], ![![-3660, -1085, -234, -280, 630]], ![![-257, -73, -16, -17, 42]], ![![-1197, -350, -76, -88, 203]]]
  g := ![![![5, 21, 17, -10, -18], ![30, 112, 85, -72, -78], ![200, 735, 556, -470, -510], ![99, 385, 300, -219, -294], ![199, 759, 585, -454, -559]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [6, 10, 66, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 20, 86], [75, 76, 11], [0, 1]]
 g := ![![[72, 8, 8], [2, 35], [67, 2], [46, 33], [71, 88], [1]], ![[9, 7, 10, 93], [11, 93], [82, 75], [58, 88], [75, 32], [25, 17, 46, 27]], ![[94, 8, 63, 22], [46, 95], [22, 35], [90, 73], [5, 43], [66, 75, 76, 70]]]
 h' := ![![[53, 20, 86], [20, 32, 69], [56, 11, 61], [19, 31, 83], [95, 46, 79], [91, 87, 31], [0, 1]], ![[75, 76, 11], [35, 71, 42], [2, 15, 53], [94, 93, 50], [32, 90, 66], [26, 87, 41], [53, 20, 86]], ![[0, 1], [63, 91, 83], [40, 71, 80], [50, 70, 61], [69, 58, 49], [14, 20, 25], [75, 76, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 47], []]
 b := ![[], [75, 83, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [6, 10, 66, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-44199, 10936, 63678, 43716, -81857]
  a := ![-1, -3, -3, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5144, 29210, 42152, 43716, -81857]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![123, 178, 12, 60, 74]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![123, 178, 12, 60, 74]] 
 ![![97, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![85, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![123, 178, 12, 60, 74], ![740, 1057, 72, 356, 434], ![4340, 6230, 423, 2100, 2570], ![2200, 3154, 214, 1063, 1300], ![4580, 6570, 446, 2214, 2709]]]
  hmulB := by decide  
  f := ![![![-1501, -530, -104, -128, 286]], ![![-280, -99, -20, -24, 54]], ![![-1365, -480, -93, -120, 260]], ![![-222, -78, -14, -17, 40]], ![![-203, -72, -14, -18, 39]]]
  g := ![![![-63, 178, 12, 60, 74], ![-374, 1057, 72, 356, 434], ![-2205, 6230, 423, 2100, 2570], ![-1116, 3154, 214, 1063, 1300], ![-2325, 6570, 446, 2214, 2709]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-307, -207, -59, 97, 51]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-307, -207, -59, 97, 51]] 
 ![![97, 0, 0, 0, 0], ![75, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![58, 0, 0, 0, 1]] where
  M :=![![![-307, -207, -59, 97, 51], ![510, 56, -447, -483, 633], ![6330, 4755, 2138, -1455, -2265], ![-2520, -963, 909, 1619, -1416], ![300, 219, 89, -76, -91]]]
  hmulB := by decide  
  f := ![![![76949, 25809, 5135, 7025, -14469]], ![![58005, 19445, 3870, 5292, -10902]], ![![3647, 1272, 247, 350, -702]], ![![41444, 13893, 2765, 3781, -7788]], ![![47666, 16017, 3183, 4362, -8971]]]
  g := ![![![75, -207, -59, 97, 51], ![-153, 56, -447, -483, 633], ![-1499, 4755, 2138, -1455, -2265], ![688, -963, 909, 1619, -1416], ![-72, 219, 89, -76, -91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-23, -35, -1, -10, -18]] ![![123, 178, 12, 60, 74]]
  ![![-137509, -197119, -13387, -66422, -81224]] where
 M := ![![![-137509, -197119, -13387, -66422, -81224]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![-137509, -197119, -13387, -66422, -81224]] ![![-307, -207, -59, 97, 51]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![-38897, -53156, -2716, -16005, -22795]]]
 hmul := by decide  
 g := ![![![![-401, -548, -28, -165, -235]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![88729, 42007, 6875, 12374, -21738]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![88729, 42007, 6875, 12374, -21738]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![17, 52, 1, 0, 0], ![53, 55, 0, 1, 0], ![13, 22, 0, 0, 1]] where
  M :=![![![88729, 42007, 6875, 12374, -21738], ![-217380, -103640, -16853, -30576, 52506], ![525060, 245345, 40594, 72070, -130950], ![-22260, -12215, -1755, -3705, 3894], ![301540, 139259, 23279, 40802, -76633]]]
  hmulB := by decide  
  f := ![![![-18571, -6573, 7691, 12516, -11742]], ![![-117420, -96762, -55863, 17426, 63354]], ![![-57307, -47780, -28315, 7884, 32304]], ![![-71443, -53950, -24669, 16107, 26274]], ![![-27703, -21798, -11228, 5264, 12377]]]
  g := ![![![-3974, -5127, 6875, 12374, -21738], ![9971, 12864, -16853, -30576, 52506], ![-22598, -29193, 40594, 72070, -130950], ![1518, 1952, -1755, -3705, 3894], ![-12480, -16133, 23279, 40802, -76633]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [85, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 100], [0, 1]]
 g := ![![[54, 82], [65], [57, 23], [20], [37], [56, 1]], ![[0, 19], [65], [32, 78], [20], [37], [11, 100]]]
 h' := ![![[56, 100], [39, 48], [3, 41], [4, 86], [54, 11], [88, 21], [0, 1]], ![[0, 1], [0, 53], [77, 60], [73, 15], [64, 90], [52, 80], [56, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [74, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [85, 45, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![81429, 83100, -2828, -230, 41860]
  a := ![3, 10, -28, -15, 70]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3985, -6714, -2828, -230, 41860]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-99809, -47283, -7709, -13934, 23862]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-99809, -47283, -7709, -13934, 23862]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![4, 40, 1, 0, 0], ![85, 53, 0, 1, 0], ![65, 77, 0, 0, 1]] where
  M :=![![![-99809, -47283, -7709, -13934, 23862], ![238620, 110194, 18381, 32292, -59742], ![-597420, -294345, -46424, -87450, 134010], ![14700, 615, 1011, -221, -9198], ![-351360, -179043, -27427, -53554, 73675]]]
  hmulB := by decide  
  f := ![![![-73549, -35559, 12427, 38920, -22758]], ![![-227580, -222832, -175077, -5682, 210762]], ![![-72176, -77681, -68796, -9640, 84318]], ![![-178445, -142612, -76495, 31443, 85218]], ![![-219925, -192262, -125509, 20306, 146155]]]
  g := ![![![-4313, -8295, -7709, -13934, 23862], ![12906, 22412, 18381, 32292, -59742], ![-16724, -40805, -46424, -87450, 134010], ![6211, 6734, 1011, -221, -9198], ![-4737, -18976, -27427, -53554, 73675]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P1 : CertificateIrreducibleZModOfList' 101 2 2 6 [17, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 100], [0, 1]]
 g := ![![[61, 6], [47], [42, 30], [71], [25], [74, 1]], ![[0, 95], [47], [40, 71], [71], [25], [47, 100]]]
 h' := ![![[74, 100], [58, 62], [94, 42], [75, 38], [75, 77], [55, 5], [0, 1]], ![[0, 1], [0, 39], [71, 59], [59, 63], [16, 24], [21, 96], [74, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [95, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N1 : CertifiedPrimeIdeal' SI101N1 101 where
  n := 2
  hpos := by decide
  P := [17, 27, 1]
  hirr := P101P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16225, 16105, -1061, -419, 8789]
  a := ![1, 5, -13, -6, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5101, -5901, -1061, -419, 8789]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N1 B_one_repr
lemma NI101N1 : Nat.card (O ⧸ I101N1) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 15, 1, 5, 7]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![9, 15, 1, 5, 7]] 
 ![![101, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![89, 0, 0, 0, 1]] where
  M :=![![![9, 15, 1, 5, 7], ![70, 96, 7, 33, 37], ![370, 545, 34, 185, 235], ![200, 283, 19, 93, 116], ![400, 581, 39, 196, 243]]]
  hmulB := by decide  
  f := ![![![-9091, -2845, -589, -759, 1627]], ![![-649, -203, -42, -54, 116]], ![![-2090, -655, -136, -175, 375]], ![![-2548, -797, -165, -213, 456]], ![![-8179, -2560, -530, -683, 1464]]]
  g := ![![![-9, 15, 1, 5, 7], ![-51, 96, 7, 33, 37], ![-310, 545, 34, 185, 235], ![-155, 283, 19, 93, 116], ![-324, 581, 39, 196, 243]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![88729, 42007, 6875, 12374, -21738]] ![![-99809, -47283, -7709, -13934, 23862]]
  ![![4880256559, 2309570920, 377672046, 680343606, -1186375248]] where
 M := ![![![4880256559, 2309570920, 377672046, 680343606, -1186375248]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![4880256559, 2309570920, 377672046, 680343606, -1186375248]] ![![9, 15, 1, 5, 7]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![6849552451, 4007143185, 545996405, 1228858415, -1000476205]]]
 hmul := by decide  
 g := ![![![![67817351, 39674685, 5405905, 12166915, -9905705]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1965283, 610255, 127375, 162347, -350167]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![1965283, 610255, 127375, 162347, -350167]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![58, 87, 90, 1, 0], ![99, 96, 22, 0, 1]] where
  M :=![![![1965283, 610255, 127375, 162347, -350167], ![-3501670, -1087332, -226953, -289265, 623915], ![6239150, 1937365, 404378, 515395, -1111675], ![639160, 198467, 41427, 52801, -113888], ![3619900, 1124037, 234615, 299028, -644985]]]
  hmulB := by decide  
  f := ![![![-10179, -4815, -789, -1419, 2479]], ![![24790, 11726, 1921, 3445, -6035]], ![![-60350, -28545, -4644, -8375, 14635]], ![![-37504, -17739, -2878, -5204, 9081]], ![![93, 44, 14, 11, -34]]]
  g := ![![![264230, 195166, -65827, 162347, -350167], ![-470795, -347739, 117289, -289265, 623915], ![838855, 619600, -208974, 515395, -1111675], ![85938, 63476, -21409, 52801, -113888], ![486697, 359487, -121245, 299028, -644985]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [93, 12, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 26, 23], [43, 76, 80], [0, 1]]
 g := ![![[5, 11, 16], [27, 8, 82], [73, 59, 1], [27, 13], [64, 100], [1]], ![[24, 32, 68, 41], [79, 2, 34, 56], [18, 86, 102, 4], [7, 14], [61, 36], [28, 34, 35, 13]], ![[31, 9, 69, 74], [43, 83, 76, 39], [6, 83, 7, 43], [88, 52], [11, 50], [49, 17, 26, 90]]]
 h' := ![![[50, 26, 23], [64, 43, 99], [9, 89, 44], [13, 17, 102], [19, 95, 61], [10, 91, 93], [0, 1]], ![[43, 76, 80], [32, 58, 67], [33, 69, 35], [60, 74, 6], [89, 95, 23], [32, 25, 97], [50, 26, 23]], ![[0, 1], [83, 2, 40], [70, 48, 24], [29, 12, 98], [30, 16, 19], [69, 90, 16], [43, 76, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 13], []]
 b := ![[], [89, 5, 89], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [93, 12, 10, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-190375, -228650, -39663, -45827, -41308]
  a := ![4, -1, 4, 3, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![63661, 74989, 48481, -45827, -41308]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10179, 4815, 789, 1419, -2479]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![10179, 4815, 789, 1419, -2479]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![70, 27, 1, 0, 0], ![17, 17, 0, 1, 0], ![97, 63, 0, 0, 1]] where
  M :=![![![10179, 4815, 789, 1419, -2479], ![-24790, -11726, -1921, -3445, 6035], ![60350, 28545, 4644, 8375, -14635], ![-2240, -1041, -161, -325, 544], ![34840, 16489, 2695, 4856, -8467]]]
  hmulB := by decide  
  f := ![![![-1965283, -610255, -127375, -162347, 350167]], ![![3501670, 1087332, 226953, 289265, -623915]], ![![-478290, -148517, -30999, -39510, 85220]], ![![247373, 76814, 16033, 20435, -44076]], ![![255853, 79448, 16583, 21136, -45587]]]
  g := ![![![1663, 1122, 789, 1419, -2479], ![-4050, -2733, -1921, -3445, 6035], ![9830, 6629, 4644, 8375, -14635], ![-371, -247, -161, -325, 544], ![5679, 3831, 2695, 4856, -8467]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [41, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 102], [0, 1]]
 g := ![![[62, 98], [12, 9], [20, 15], [81], [15], [33, 1]], ![[0, 5], [0, 94], [0, 88], [81], [15], [66, 102]]]
 h' := ![![[33, 102], [23, 43], [4, 3], [24, 18], [96, 94], [89, 18], [0, 1]], ![[0, 1], [0, 60], [0, 100], [0, 85], [5, 9], [65, 85], [33, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [35, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [41, 70, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![870940, 948240, -39113, 86823, 495870]
  a := ![7, -44, 91, 25, -228]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-446277, -298170, -39113, 86823, 495870]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![1965283, 610255, 127375, 162347, -350167]] ![![10179, 4815, 789, 1419, -2479]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![-103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)


lemma PB1321I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB1321I2 : PrimesBelowBoundCertificateInterval O 61 103 1321 where
  m := 9
  g := ![4, 2, 1, 2, 2, 1, 3, 3, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB1321I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2, I67N3]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
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
    · exact ![4489, 67, 67, 67]
    · exact ![25411681, 71]
    · exact ![2073071593]
    · exact ![38950081, 79]
    · exact ![571787, 6889]
    · exact ![5584059449]
    · exact ![912673, 97, 97]
    · exact ![10201, 10201, 101]
    · exact ![1092727, 10609]
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
      exact NI67N3
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
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
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I67N1, I67N2, I67N3, I71N1, I79N1, I97N1, I97N2, I101N2]
  Il := ![[I67N1, I67N2, I67N3], [I71N1], [], [I79N1], [], [], [I97N1, I97N2], [I101N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
