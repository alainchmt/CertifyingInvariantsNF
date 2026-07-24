
import IdealArithmetic.Examples.NF5_3_6075000000_7.RI5_3_6075000000_7
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![105735, 26313, -6313, 2566, 29010]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![105735, 26313, -6313, 2566, 29010]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![145, 161, 1, 0, 0], ![38, 36, 0, 1, 0], ![139, 174, 0, 0, 1]] where
  M :=![![![105735, 26313, -6313, 2566, 29010], ![-609210, -151608, 36373, -14784, -167146], ![3510066, 873515, -209570, 85182, 963046], ![-2302174, -572923, 137451, -55867, -631638], ![2634630, 655657, -157301, 63936, 722855]]]
  hmulB := by decide  
  f := ![![![-679, -203, 31, 8, -54]], ![![1134, -232, -273, 258, 490]], ![![371, -352, -198, 218, 358]], ![![56, -97, -47, 55, 86]], ![![515, -342, -216, 230, 389]]]
  g := ![![![-15622, -20590, -6313, 2566, 29010], ![90009, 118633, 36373, -14784, -167146], ![-518606, -683529, -209570, 85182, 963046], ![340141, 448310, 137451, -55867, -631638], ![-389262, -513052, -157301, 63936, 722855]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [89, 183, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 198], [0, 1]]
 g := ![![[11, 161], [175, 28], [104, 8], [7], [18], [29], [16, 1]], ![[0, 38], [26, 171], [33, 191], [7], [18], [29], [32, 198]]]
 h' := ![![[16, 198], [146, 165], [97, 174], [60, 159], [177, 112], [171, 60], [168, 167], [0, 1]], ![[0, 1], [0, 34], [95, 25], [17, 40], [178, 87], [136, 139], [54, 32], [16, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [167, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [89, 183, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2623256, -2229200, -579771, 1715201, 2159617]
  a := ![0, 14, 13, -137, -247]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1426738, -1740737, -579771, 1715201, 2159617]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34926, -23234, -4569, 5947, 7313]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-34926, -23234, -4569, 5947, 7313]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![90, 59, 1, 0, 0], ![140, 184, 0, 1, 0], ![155, 87, 0, 0, 1]] where
  M :=![![![-34926, -23234, -4569, 5947, 7313], ![-153573, -102121, -20043, 26109, 32067], ![-673407, -448242, -88144, 114723, 141057], ![-743764, -494684, -97168, 126533, 155484], ![185838, 123522, 24246, -31584, -38797]]]
  hmulB := by decide  
  f := ![![![-102058, -25388, 6097, -2485, -28013]], ![![588273, 146447, -35097, 14217, 161301]], ![![111234, 27703, -6631, 2676, 30480]], ![![483308, 120332, -28828, 11665, 132496]], ![![164911, 41069, -9832, 3970, 45193]]]
  g := ![![![-7989, -7458, -4569, 5947, 7313], ![-35052, -32731, -20043, 26109, 32067], ![-154098, -143863, -88144, 114723, 141057], ![-169916, -158648, -97168, 126533, 155484], ![42407, 39597, 24246, -31584, -38797]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P1 : CertificateIrreducibleZModOfList' 199 2 2 7 [181, 113, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 198], [0, 1]]
 g := ![![[49, 66], [143, 56], [147, 25], [158], [50], [14], [86, 1]], ![[153, 133], [183, 143], [108, 174], [158], [50], [14], [172, 198]]]
 h' := ![![[86, 198], [186, 71], [59, 97], [138, 5], [105, 122], [198, 99], [155, 51], [0, 1]], ![[0, 1], [123, 128], [43, 102], [170, 194], [50, 77], [155, 100], [163, 148], [86, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [144]]
 b := ![[], [88, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N1 : CertifiedPrimeIdeal' SI199N1 199 where
  n := 2
  hpos := by decide
  P := [181, 113, 1]
  hirr := P199P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-939515031, -711705111, -166557321, 522800962, 623346416]
  a := ![3, 252, 254, -2387, -4062]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-782714499, -710107228, -166557321, 522800962, 623346416]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N1 B_one_repr
lemma NI199N1 : Nat.card (O ⧸ I199N1) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![60, 33, 4, -17, -15]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![60, 33, 4, -17, -15]] 
 ![![199, 0, 0, 0, 0], ![178, 1, 0, 0, 0], ![156, 0, 1, 0, 0], ![97, 0, 0, 1, 0], ![107, 0, 0, 0, 1]] where
  M :=![![![60, 33, 4, -17, -15], ![315, 208, 42, -129, -133], ![2793, 1599, 253, -909, -875], ![4046, 2455, 425, -1435, -1414], ![-258, -179, -35, 108, 109]]]
  hmulB := by decide  
  f := ![![![13388, 8959, 1770, -2299, -2841]], ![![12275, 8212, 1622, -2107, -2603]], ![![11793, 7891, 1559, -2025, -2503]], ![![7974, 5328, 1051, -1366, -1685]], ![![6832, 4576, 905, -1175, -1454]]]
  g := ![![![-16, 33, 4, -17, -15], ![-83, 208, 42, -129, -133], ![-701, 1599, 253, -909, -875], ![-1049, 2455, 425, -1435, -1414], ![75, -179, -35, 108, 109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![105735, 26313, -6313, 2566, 29010]] ![![-34926, -23234, -4569, 5947, 7313]]
  ![![13388, 8959, 1770, -2299, -2841]] where
 M := ![![![13388, 8959, 1770, -2299, -2841]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![13388, 8959, 1770, -2299, -2841]] ![![60, 33, 4, -17, -15]]
  ![![199, 0, 0, 0, 0]] where
 M := ![![![199, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1, I199N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
    exact isPrimeI199N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0 ⊙ MulI199N1)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5560, 873, -522, 255, 897]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![5560, 873, -522, 255, 897]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![110, 105, 158, 1, 0], ![137, 204, 66, 0, 1]] where
  M :=![![![5560, 873, -522, 255, 897], ![-18837, -2246, 1662, -837, -2709], ![56889, 4719, -4733, 2439, 7245], ![-9534, 195, 657, -401, -798], ![10044, -135, -693, 396, 835]]]
  hmulB := by decide  
  f := ![![![10240, 2547, -612, 249, 2811]], ![![-59031, -14696, 3522, -1431, -16191]], ![![340011, 84597, -20309, 8253, 93303]], ![![229511, 57099, -13711, 5572, 62985]], ![![57140, 14208, -3417, 1389, 15688]]]
  g := ![![![-689, -990, -474, 255, 897], ![2106, 3025, 1482, -837, -2709], ![-5706, -8196, -4115, 2439, 7245], ![682, 972, 553, -401, -798], ![-701, -1005, -561, 396, 835]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [153, 60, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [176, 202, 199], [175, 8, 12], [0, 1]]
 g := ![![[134, 202, 56], [87, 173, 182], [164, 62], [61, 19], [101, 7, 34], [25, 188], [1]], ![[71, 83, 95, 78], [185, 195, 122, 163], [202, 52], [131, 173], [49, 138, 112, 34], [12, 105], [150, 114, 7, 171]], ![[96, 133, 17, 92], [136, 38, 185, 67], [178, 119], [83, 34], [120, 209, 35, 98], [145, 20], [58, 118, 194, 40]]]
 h' := ![![[176, 202, 199], [193, 64, 181], [37, 209, 155], [130, 136, 189], [161, 87, 190], [172, 123, 33], [58, 151, 140], [0, 1]], ![[175, 8, 12], [117, 191, 47], [39, 29, 209], [136, 84, 91], [150, 197, 54], [112, 96, 54], [7, 196, 152], [176, 202, 199]], ![[0, 1], [15, 167, 194], [167, 184, 58], [155, 202, 142], [163, 138, 178], [73, 203, 124], [174, 75, 130], [175, 8, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147, 13], []]
 b := ![[], [100, 15, 89], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [153, 60, 71, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![66232397022, 42037644212, 7856096507, -25813406079, -26973343011]
  a := ![1, 17, 17, -162, -279]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![31284621129, 39123257141, 27803862065, -25813406079, -26973343011]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2431632, 473651, 105504, -79943, -3307]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![-2431632, 473651, 105504, -79943, -3307]] 
 ![![211, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![207, 0, 1, 0, 0], ![141, 0, 0, 1, 0], ![85, 0, 0, 0, 1]] where
  M :=![![![-2431632, 473651, 105504, -79943, -3307], ![69447, -2427430, 342586, -86463, -1096053], ![23017113, 9677801, -3026139, 1277349, 6461889], ![-14932666, -2743821, 1457173, -698743, -2587102], ![15129264, 2824113, -1482681, 709566, 2641219]]]
  hmulB := by decide  
  f := ![![![8436008, 6156949, 1351758, -1690141, -2397089]], ![![318535, 202190, 37190, -49673, -55339]], ![![8961057, 6581638, 1454861, -1814712, -2594460]], ![![6755266, 4801830, 1023707, -1293432, -1770365]], ![![2998466, 2278588, 521703, -642853, -956734]]]
  g := ![![![-64764, 473651, 105504, -79943, -3307], ![186563, -2427430, 342586, -86463, -1096053], ![-470590, 9677801, -3026139, 1277349, 6461889], ![34818, -2743821, 1457173, -698743, -2587102], ![-38656, 2824113, -1482681, 709566, 2641219]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![435415203, 74374149, -41682779, 20167292, 72878822]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![435415203, 74374149, -41682779, 20167292, 72878822]] 
 ![![211, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![152, 0, 1, 0, 0], ![96, 0, 0, 1, 0], ![49, 0, 0, 0, 1]] where
  M :=![![![435415203, 74374149, -41682779, 20167292, 72878822], ![-1530455262, -198978708, 137572415, -68591046, -227809666], ![4784002986, 450850363, -405532492, 208115076, 634393018], ![-880783778, -4232457, 63384617, -35420027, -81027282], ![920155332, 7890067, -66714521, 37130838, 86224249]]]
  hmulB := by decide  
  f := ![![![-59499023, -37970539, -7039843, 9380674, 10580326]], ![![-30097565, -19279755, -3594196, 4779130, 5436212]], ![![-48561430, -30891131, -5700298, 7610978, 8521126]], ![![-32293486, -20915321, -3961123, 5236815, 6100750]], ![![-12872525, -7999358, -1424510, 1928758, 2038691]]]
  g := ![![![-30314986, 74374149, -41682779, 20167292, 72878822], ![74885112, -198978708, 137572415, -68591046, -227809666], ![-147284127, 450850363, -405532492, 208115076, 634393018], ![-12837171, -4232457, 63384617, -35420027, -81027282], ![11651834, 7890067, -66714521, 37130838, 86224249]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![5560, 873, -522, 255, 897]] ![![-2431632, 473651, 105504, -79943, -3307]]
  ![![-15711059697, -2703903946, 1506938634, -728440220, -2638884814]] where
 M := ![![![-15711059697, -2703903946, 1506938634, -728440220, -2638884814]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![-15711059697, -2703903946, 1506938634, -728440220, -2638884814]] ![![435415203, 74374149, -41682779, 20167292, 72878822]]
  ![![211, 0, 0, 0, 0]] where
 M := ![![![2719983096441474397, 31188562956711059, -198334514122399201, 110048087474074984, 258450949550789868]]]
 hmul := by decide  
 g := ![![![![12890915149011727, 147813094581569, -939974000580091, 521554916938744, 1224886016828388]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1, I211N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
    exact isPrimeI211N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0 ⊙ MulI211N1)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10106, 2520, -601, 233, 2757]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![10106, 2520, -601, 233, 2757]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![0, 0, 223, 0, 0], ![170, 166, 70, 1, 0], ![79, 129, 39, 0, 1]] where
  M :=![![![10106, 2520, -601, 233, 2757], ![-57897, -14339, 3489, -1509, -16037], ![336777, 84456, -19808, 7353, 91133], ![-216356, -52732, 13432, -6579, -61460], ![251196, 62474, -15016, 6174, 69025]]]
  hmulB := by decide  
  f := ![![![-1338, -1130, 257, -95, -633]], ![![13293, 4197, -1549, 687, 3101]], ![![-65121, -13754, 6608, -3111, -12089]], ![![-11464, -2042, 1108, -533, -1954]], ![![-4278, -391, 360, -185, -560]]]
  g := ![![![-1109, -1757, -558, 233, 2757], ![6572, 10336, 3294, -1509, -16037], ![-36380, -57813, -18335, 7353, 91133], ![25818, 40214, 12874, -6579, -61460], ![-28033, -44245, -14077, 6174, 69025]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [137, 129, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 29, 168], [77, 193, 55], [0, 1]]
 g := ![![[63, 130, 110], [214, 193, 131], [44, 74, 164], [11, 163, 53], [201, 40, 55], [132, 156], [1]], ![[136, 144, 24, 87], [24, 65, 157, 44], [28, 210, 147, 145], [130, 164, 163, 90], [82, 177, 121, 221], [92, 139], [183, 222, 57, 206]], ![[47, 88, 90, 64], [99, 197, 19, 14], [203, 59, 152, 220], [119, 102, 12, 127], [218, 11, 123, 217], [121, 171], [222, 147, 11, 17]]]
 h' := ![![[66, 29, 168], [118, 191, 188], [216, 36, 77], [54, 179, 68], [115, 67, 161], [16, 68, 72], [86, 94, 143], [0, 1]], ![[77, 193, 55], [140, 99, 134], [38, 78, 170], [38, 182, 157], [28, 207, 182], [216, 197, 121], [177, 40, 129], [66, 29, 168]], ![[0, 1], [205, 156, 124], [141, 109, 199], [222, 85, 221], [51, 172, 103], [189, 181, 30], [189, 89, 174], [77, 193, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [112, 18], []]
 b := ![[], [75, 16, 199], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [137, 129, 80, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9491803264525, -6111884422430, -1166425115200, 3793993826424, 4021102910106]
  a := ![1, -88, -84, 851, 1501]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4359362706973, -5177745000056, -1899412585018, 3793993826424, 4021102910106]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 11089567 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, 5, -5, 2, 8]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![39, 5, -5, 2, 8]] 
 ![![223, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![192, 0, 1, 0, 0], ![187, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![39, 5, -5, 2, 8], ![-168, -30, 13, -12, -28], ![588, 83, -44, -30, 28], ![70, 91, 21, -101, -98], ![132, 19, -5, 6, 11]]]
  hmulB := by decide  
  f := ![![![-318275, -79203, 19003, -7724, -87320]], ![![-44585, -11095, 2662, -1082, -12232]], ![![-321408, -79983, 19190, -7800, -88180]], ![![-235821, -58684, 14080, -5723, -64698]], ![![-114059, -28384, 6810, -2768, -31293]]]
  g := ![![![0, 5, -5, 2, 8], ![10, -30, 13, -12, -28], ![45, 83, -44, -30, 28], ![76, 91, 21, -101, -98], ![-6, 19, -5, 6, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-364, -17, 28, -15, -41]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![-364, -17, 28, -15, -41]] 
 ![![223, 0, 0, 0, 0], ![210, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![170, 0, 0, 1, 0], ![163, 0, 0, 0, 1]] where
  M :=![![![-364, -17, 28, -15, -41], ![861, -8, -58, 33, 77], ![-1617, 193, 75, -51, -77], ![-126, -95, 31, -13, -42], ![90, 91, -29, 12, 35]]]
  hmulB := by decide  
  f := ![![![-2380, -1367, -218, 1011, 953]], ![![-2331, -1340, -214, 987, 931]], ![![-1281, -749, -123, 507, 485]], ![![-2954, -1721, -281, 1187, 1132]], ![![-1672, -960, -153, 711, 670]]]
  g := ![![![49, -17, 28, -15, -41], ![-56, -8, -58, 33, 77], ![-112, 193, 75, -51, -77], ![122, -95, 31, -13, -42], ![-113, 91, -29, 12, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![10106, 2520, -601, 233, 2757]] ![![39, 5, -5, 2, 8]]
  ![![-2380, -1367, -218, 1011, 953]] where
 M := ![![![-2380, -1367, -218, 1011, 953]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![-2380, -1367, -218, 1011, 953]] ![![-364, -17, 28, -15, -41]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3088, -769, 184, -75, -849]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-3088, -769, 184, -75, -849]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![159, 90, 135, 1, 0], ![119, 136, 67, 0, 1]] where
  M :=![![![-3088, -769, 184, -75, -849], ![17829, 4444, -1062, 429, 4893], ![-102753, -25575, 6139, -2511, -28245], ![67578, 16853, -4021, 1607, 18494], ![-77250, -19233, 4611, -1872, -21197]]]
  hmulB := by decide  
  f := ![![![-128, -35, 2, 3, -3]], ![![63, -106, -42, 39, 63]], ![![-1323, -501, -61, 99, 105]], ![![-855, -367, -52, 77, 86]], ![![-419, -229, -42, 54, 67]]]
  g := ![![![484, 535, 296, -75, -849], ![-2787, -3082, -1704, 429, 4893], ![16113, 17805, 9857, -2511, -28245], ![-10523, -11643, -6432, 1607, 18494], ![12083, 13357, 7390, -1872, -21197]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [212, 217, 180, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [204, 144, 201], [70, 82, 26], [0, 1]]
 g := ![![[59, 215, 75], [157, 1, 144], [193, 141], [109, 167], [219, 102], [223, 116, 166], [1]], ![[99, 218, 83, 55], [7, 5, 159, 198], [77, 70], [225, 110], [32, 87], [201, 80, 82, 138], [25, 214, 91, 130]], ![[65, 126, 172, 57], [218, 6, 63, 110], [206, 166], [210, 89], [82, 121], [99, 51, 125, 63], [146, 82, 151, 97]]]
 h' := ![![[204, 144, 201], [85, 7, 23], [187, 68, 12], [223, 185, 82], [75, 174, 103], [167, 109, 130], [15, 10, 47], [0, 1]], ![[70, 82, 26], [151, 141, 115], [212, 82, 124], [54, 89, 98], [159, 13, 63], [157, 18, 108], [12, 221, 189], [204, 144, 201]], ![[0, 1], [86, 79, 89], [142, 77, 91], [50, 180, 47], [87, 40, 61], [197, 100, 216], [150, 223, 218], [70, 82, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132, 5], []]
 b := ![[], [131, 211, 201], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [212, 217, 180, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![68553102666, 58055349106, 14858070968, -42183027102, -53444781040]
  a := ![-1, 17, 10, -189, -406]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![57866005972, 49000079338, 40926727134, -42183027102, -53444781040]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-128, -35, 2, 3, -3]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![-128, -35, 2, 3, -3]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![216, 96, 1, 0, 0], ![21, 83, 0, 1, 0], ![132, 83, 0, 0, 1]] where
  M :=![![![-128, -35, 2, 3, -3], ![63, -106, -42, 39, 63], ![-1323, -501, -61, 99, 105], ![-798, -569, -107, 127, 154], ![192, 165, 27, -36, -37]]]
  hmulB := by decide  
  f := ![![![-3088, -769, 184, -75, -849]], ![![17829, 4444, -1062, 429, 4893]], ![![4149, 1035, -247, 99, 1137]], ![![6531, 1628, -389, 157, 1792]], ![![4383, 1093, -261, 105, 1202]]]
  g := ![![![-1, -1, 2, 3, -3], ![0, -20, -42, 39, 63], ![-18, -51, -61, 99, 105], ![-3, -60, -107, 127, 154], ![0, 16, 27, -36, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P1 : CertificateIrreducibleZModOfList' 227 2 2 7 [200, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [170, 226], [0, 1]]
 g := ![![[124, 23], [119, 196], [112], [12], [12], [135, 70], [170, 1]], ![[175, 204], [70, 31], [112], [12], [12], [4, 157], [113, 226]]]
 h' := ![![[170, 226], [35, 134], [6, 14], [29, 79], [39, 100], [13, 100], [50, 98], [0, 1]], ![[0, 1], [115, 93], [116, 213], [66, 148], [14, 127], [215, 127], [139, 129], [170, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [214, 123]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N1 : CertifiedPrimeIdeal' SI227N1 227 where
  n := 2
  hpos := by decide
  P := [200, 57, 1]
  hirr := P227P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3852776, 878260, -303968, 282198, 1475628]
  a := ![0, 0, 12, 42, 196]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-577970, -510310, -303968, 282198, 1475628]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N1 B_one_repr
lemma NI227N1 : Nat.card (O ⧸ I227N1) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-3088, -769, 184, -75, -849]] ![![-128, -35, 2, 3, -3]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![227, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22040, 13265, 1838, -2821, -2731]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![22040, 13265, 1838, -2821, -2731]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![118, 220, 1, 0, 0], ![140, 3, 0, 1, 0], ![24, 42, 0, 0, 1]] where
  M :=![![![22040, 13265, 1838, -2821, -2731], ![57351, 47602, 12410, -14361, -20377], ![427917, 242695, 37143, -54789, -58415], ![356650, 250715, 51649, -65697, -82558], ![-70776, -60887, -14441, 17196, 23027]]]
  hmulB := by decide  
  f := ![![![261684936, 65123261, -15623948, 6350443, 71797681]], ![![-1507751301, -375220688, 90020714, -36589701, -413677565]], ![![-1275717183, -317476379, 76167069, -30958799, -350015069]], ![![115348835, 28705879, -6886917, 2799214, 31647875]], ![![-220631160, -54906511, 13172849, -5354226, -60533977]]]
  g := ![![![1160, -1170, 1838, -2821, -2731], ![4771, -7789, 12410, -14361, -20377], ![22347, -23192, 37143, -54789, -58415], ![23760, -32522, 51649, -65697, -82558], ![-5794, 9159, -14441, 17196, 23027]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [63, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 228], [0, 1]]
 g := ![![[], [158], [], [], [212], [0, 76], [0, 1]], ![[], [158], [], [], [212], [0, 153], [0, 228]]]
 h' := ![![[0, 228], [122], [0, 171], [209], [155], [0, 21], [0, 166], [0, 1]], ![[0, 1], [122], [0, 58], [209], [155], [0, 208], [0, 63], [0, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [0, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [63, 0, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2589009, -3722402, -1303768, 3468418, 5072652]
  a := ![13, 18, 13, -191, -387]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1991557, 260480, -1303768, 3468418, 5072652]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77776674, 19355591, -4643678, 1887463, 21339371]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![77776674, 19355591, -4643678, 1887463, 21339371]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![142, 228, 1, 0, 0], ![71, 23, 0, 1, 0], ![42, 139, 0, 0, 1]] where
  M :=![![![77776674, 19355591, -4643678, 1887463, 21339371], ![-448126791, -111521450, 26755484, -10874901, -122951115], ![2581973415, 642552661, -154157517, 62658795, 708409191], ![-1693462162, -421437785, 101108225, -41095543, -464628990], ![1938015348, 482296953, -115709625, 47030946, 531727451]]]
  hmulB := by decide  
  f := ![![![491066, 31239, -39516, 20843, 58375]], ![![-1225875, -15636, 89428, -49509, -116823]], ![![-905305, 2867, 63901, -35971, -79571]], ![![29903, 8800, -3427, 1549, 6754]], ![![-654723, -4461, 47185, -26283, -60586]]]
  g := ![![![-1279845, -8434367, -4643678, 1887463, 21339371], ![7374058, 48596314, 26755484, -10874901, -122951115], ![-42487422, -279998093, -154157517, 62658795, 708409191], ![27866249, 183644166, 101108225, -41095543, -464628990], ![-31890690, -210164786, -115709625, 47030946, 531727451]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P1 : CertificateIrreducibleZModOfList' 229 2 2 7 [196, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [193, 228], [0, 1]]
 g := ![![[103, 111], [103], [154, 56], [184], [168], [128, 193], [193, 1]], ![[0, 118], [103], [199, 173], [184], [168], [50, 36], [157, 228]]]
 h' := ![![[193, 228], [68, 180], [44, 65], [201, 133], [147, 111], [102, 175], [186, 184], [0, 1]], ![[0, 1], [0, 49], [223, 164], [222, 96], [44, 118], [214, 54], [203, 45], [193, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [195]]
 b := ![[], [152, 212]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N1 : CertifiedPrimeIdeal' SI229N1 229 where
  n := 2
  hpos := by decide
  P := [196, 36, 1]
  hirr := P229P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1026922, -645566, -118817, 420822, 432970]
  a := ![-1, 8, 10, -69, -97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-140690, -189594, -118817, 420822, 432970]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N1 B_one_repr
lemma NI229N1 : Nat.card (O ⧸ I229N1) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-131, -18, 12, -6, -20]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![-131, -18, 12, -6, -20]] 
 ![![229, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![129, 0, 1, 0, 0], ![135, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![-131, -18, 12, -6, -20], ![420, 43, -36, 18, 56], ![-1176, -66, 97, -54, -140], ![168, -8, -8, 1, 0], ![-162, 16, 10, -6, -5]]]
  hmulB := by decide  
  f := ![![![-7271, -4850, -956, 1242, 1532]], ![![-458, -305, -60, 78, 96]], ![![-4707, -3140, -619, 804, 992]], ![![-4965, -3310, -652, 847, 1044]], ![![-559, -374, -74, 96, 119]]]
  g := ![![![-1, -18, 12, -6, -20], ![4, 43, -36, 18, 56], ![-11, -66, 97, -54, -140], ![5, -8, -8, 1, 0], ![-3, 16, 10, -6, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![22040, 13265, 1838, -2821, -2731]] ![![77776674, 19355591, -4643678, 1887463, 21339371]]
  ![![-7271, -4850, -956, 1242, 1532]] where
 M := ![![![-7271, -4850, -956, 1242, 1532]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![-7271, -4850, -956, 1242, 1532]] ![![-131, -18, 12, -6, -20]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![229, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1, I229N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
    exact isPrimeI229N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0 ⊙ MulI229N1)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8693, 5785, 1137, -1474, -1814]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![8693, 5785, 1137, -1474, -1814]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![51, 13, 1, 0, 0], ![23, 101, 0, 1, 0], ![37, 160, 0, 0, 1]] where
  M :=![![![8693, 5785, 1137, -1474, -1814], ![38094, 25356, 4985, -6444, -7938], ![166698, 110995, 21830, -28086, -34650], ![183190, 122025, 24011, -30735, -37982], ![-46164, -30723, -6039, 7824, 9631]]]
  hmulB := by decide  
  f := ![![![-267, 355, 3, -16, 190]], ![![-3990, -1964, 365, -126, -1554]], ![![-141, 10, 10, -6, -6]], ![![-1849, -838, 165, -59, -678]], ![![-2679, -1268, 244, -86, -1011]]]
  g := ![![![222, 1846, 1137, -1474, -1814], ![969, 8075, 4985, -6444, -7938], ![4212, 35227, 21830, -28086, -34650], ![4596, 38589, 24011, -30735, -37982], ![-1178, -9800, -6039, 7824, 9631]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [136, 168, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [65, 232], [0, 1]]
 g := ![![[152, 2], [52], [128], [221, 30], [33], [6, 74], [65, 1]], ![[49, 231], [52], [128], [74, 203], [33], [156, 159], [130, 232]]]
 h' := ![![[65, 232], [115, 148], [68, 127], [1, 214], [114, 206], [116, 75], [14, 128], [0, 1]], ![[0, 1], [182, 85], [168, 106], [164, 19], [223, 27], [98, 158], [179, 105], [65, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [187, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [136, 168, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![227029, -75369, -78521, 169803, 346318]
  a := ![3, -3, 1, 39, 98]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-53595, -307363, -78521, 169803, 346318]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![621, -79, -33, 22, 20]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![621, -79, -33, 22, 20]] 
 ![![233, 0, 0, 0, 0], ![121, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![82, 0, 0, 1, 0], ![132, 0, 0, 0, 1]] where
  M :=![![![621, -79, -33, 22, 20], ![-420, 452, -35, 0, 168], ![-3528, -1897, 522, -210, -1176], ![2870, 567, -287, 137, 518], ![-2904, -585, 291, -138, -527]]]
  hmulB := by decide  
  f := ![![![13225, 3227, -819, 364, 3716]], ![![6533, 1591, -406, 182, 1840]], ![![4042, 987, -250, 112, 1136]], ![![3372, 805, -217, 107, 974]], ![![8928, 2187, -549, 240, 2497]]]
  g := ![![![30, -79, -33, 22, 20], ![-326, 452, -35, 0, 168], ![1625, -1897, 522, -210, -1176], ![-577, 567, -287, 137, 518], ![591, -585, 291, -138, -527]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41096, 19046, 1579, -3121, 1035]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![41096, 19046, 1579, -3121, 1035]] 
 ![![233, 0, 0, 0, 0], ![156, 1, 0, 0, 0], ![129, 0, 1, 0, 0], ![210, 0, 0, 1, 0], ![125, 0, 0, 0, 1]] where
  M :=![![![41096, 19046, 1579, -3121, 1035], ![-21735, 33323, 19009, -18615, -50939], ![1069719, 436322, 13920, -53481, 95963], ![17080, 191930, 84802, -87231, -213248], ![383748, 48644, -44338, 31194, 159697]]]
  hmulB := by decide  
  f := ![![![-2901816, -209972, 236895, -123907, -355977]], ![![-1910763, -139771, 156205, -81645, -235087]], ![![-1674825, -112324, 135459, -71190, -201434]], ![![-2617552, -192938, 214196, -111901, -322714]], ![![-1555134, -108916, 126439, -66271, -189134]]]
  g := ![![![-11192, 19046, 1579, -3121, 1035], ![11177, 33323, 19009, -18615, -50939], ![-298526, 436322, 13920, -53481, 95963], ![17644, 191930, 84802, -87231, -213248], ![-120163, 48644, -44338, 31194, 159697]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2

def I233N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7607, -5060, -994, 1296, 1592]] i)))

def SI233N3: IdealEqSpanCertificate' Table ![![-7607, -5060, -994, 1296, 1592]] 
 ![![233, 0, 0, 0, 0], ![176, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![196, 0, 0, 1, 0], ![103, 0, 0, 0, 1]] where
  M :=![![![-7607, -5060, -994, 1296, 1592], ![-33432, -22237, -4368, 5700, 7000], ![-147000, -97764, -19201, 25092, 30800], ![-162372, -107976, -21204, 27751, 34048], ![40422, 26888, 5282, -6888, -8461]]]
  hmulB := by decide  
  f := ![![![-2335, 2964, -274, 24, 1112]], ![![-1864, 2187, -192, 12, 808]], ![![541, 344, -91, 36, 200]], ![![-2240, 2456, -204, 7, 896]], ![![-755, 1348, -148, 24, 531]]]
  g := ![![![2051, -5060, -994, 1296, 1592], ![9008, -22237, -4368, 5700, 7000], ![39565, -97764, -19201, 25092, 30800], ![43652, -107976, -21204, 27751, 34048], ![-10897, 26888, 5282, -6888, -8461]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N3 : Nat.card (O ⧸ I233N3) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N3)

lemma isPrimeI233N3 : Ideal.IsPrime I233N3 := prime_ideal_of_norm_prime hp233.out _ NI233N3
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![8693, 5785, 1137, -1474, -1814]] ![![621, -79, -33, 22, 20]]
  ![![-5207, -3384, -666, 870, 1074]] where
 M := ![![![-5207, -3384, -666, 870, 1074]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![-5207, -3384, -666, 870, 1074]] ![![41096, 19046, 1579, -3121, 1035]]
  ![![-425863534, -283305250, -55660301, 72473939, 89065791]] where
 M := ![![![-425863534, -283305250, -55660301, 72473939, 89065791]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI233N2 : IdealMulLeCertificate' Table 
  ![![-425863534, -283305250, -55660301, 72473939, 89065791]] ![![-7607, -5060, -994, 1296, 1592]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![12725548248632, 8465656944198, 1663227229803, -2165648224975, -2661441749507]]]
 hmul := by decide  
 g := ![![![![54616086904, 36333291606, 7138314291, -9294627575, -11422496779]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1, I233N2, I233N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
    exact isPrimeI233N2
    exact isPrimeI233N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0 ⊙ MulI233N1 ⊙ MulI233N2)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![275147, 78905, -11711, 8400, 69968]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![275147, 78905, -11711, 8400, 69968]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![0, 0, 0, 239, 0], ![157, 206, 0, 206, 1]] where
  M :=![![![275147, 78905, -11711, 8400, 69968], ![-1469328, -351254, 93927, 5334, -372176], ![7815696, 1780995, -544442, 611568, 2679908], ![-7019334, -2193311, 210559, 577655, -868294], ![6268182, 1512617, -395545, 134304, 1734829]]]
  hmulB := by decide  
  f := ![![![1752025, 485337, -194363, 87990, 377744]], ![![-7932624, -1541298, 786073, -374268, -1412348]], ![![29659308, 4366703, -2739176, 1348026, 4646684]], ![![-7699062, -596265, 634125, -330173, -962234]], ![![-12289183, -1520954, 1093678, -547946, -1794383]]]
  g := ![![![-44811, -59977, -49, -60272, 69968], ![238336, 319318, 393, 320810, -372176], ![-1727740, -2302427, -2278, -2307320, 2679908], ![541016, 739227, 881, 750821, -868294], ![-1113389, -1488963, -1655, -1494730, 1734829]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 4 2 7 [184, 11, 228, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 120, 228, 191], [115, 22, 113, 213], [117, 96, 137, 74], [0, 1]]
 g := ![![[200, 141, 179, 87], [50, 40, 130, 71], [42, 233, 157, 166], [57, 87, 36, 80], [204, 157, 49], [205, 12, 238, 1], []], ![[64, 25, 181, 60, 235, 235], [51, 80, 71, 106, 66, 233], [46, 143, 95, 173, 207, 229], [223, 190, 238, 67, 161, 47], [41, 203, 30], [7, 103, 136, 128, 169, 141], [201, 24, 65, 226, 144, 65]], ![[126, 230, 201, 34, 122, 150], [172, 142, 10, 3, 181, 120], [200, 142, 198, 22, 198, 45], [189, 88, 163, 235, 50, 226], [195, 145, 8], [182, 150, 156, 47, 236, 31], [166, 107, 116, 16, 92, 110]], ![[166, 8, 233, 190, 81, 43], [101, 173, 22, 58, 184, 199], [231, 216, 25, 150, 221, 164], [104, 103, 73, 163, 67, 234], [190, 234, 169], [152, 115, 10, 136, 210, 159], [211, 133, 4, 179, 93, 119]]]
 h' := ![![[6, 120, 228, 191], [121, 163, 175, 39], [159, 231, 33, 166], [28, 204, 13, 40], [78, 37, 173, 115], [42, 78, 156, 232], [0, 0, 0, 1], [0, 1]], ![[115, 22, 113, 213], [35, 201, 30, 62], [151, 99, 177, 35], [100, 177, 145, 222], [237, 67, 76, 237], [206, 107, 116, 35], [38, 119, 156, 212], [6, 120, 228, 191]], ![[117, 96, 137, 74], [115, 206, 100, 105], [221, 204, 161, 132], [18, 219, 174, 230], [91, 213, 172, 70], [11, 38, 71, 198], [166, 18, 130, 41], [115, 22, 113, 213]], ![[0, 1], [28, 147, 173, 33], [27, 183, 107, 145], [10, 117, 146, 225], [206, 161, 57, 56], [64, 16, 135, 13], [207, 102, 192, 224], [117, 96, 137, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [63, 212, 66], []]
 b := ![[], [], [53, 94, 79, 168], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 4
  hpos := by decide
  P := [184, 11, 228, 1, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-496325625765630, -322714687003410, -62419023481813, 200105516939320, 214170433227196]
  a := ![1, -14, -10, 149, 303]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-142766040344918, -185949054107974, -261167462267, -183761521873904, 214170433227196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 3262808641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1752025, -485337, 194363, -87990, -377744]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-1752025, -485337, 194363, -87990, -377744]] 
 ![![239, 0, 0, 0, 0], ![230, 1, 0, 0, 0], ![158, 0, 1, 0, 0], ![89, 0, 0, 1, 0], ![96, 0, 0, 0, 1]] where
  M :=![![![-1752025, -485337, 194363, -87990, -377744], ![7932624, 1541298, -786073, 374268, 1412348], ![-29659308, -4366703, 2739176, -1348026, -4646684], ![7699062, 596265, -634125, 330173, 962234], ![-7944654, -632063, 656755, -341322, -1000547]]]
  hmulB := by decide  
  f := ![![![-275147, -78905, 11711, -8400, -69968]], ![![-258638, -74464, 10877, -8106, -65776]], ![![-214598, -59615, 10020, -8112, -57468]], ![![-73091, -20206, 3480, -5545, -22422]], ![![-136746, -38023, 6359, -3936, -35363]]]
  g := ![![![515735, -485337, 194363, -87990, -377744], ![-1637078, 1541298, -786073, 374268, 1412348], ![4635768, -4366703, 2739176, -1348026, -4646684], ![-631841, 596265, -634125, 330173, 962234], ![669844, -632063, 656755, -341322, -1000547]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![275147, 78905, -11711, 8400, 69968]] ![![-1752025, -485337, 194363, -87990, -377744]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0, 0, 0]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]] where
  M :=![![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 5 2 7 [165, 8, 149, 198, 68, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [159, 41, 11, 107, 32], [196, 9, 236, 189, 188], [49, 126, 195, 180, 55], [10, 64, 40, 6, 207], [0, 1]]
 g := ![![[56, 233, 23, 86, 214], [113, 224, 128, 123], [136, 240, 117, 116], [236, 139, 28, 237], [144, 133, 100, 9, 79], [88, 173, 1], []], ![[136, 118, 224, 21, 3, 153, 83, 201], [185, 39, 111, 80], [203, 224, 23, 150], [152, 102, 48, 9], [16, 153, 239, 182, 109, 168, 30, 40], [139, 158, 176, 108, 136, 4, 22, 45], [76, 30, 36, 111, 126, 129, 42, 233]], ![[27, 62, 81, 172, 211, 153, 67, 161], [215, 123, 235, 113], [5, 20, 40, 47], [50, 227, 144, 209], [11, 36, 175, 228, 180, 68, 81, 239], [35, 185, 232, 188, 61, 175, 125, 238], [106, 74, 214, 179, 28, 23, 124, 61]], ![[108, 30, 34, 195, 192, 183, 226, 206], [16, 239, 169, 231], [200, 229, 108, 64], [28, 15, 216, 232], [126, 228, 185, 100, 239, 129, 40, 220], [61, 41, 135, 114, 103, 178, 135, 68], [233, 194, 61, 230, 37, 214, 6, 85]], ![[175, 125, 86, 195, 69, 46, 24, 111], [61, 227, 10, 160], [7, 2, 50, 40], [19, 234, 65, 49], [34, 100, 12, 166, 24, 161, 24, 215], [236, 5, 113, 154, 188, 186, 201, 56], [85, 49, 21, 166, 4, 135, 64, 220]]]
 h' := ![![[159, 41, 11, 107, 32], [55, 31, 134, 12, 148], [216, 182, 101, 95, 169], [22, 173, 150, 8, 184], [99, 24, 219, 48, 128], [181, 153, 40, 171, 101], [0, 0, 0, 1], [0, 1]], ![[196, 9, 236, 189, 188], [163, 118, 202, 10, 163], [9, 58, 168, 117, 171], [138, 23, 201, 178, 135], [40, 18, 207, 110, 3], [101, 148, 184, 144, 69], [32, 166, 50, 29, 187], [159, 41, 11, 107, 32]], ![[49, 126, 195, 180, 55], [166, 97, 114, 156, 196], [148, 218, 141, 50, 178], [238, 130, 16, 3, 218], [52, 159, 165, 6, 152], [128, 215, 1, 49, 83], [76, 165, 20, 38, 36], [196, 9, 236, 189, 188]], ![[10, 64, 40, 6, 207], [156, 101, 46, 26, 150], [164, 21, 213, 60, 58], [151, 164, 73, 143, 233], [207, 167, 77, 127, 192], [53, 171, 148, 198, 239], [156, 79, 144, 156, 144], [49, 126, 195, 180, 55]], ![[0, 1], [57, 135, 227, 37, 66], [0, 3, 100, 160, 147], [51, 233, 42, 150, 194], [189, 114, 55, 191, 7], [107, 36, 109, 161, 231], [230, 72, 27, 17, 115], [10, 64, 40, 6, 207]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [162, 8, 80, 171], [], [], []]
 b := ![[], [35, 96, 105, 162, 198], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 5
  hpos := by decide
  P := [165, 8, 149, 198, 68, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-585555873461, -139701246984, 37743514172, -20629557102, -171290351386]
  a := ![4, 0, -1, -3, -14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2429692421, -579673224, 156612092, -85599822, -710748346]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 812990017201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def PBC241 : ContainsPrimesAboveP 241 ![I241N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![241, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 241 (by decide) 𝕀

instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-694, -840, 93, 63, -235]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![-694, -840, 93, 63, -235]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![17, 111, 97, 1, 0], ![125, 185, 220, 0, 1]] where
  M :=![![![-694, -840, 93, 63, -235], ![4935, 1265, -1089, 1125, 2527], ![-53067, -17844, 2318, 3591, -1939], ![-10080, -12658, -3754, 9089, 10416], ![-12582, -844, 1484, -1272, -2773]]]
  hmulB := by decide  
  f := ![![![612190, 407254, 80011, -104181, -128029]], ![![2688609, 1788621, 351413, -457563, -562331]], ![![11808951, 7855738, 1543358, -2009589, -2469565]], ![![5845972, 3888979, 764046, -994852, -1222581]], ![![12624037, 8398009, 1649906, -2148318, -2640075]]]
  g := ![![![110, 142, 182, 63, -235], ![-1315, -2355, -2654, 1125, 2527], ![511, -230, 321, 3591, -1939], ![-5843, -11747, -12657, 9089, 10416], ![1417, 2603, 2928, -1272, -2773]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [216, 112, 109, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 40, 212], [43, 210, 39], [0, 1]]
 g := ![![[10, 101, 181], [240, 220, 63], [175, 161], [169, 225, 60], [1, 222, 80], [61, 200, 84], [1]], ![[228, 78, 133, 134], [50, 170, 69, 76], [40, 52], [144, 192, 165, 133], [124, 82, 65, 151], [129, 45, 137, 215], [16, 130, 54, 168]], ![[9, 44, 103, 101], [195, 34, 19, 69], [48, 81], [115, 107, 211, 12], [130, 164, 217, 41], [114, 123, 119, 207], [129, 60, 152, 83]]]
 h' := ![![[99, 40, 212], [117, 236, 92], [185, 59, 126], [142, 212, 101], [35, 193, 78], [127, 138, 187], [35, 139, 142], [0, 1]], ![[43, 210, 39], [138, 66, 76], [2, 151, 63], [46, 6, 141], [66, 209, 68], [235, 124, 3], [242, 182, 52], [99, 40, 212]], ![[0, 1], [146, 200, 83], [142, 41, 62], [138, 33, 9], [175, 100, 105], [212, 240, 61], [188, 181, 57], [43, 210, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [140, 186], []]
 b := ![[], [85, 97, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [216, 112, 109, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21737553990, 13057837538, 2237423044, -7715887486, -7585854452]
  a := ![7, 13, 14, -107, -136]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4387009752, 9055396104, 9639707126, -7715887486, -7585854452]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![612190, 407254, 80011, -104181, -128029]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![612190, 407254, 80011, -104181, -128029]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![224, 169, 1, 0, 0], ![124, 186, 0, 1, 0], ![44, 166, 0, 0, 1]] where
  M :=![![![612190, 407254, 80011, -104181, -128029], ![2688609, 1788621, 351413, -457563, -562331], ![11808951, 7855738, 1543358, -2009589, -2469565], ![13027896, 8666894, 1702790, -2217149, -2724792], ![-3252348, -2163736, -425134, 553542, 680335]]]
  hmulB := by decide  
  f := ![![![-694, -840, 93, 63, -235]], ![![4935, 1265, -1089, 1125, 2527]], ![![2492, 31, -641, 828, 1484]], ![![3274, 472, -776, 901, 1798]], ![![3092, 686, -698, 750, 1619]]]
  g := ![![![4946, 109625, 80011, -104181, -128029], ![21723, 481488, 351413, -457563, -562331], ![95405, 2114580, 1543358, -2009589, -2469565], ![105260, 2333070, 1702790, -2217149, -2724792], ![-26280, -582512, -425134, 553542, 680335]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P1 : CertificateIrreducibleZModOfList' 251 2 2 7 [86, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [235, 250], [0, 1]]
 g := ![![[222, 108], [172, 60], [249], [179, 103], [201, 84], [169, 35], [235, 1]], ![[0, 143], [216, 191], [249], [37, 148], [112, 167], [111, 216], [219, 250]]]
 h' := ![![[235, 250], [17, 205], [33, 78], [168, 160], [33, 176], [24, 142], [121, 170], [0, 1]], ![[0, 1], [0, 46], [40, 173], [118, 91], [229, 75], [11, 109], [162, 81], [235, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [194]]
 b := ![[], [23, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N1 : CertifiedPrimeIdeal' SI251N1 251 where
  n := 2
  hpos := by decide
  P := [86, 16, 1]
  hirr := P251P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2020, -11067, -5658, 13473, 22872]
  a := ![1, -1, -1, 12, 27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5608, -21345, -5658, 13473, 22872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N1 B_one_repr
lemma NI251N1 : Nat.card (O ⧸ I251N1) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![-694, -840, 93, 63, -235]] ![![612190, 407254, 80011, -104181, -128029]]
  ![![251, 0, 0, 0, 0]] where
 M := ![![![251, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB3811I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB3811I5 : PrimesBelowBoundCertificateInterval O 197 251 3811 where
  m := 9
  g := ![3, 3, 3, 2, 3, 4, 2, 1, 2]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB3811I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0, I233N1, I233N2, I233N3]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
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
    · exact ![39601, 39601, 199]
    · exact ![9393931, 211, 211]
    · exact ![11089567, 223, 223]
    · exact ![11697083, 51529]
    · exact ![52441, 52441, 229]
    · exact ![54289, 233, 233, 233]
    · exact ![3262808641, 239]
    · exact ![812990017201]
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
      exact NI199N2
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
      exact NI211N2
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
      exact NI229N2
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
      exact NI233N2
      exact NI233N3
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
  β := ![I199N2, I211N1, I211N2, I223N1, I223N2, I229N2, I233N1, I233N2, I233N3, I239N1]
  Il := ![[I199N2], [I211N1, I211N2], [I223N1, I223N2], [], [I229N2], [I233N1, I233N2, I233N3], [I239N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
