
import IdealArithmetic.Examples.NF5_3_379687500_1.RI5_3_379687500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77243, -32226, 140470, -63002, -159512]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![77243, -32226, 140470, -63002, -159512]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![28, 41, 185, 1, 0], ![159, 189, 176, 0, 1]] where
  M :=![![![77243, -32226, 140470, -63002, -159512], ![-33508, 14241, -61720, 26508, 65620], ![12604, -7000, 28145, -4804, -2204], ![7404, 7800, -19208, -40299, -164300], ![-1414, -5314, 15142, 19726, 83705]]]
  hmulB := by decide  
  f := ![![![-181, -5450, -15602, 7126, 17504]], ![![3252, 6945, -1576, 516, 1724]], ![![692, 3768, 6769, -3148, -7636]], ![![992, 3217, 2929, -1411, -3324]], ![![2755, 4317, -6184, 2636, 6877]]]
  g := ![![![105851, 127232, 155136, -63002, -159512], ![-43616, -52431, -64260, 26508, 65620], ![1936, 2360, 5077, -4804, -2204], ![106068, 127287, 141451, -40299, -164300], ![-53941, -64725, -71464, 19726, 83705]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [152, 85, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 9, 156], [122, 247, 101], [0, 1]]
 g := ![![[23, 229, 118], [97, 21], [129, 253], [238, 158], [210, 120], [138, 62], [224, 1], []], ![[85, 13, 207, 10], [17, 57], [200, 100], [16, 72], [87, 223], [60, 136], [224, 100], [18, 178]], ![[167, 102, 105, 63], [195, 52], [158, 222], [42, 253], [118, 52], [50, 165], [36, 81], [73, 178]]]
 h' := ![![[102, 9, 156], [110, 48, 142], [132, 62, 110], [145, 12, 32], [37, 223, 71], [54, 153, 190], [133, 83, 233], [0, 0, 1], [0, 1]], ![[122, 247, 101], [70, 135, 157], [37, 194, 91], [25, 175, 10], [12, 188, 154], [227, 24, 123], [98, 247, 81], [215, 235, 247], [102, 9, 156]], ![[0, 1], [50, 74, 215], [69, 1, 56], [236, 70, 215], [127, 103, 32], [79, 80, 201], [45, 184, 200], [190, 22, 9], [122, 247, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84, 27], []]
 b := ![[], [89, 39, 242], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [152, 85, 33, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![69155379, -94786767, -180292851, -891834406, -1906177455]
  a := ![5, -3, -9, -44, -105]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1276742156, 1543727482, 1946678227, -891834406, -1906177455]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 16974593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-181, -5450, -15602, 7126, 17504]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![-181, -5450, -15602, 7126, 17504]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![220, 72, 1, 0, 0], ![94, 176, 0, 1, 0], ![89, 181, 0, 0, 1]] where
  M :=![![![-181, -5450, -15602, 7126, 17504], ![3252, 6945, -1576, 516, 1724], ![692, 3768, 6769, -3148, -7636], ![-1340, -2456, 1960, -931, -2404], ![394, 246, -2050, 942, 2353]]]
  hmulB := by decide  
  f := ![![![77243, -32226, 140470, -63002, -159512]], ![![-33508, 14241, -61720, 26508, 65620]], ![![56784, -23624, 103065, -46524, -118172]], ![![5334, -2004, 9036, -5047, -14044]], ![![3145, -1151, 5236, -3072, -8699]]]
  g := ![![![4687, -12858, -15602, 7126, 17504], ![576, -1099, -1576, 516, 1724], ![-1996, 5652, 6769, -3148, -7636], ![-510, 1772, 1960, -931, -2404], ![597, -1727, -2050, 942, 2353]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P1 : CertificateIrreducibleZModOfList' 257 2 2 8 [106, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [234, 256], [0, 1]]
 g := ![![[216, 62], [42], [34], [239], [64], [30], [15], [1]], ![[75, 195], [42], [34], [239], [64], [30], [15], [1]]]
 h' := ![![[234, 256], [152, 24], [135, 175], [107, 169], [189, 204], [169, 8], [137, 162], [151, 234], [0, 1]], ![[0, 1], [114, 233], [222, 82], [75, 88], [123, 53], [242, 249], [9, 95], [166, 23], [234, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115]]
 b := ![[], [83, 186]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N1 : CertifiedPrimeIdeal' SI257N1 257 where
  n := 2
  hpos := by decide
  P := [106, 23, 1]
  hirr := P257P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2350256, 3173188, 6070405, 30047229, 64380684]
  a := ![59, -60, -118, -533, -1236]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-38490894, -67607440, 6070405, 30047229, 64380684]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N1 B_one_repr
lemma NI257N1 : Nat.card (O ⧸ I257N1) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![77243, -32226, 140470, -63002, -159512]] ![![-181, -5450, -15602, 7126, 17504]]
  ![![257, 0, 0, 0, 0]] where
 M := ![![![257, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0)
instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-213, -333, 497, -240, -604]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![-213, -333, 497, -240, -604]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![218, 16, 140, 1, 0], ![212, 127, 72, 0, 1]] where
  M :=![![![-213, -333, 497, -240, -604], ![-124, -453, -449, 41, 188], ![106, -83, -518, -880, -1474], ![286, -774, -1249, -6634, -11902], ![-98, 163, 368, 1721, 3073]]]
  hmulB := by decide  
  f := ![![![293, -130, 557, -215, -500]], ![![-70, 78, -275, -98, -530]], ![![-334, -168, 314, 1239, 4894]], ![![70, -189, 607, 445, 2040]], ![![106, -115, 405, 135, 745]]]
  g := ![![![685, 305, 295, -240, -604], ![-186, -95, -75, 41, 188], ![1918, 765, 870, -880, -1474], ![15094, 6148, 6785, -6634, -11902], ![-3904, -1588, -1756, 1721, 3073]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [184, 169, 218, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 6, 98], [174, 256, 165], [0, 1]]
 g := ![![[25, 10, 78], [137, 139, 248], [132, 241, 48], [243, 105], [168, 183], [5, 225], [45, 1], []], ![[128, 110, 39, 234], [86, 127, 89, 108], [170, 145, 137, 151], [152, 11], [138, 243], [2, 162], [32, 49], [195, 136]], ![[262, 75, 209, 220], [57, 239], [25, 110, 134, 73], [208, 198], [209, 243], [195, 143], [58, 36], [128, 136]]]
 h' := ![![[134, 6, 98], [40, 237, 128], [171, 186, 145], [6, 9, 171], [43, 109, 47], [218, 218, 151], [136, 101, 15], [0, 0, 1], [0, 1]], ![[174, 256, 165], [115, 24, 238], [96, 46, 118], [158, 89, 211], [145, 153, 96], [246, 230, 56], [183, 60, 62], [223, 174, 256], [134, 6, 98]], ![[0, 1], [123, 2, 160], [225, 31], [225, 165, 144], [238, 1, 120], [159, 78, 56], [220, 102, 186], [149, 89, 6], [174, 256, 165]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [149, 113], []]
 b := ![[], [80, 229, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [184, 169, 218, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28950914, -61874412, -101991952, -496222944, -986830070]
  a := ![4, -3, -7, -36, -83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1206895542, 506483314, 533920096, -496222944, -986830070]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 18191447 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-293, 130, -557, 215, 500]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![-293, 130, -557, 215, 500]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![82, 123, 1, 0, 0], ![171, 207, 0, 1, 0], ![53, 63, 0, 0, 1]] where
  M :=![![![-293, 130, -557, 215, 500], ![70, -78, 275, 98, 530], ![334, 168, -314, -1239, -4894], ![-2416, -905, 1345, 7987, 31160], ![1300, 495, -748, -4323, -16877]]]
  hmulB := by decide  
  f := ![![![213, 333, -497, 240, 604]], ![![124, 453, 449, -41, -188]], ![![124, 316, 57, 59, 106]], ![![235, 576, 35, 149, 290]], ![![73, 175, 6, 32, 65]]]
  g := ![![![-68, -28, -557, 215, 500], ![-256, -333, 275, 98, 530], ![1891, 2295, -314, -1239, -4894], ![-11901, -14383, 1345, 7987, 31160], ![6450, 7797, -748, -4323, -16877]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P1 : CertificateIrreducibleZModOfList' 263 2 2 8 [246, 114, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [149, 262], [0, 1]]
 g := ![![[148, 24], [242, 61], [206, 166], [143], [208], [16], [109], [1]], ![[42, 239], [126, 202], [218, 97], [143], [208], [16], [109], [1]]]
 h' := ![![[149, 262], [169, 63], [83, 18], [193, 70], [225, 186], [138, 58], [38, 4], [17, 149], [0, 1]], ![[0, 1], [88, 200], [135, 245], [103, 193], [61, 77], [101, 205], [108, 259], [126, 114], [149, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [208]]
 b := ![[], [142, 104]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N1 : CertifiedPrimeIdeal' SI263N1 263 where
  n := 2
  hpos := by decide
  P := [246, 114, 1]
  hirr := P263P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-495540, 517068, 1098160, 5490303, 12276309]
  a := ![-26, 23, 50, 230, 547]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6387950, -7773600, 1098160, 5490303, 12276309]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N1 B_one_repr
lemma NI263N1 : Nat.card (O ⧸ I263N1) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![-213, -333, 497, -240, -604]] ![![-293, 130, -557, 215, 500]]
  ![![263, 0, 0, 0, 0]] where
 M := ![![![-263, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![379, -309, -3640, 1631, 4056]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![379, -309, -3640, 1631, 4056]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![0, 0, 0, 269, 0], ![223, 139, 6, 257, 1]] where
  M :=![![![379, -309, -3640, 1631, 4056], ![794, 2010, 528, -249, -450], ![48, 545, 1713, -1005, -2808], ![-798, -957, 338, 1476, 5526], ![380, 302, -494, -626, -2593]]]
  hmulB := by decide  
  f := ![![![-17817, 7423, -32370, 14565, 36936]], ![![7806, -3252, 14182, -6381, -16182]], ![![-3420, 1425, -6213, 2797, 7092]], ![![1498, -623, 2724, -1216, -3090]], ![![-9387, 3912, -17052, 7682, 19475]]]
  g := ![![![-3361, -2097, -104, -3869, 4056], ![376, 240, 12, 429, -450], ![2328, 1453, 69, 2679, -2808], ![-4584, -2859, -122, -5274, 5526], ![2151, 1341, 56, 2475, -2593]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 4 2 8 [263, 50, 47, 232, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [153, 42, 195, 217], [250, 67, 162, 250], [172, 159, 181, 71], [0, 1]]
 g := ![![[160, 204, 15, 54], [229, 164, 177], [45, 109, 48, 67], [14, 245, 188, 16], [91, 236, 13], [5, 100, 24], [1], []], ![[99, 28, 66, 114, 190, 133], [91, 125, 264], [193, 161, 86, 171, 177, 231], [209, 173, 74, 258, 113, 51], [23, 191, 4], [15, 160, 115], [232, 190, 245], [129, 144, 14]], ![[71, 115, 268, 209, 9, 221], [141, 202, 249], [9, 38, 102, 33, 230, 71], [183, 241, 196, 48, 12, 210], [167, 50, 214], [102, 92, 73], [149, 105, 264], [133, 207, 92]], ![[239, 93, 151, 205, 223, 94], [266, 32, 226], [189, 263, 203, 249, 162, 59], [264, 209, 13, 164, 175, 2], [32, 191, 151], [198, 244, 126], [23, 190, 149], [249, 247, 199]]]
 h' := ![![[153, 42, 195, 217], [30, 185, 156, 79], [1, 80, 45, 213], [84, 66, 256, 228], [60, 181, 185, 265], [66, 19, 73, 236], [6, 219, 222, 37], [0, 0, 1], [0, 1]], ![[250, 67, 162, 250], [81, 231, 38, 154], [72, 127, 182, 159], [217, 75, 41, 73], [225, 77, 68, 166], [244, 262, 78, 2], [238, 138, 207, 148], [242, 3, 104, 194], [153, 42, 195, 217]], ![[172, 159, 181, 71], [96, 248, 29, 160], [47, 225, 199, 220], [222, 93, 194, 48], [158, 87, 137, 119], [129, 214, 221, 138], [251, 62, 218, 197], [83, 116, 38, 110], [250, 67, 162, 250]], ![[0, 1], [36, 143, 46, 145], [79, 106, 112, 215], [118, 35, 47, 189], [162, 193, 148, 257], [117, 43, 166, 162], [143, 119, 160, 156], [143, 150, 126, 234], [172, 159, 181, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [124, 182, 196], []]
 b := ![[], [], [159, 0, 154, 251], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 4
  hpos := by decide
  P := [263, 50, 47, 232, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7714685891923, 4408260486368, 12746259109764, 65353478875552, 160181932431456]
  a := ![11, -6, -16, -92, -232]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-132818905643519, -82754202035264, -3525447343788, -152793320282560, 160181932431456]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 5236114321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17817, -7423, 32370, -14565, -36936]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![17817, -7423, 32370, -14565, -36936]] 
 ![![269, 0, 0, 0, 0], ![252, 1, 0, 0, 0], ![249, 0, 1, 0, 0], ![198, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![17817, -7423, 32370, -14565, -36936], ![-7806, 3252, -14182, 6381, 16182], ![3420, -1425, 6213, -2797, -7092], ![-1498, 623, -2724, 1216, 3090], ![1412, -588, 2566, -1152, -2923]]]
  hmulB := by decide  
  f := ![![![-379, 309, 3640, -1631, -4056]], ![![-358, 282, 3408, -1527, -3798]], ![![-351, 284, 3363, -1506, -3744]], ![![-276, 231, 2678, -1206, -3006]], ![![-31, 23, 286, -125, -307]]]
  g := ![![![-9339, -7423, 32370, -14565, -36936], ![4092, 3252, -14182, 6381, 16182], ![-1791, -1425, 6213, -2797, -7092], ![796, 623, -2724, 1216, 3090], ![-743, -588, 2566, -1152, -2923]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![379, -309, -3640, 1631, 4056]] ![![17817, -7423, 32370, -14565, -36936]]
  ![![269, 0, 0, 0, 0]] where
 M := ![![![-269, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4293, -1741, 7894, -3167, -8294]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![4293, -1741, 7894, -3167, -8294]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![39, 192, 1, 0, 0], ![100, 31, 0, 1, 0], ![186, 28, 0, 0, 1]] where
  M :=![![![4293, -1741, 7894, -3167, -8294], ![-1960, 1126, -2948, 3819, 7984], ![346, 1859, 4599, 14071, 24670], ![-3472, 14417, 19402, 95786, 171592], ![1156, -3880, -4636, -25298, -45469]]]
  hmulB := by decide  
  f := ![![![739, 1789, 576, -487, -1346]], ![![-372, 252, 1674, 373, 2428]], ![![-151, 436, 1265, 170, 1432]], ![![184, 671, 426, 15, 372]], ![![494, 1264, 556, -378, -993]]]
  g := ![![![5741, -4380, 7894, -3167, -8294], ![-6472, 831, -2948, 3819, 7984], ![-22785, -7410, 4599, 14071, 24670], ![-155922, -42379, 19402, 95786, 171592], ![41214, 10862, -4636, -25298, -45469]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [185, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [256, 270], [0, 1]]
 g := ![![[66, 167], [140, 138], [219, 148], [], [], [49], [225], [1]], ![[0, 104], [238, 133], [167, 123], [], [], [49], [225], [1]]]
 h' := ![![[256, 270], [116, 80], [135, 229], [0, 31], [64], [263], [188, 7], [86, 256], [0, 1]], ![[0, 1], [0, 191], [223, 42], [77, 240], [64], [263], [83, 264], [40, 15], [256, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [150, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 2
  hpos := by decide
  P := [185, 15, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33443, -11442, 18972, 115000, 437388]
  a := ![-4, 2, 8, 24, 84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-345489, -71830, 18972, 115000, 437388]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 8, -87, 39, 98]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![9, 8, -87, 39, 98]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![82, 119, 1, 0, 0], ![269, 13, 0, 1, 0], ![176, 1, 0, 0, 1]] where
  M :=![![![9, 8, -87, 39, 98], ![20, 48, 27, -12, -28], ![-4, 8, 40, -9, -28], ![-10, -13, 9, 55, 98], ![4, 5, -10, -11, -17]]]
  hmulB := by decide  
  f := ![![![-29, 13, -55, 34, 98]], ![![30, 5, 17, -65, -238]], ![![4, 6, -9, -17, -70]], ![![-25, 14, -55, 23, 56]], ![![-20, 8, -35, 26, 79]]]
  g := ![![![-76, 36, -87, 39, 98], ![22, -11, 27, -12, -28], ![15, -17, 40, -9, -28], ![-121, -7, 9, 55, 98], ![25, 5, -10, -11, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P1 : CertificateIrreducibleZModOfList' 271 2 2 8 [167, 229, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 270], [0, 1]]
 g := ![![[89, 185], [131, 219], [214, 167], [132, 106], [198], [106], [138], [1]], ![[0, 86], [115, 52], [182, 104], [248, 165], [198], [106], [138], [1]]]
 h' := ![![[42, 270], [74, 166], [34, 46], [178, 191], [202, 102], [54, 210], [236, 169], [104, 42], [0, 1]], ![[0, 1], [0, 105], [69, 225], [70, 80], [150, 169], [202, 61], [17, 102], [242, 229], [42, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [139, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N1 : CertifiedPrimeIdeal' SI271N1 271 where
  n := 2
  hpos := by decide
  P := [167, 229, 1]
  hirr := P271P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17367, 20119, 40956, 198885, 442072]
  a := ![-4, 8, 13, 41, 97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-496976, -29082, 40956, 198885, 442072]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N1 B_one_repr
lemma NI271N1 : Nat.card (O ⧸ I271N1) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N1

def I271N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![147279, -61359, 267576, -120395, -305316]] i)))

def SI271N2: IdealEqSpanCertificate' Table ![![147279, -61359, 267576, -120395, -305316]] 
 ![![271, 0, 0, 0, 0], ![231, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![227, 0, 0, 1, 0], ![104, 0, 0, 0, 1]] where
  M :=![![![147279, -61359, 267576, -120395, -305316], ![-64526, 26884, -117228, 52757, 133782], ![28268, -11769, 51373, -23051, -58500], ![-12398, 5217, -22422, 10506, 26358], ![11676, -4878, 21186, -9642, -24377]]]
  hmulB := by decide  
  f := ![![![-1191, -9141, -19734, 8989, 21828]], ![![-1001, -7763, -16836, 7670, 18630]], ![![-106, -855, -1865, 837, 2016]], ![![-1025, -7674, -16506, 7595, 18546]], ![![-444, -3504, -7590, 3416, 8239]]]
  g := ![![![245191, -61359, 267576, -120395, -305316], ![-107439, 26884, -117228, 52757, 133782], ![46966, -11769, 51373, -23051, -58500], ![-21257, 5217, -22422, 10506, 26358], ![19600, -4878, 21186, -9642, -24377]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N2 : Nat.card (O ⧸ I271N2) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N2)

lemma isPrimeI271N2 : Ideal.IsPrime I271N2 := prime_ideal_of_norm_prime hp271.out _ NI271N2
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![4293, -1741, 7894, -3167, -8294]] ![![9, 8, -87, 39, 98]]
  ![![-29265, 13629, -50301, 34322, 79062]] where
 M := ![![![-29265, 13629, -50301, 34322, 79062]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI271N1 : IdealMulLeCertificate' Table 
  ![![-29265, 13629, -50301, 34322, 79062]] ![![147279, -61359, 267576, -120395, -305316]]
  ![![271, 0, 0, 0, 0]] where
 M := ![![![-6113849701, 2547459078, -11106985677, 5000144307, 12678361020]]]
 hmul := by decide  
 g := ![![![![-22560331, 9400218, -40985187, 18450717, 46783620]]]]
 hle2 := by decide  


def PBC271 : ContainsPrimesAboveP 271 ![I271N0, I271N1, I271N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
    exact isPrimeI271N1
    exact isPrimeI271N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 271 (by decide) (𝕀 ⊙ MulI271N0 ⊙ MulI271N1)
instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3365, -9739, -6247, 3056, 7048]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![-3365, -9739, -6247, 3056, 7048]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![41, 241, 135, 1, 0], ![89, 250, 124, 0, 1]] where
  M :=![![![-3365, -9739, -6247, 3056, 7048], ![936, -309, -7619, 3417, 8536], ![1702, 4353, 1406, -746, -1598], ![-106, 956, 3713, -1688, -4166], ![-280, -1197, -1718, 801, 1931]]]
  hmulB := by decide  
  f := ![![![47, -18, 79, -47, -128]], ![![-34, 0, -31, 48, 202]], ![![106, 14, -58, -427, -1418]], ![![27, 3, -43, -169, -512]], ![![33, 1, -29, -166, -507]]]
  g := ![![![-2729, -9055, -4667, 3056, 7048], ![-3245, -10678, -5514, 3417, 8536], ![630, 2107, 1084, -746, -1598], ![1588, 5232, 2701, -1688, -4166], ![-740, -2444, -1261, 801, 1931]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 3 2 8 [252, 220, 201, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [231, 16, 176], [122, 260, 101], [0, 1]]
 g := ![![[253, 32, 62], [43, 218], [149, 184, 49], [131, 112], [187, 109, 10], [159, 256], [76, 1], []], ![[2, 65, 71, 166], [93, 160], [14, 108, 73, 72], [203, 213], [81, 253, 230, 266], [77, 229], [118, 12], [45, 229]], ![[236, 154, 161, 114], [156, 268], [112, 196, 98, 199], [239, 87], [193, 35, 175, 251], [142, 116], [166, 256], [120, 229]]]
 h' := ![![[231, 16, 176], [108, 186, 184], [124, 75, 213], [276, 55, 270], [243, 85, 200], [233, 261, 29], [238, 202, 16], [0, 0, 1], [0, 1]], ![[122, 260, 101], [102, 185, 246], [47, 15, 161], [266, 244, 104], [231, 181, 203], [224, 242, 15], [144, 135, 101], [194, 170, 260], [231, 16, 176]], ![[0, 1], [259, 183, 124], [121, 187, 180], [77, 255, 180], [263, 11, 151], [35, 51, 233], [232, 217, 160], [156, 107, 16], [122, 260, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [238, 34], []]
 b := ![[], [250, 9, 217], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 3
  hpos := by decide
  P := [252, 220, 201, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3967310, -14677869, -21381642, -102315757, -187967846]
  a := ![2, -3, -4, -20, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![75552533, 258611484, 133932341, -102315757, -187967846]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 21253933 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, 18, -70, 0, -40]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![-27, 18, -70, 0, -40]] 
 ![![277, 0, 0, 0, 0], ![188, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![273, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-27, 18, -70, 0, -40], ![-40, -27, 58, 170, 680], ![340, 130, -197, -1132, -4420], ![-2156, -792, 1154, 7079, 27596], ![1168, 430, -628, -3838, -14963]]]
  hmulB := by decide  
  f := ![![![409, 1690, 2254, -964, -2368]], ![![276, 1145, 1534, -654, -1608]], ![![164, 682, 911, -376, -932]], ![![401, 1678, 2236, -869, -2188]], ![![11, 40, 54, -46, -99]]]
  g := ![![![17, 18, -70, 0, -40], ![-190, -27, 58, 170, 680], ![1220, 130, -197, -1132, -4420], ![-7611, -792, 1154, 7079, 27596], ![4127, 430, -628, -3838, -14963]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1

def I277N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 51, 91, -42, -102]] i)))

def SI277N2: IdealEqSpanCertificate' Table ![![3, 51, 91, -42, -102]] 
 ![![277, 0, 0, 0, 0], ![231, 1, 0, 0, 0], ![100, 0, 1, 0, 0], ![168, 0, 0, 1, 0], ![255, 0, 0, 0, 1]] where
  M :=![![![3, 51, 91, -42, -102], ![-18, -39, 27, -11, -30], ![-8, -29, -42, 20, 48], ![8, 12, -17, 10, 24], ![-2, 1, 14, -7, -17]]]
  hmulB := by decide  
  f := ![![![7, 22, -75, -103, -438]], ![![5, 18, -62, -83, -354]], ![![8, 10, -30, -55, -228]], ![![-30, 1, -27, 51, 174]], ![![25, 27, -79, -156, -641]]]
  g := ![![![44, 51, 91, -42, -102], ![57, -39, 27, -11, -30], ![-17, -29, -42, 20, 48], ![-32, 12, -17, 10, 24], ![14, 1, 14, -7, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N2 : Nat.card (O ⧸ I277N2) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N2)

lemma isPrimeI277N2 : Ideal.IsPrime I277N2 := prime_ideal_of_norm_prime hp277.out _ NI277N2
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![-3365, -9739, -6247, 3056, 7048]] ![![-27, 18, -70, 0, -40]]
  ![![-237, 561, 1827, -826, -2028]] where
 M := ![![![-237, 561, 1827, -826, -2028]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI277N1 : IdealMulLeCertificate' Table 
  ![![-237, 561, 1827, -826, -2028]] ![![3, 51, 91, -42, -102]]
  ![![277, 0, 0, 0, 0]] where
 M := ![![![-27977, -98889, -97504, 46259, 109692]]]
 hmul := by decide  
 g := ![![![![-101, -357, -352, 167, 396]]]]
 hle2 := by decide  


def PBC277 : ContainsPrimesAboveP 277 ![I277N0, I277N1, I277N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
    exact isPrimeI277N1
    exact isPrimeI277N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 277 (by decide) (𝕀 ⊙ MulI277N0 ⊙ MulI277N1)
instance hp281 : Fact (Nat.Prime 281) := {out := by norm_num}

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8359, 3477, -15164, 6863, 17436]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![-8359, 3477, -15164, 6863, 17436]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![255, 168, 251, 1, 0], ![206, 125, 55, 0, 1]] where
  M :=![![![-8359, 3477, -15164, 6863, 17436], ![3710, -1496, 6630, -3109, -8166], ![-1948, 601, -2657, 2773, 8244], ![2698, 825, 676, -4980, -23682], ![-1766, -230, -736, 3602, 14627]]]
  hmulB := by decide  
  f := ![![![-10487, -26891, -8842, 4677, 10044]], ![![690, -5810, -22904, 10403, 25686]], ![![4880, 11093, -287, -169, 264]], ![![-4743, -17951, -21937, 10296, 24666]], ![![-6430, -20141, -16741, 8030, 18857]]]
  g := ![![![-19040, -11847, -9597, 6863, 17436], ![8821, 5486, 4399, -3109, -8166], ![-8567, -5323, -4100, 2773, 8244], ![21890, 13515, 9086, -4980, -23682], ![-13998, -8661, -6083, 3602, 14627]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 3 2 8 [128, 200, 175, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 29, 191], [102, 251, 90], [0, 1]]
 g := ![![[79, 12, 224], [103, 64], [102, 181], [177, 120, 246], [180, 124, 109], [255, 28], [106, 1], []], ![[208, 85, 218, 273], [277, 271], [160, 228], [169, 189, 28, 124], [65, 227, 219, 191], [35, 280], [216, 57], [264, 232]], ![[103, 192, 127, 232], [15, 98], [0, 34], [136, 221, 205, 228], [222, 241, 89, 123], [92, 14], [1, 279], [84, 232]]]
 h' := ![![[4, 29, 191], [185, 93, 96], [217, 119, 273], [105, 105, 249], [2, 41, 33], [174, 227, 59], [201, 28, 77], [0, 0, 1], [0, 1]], ![[102, 251, 90], [239, 48, 271], [17, 89, 208], [69, 275, 221], [4, 94, 97], [26, 257, 280], [216, 224, 228], [225, 69, 251], [4, 29, 191]], ![[0, 1], [148, 140, 195], [246, 73, 81], [33, 182, 92], [6, 146, 151], [267, 78, 223], [146, 29, 257], [214, 212, 29], [102, 251, 90]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [247, 181], []]
 b := ![[], [175, 22, 155], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 3
  hpos := by decide
  P := [128, 200, 175, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54900254, -9434030, 41958486, 239181030, 792724572]
  a := ![-3, 3, 13, 23, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-798389056, -495666970, -368655984, 239181030, 792724572]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 22188041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10487, -26891, -8842, 4677, 10044]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![-10487, -26891, -8842, 4677, 10044]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![130, 30, 1, 0, 0], ![34, 73, 0, 1, 0], ![139, 198, 0, 0, 1]] where
  M :=![![![-10487, -26891, -8842, 4677, 10044], ![690, -5810, -22904, 10403, 25686], ![4880, 11093, -287, -169, 264], ![602, 4711, 10322, -4744, -11586], ![-1158, -3940, -3984, 1888, 4483]]]
  hmulB := by decide  
  f := ![![![-8359, 3477, -15164, 6863, 17436]], ![![3710, -1496, 6630, -3109, -8166]], ![![-3478, 1451, -6317, 2853, 7224]], ![![-38, 35, -110, 5, -96]], ![![-1527, 665, -2832, 1217, 2923]]]
  g := ![![![-1481, -7444, -8842, 4677, 10044], ![-3366, -18377, -22904, 10403, 25686], ![40, -72, -287, -169, 264], ![1532, 8311, 10322, -4744, -11586], ![-607, -3238, -3984, 1888, 4483]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P1 : CertificateIrreducibleZModOfList' 281 2 2 8 [253, 138, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [143, 280], [0, 1]]
 g := ![![[256, 10], [141], [163], [141, 195], [96, 169], [119], [217], [1]], ![[0, 271], [141], [163], [207, 86], [97, 112], [119], [217], [1]]]
 h' := ![![[143, 280], [22, 216], [264, 66], [14, 43], [159, 40], [209, 13], [116, 261], [28, 143], [0, 1]], ![[0, 1], [0, 65], [148, 215], [262, 238], [259, 241], [101, 268], [66, 20], [245, 138], [143, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117]]
 b := ![[], [243, 199]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N1 : CertifiedPrimeIdeal' SI281N1 281 where
  n := 2
  hpos := by decide
  P := [253, 138, 1]
  hirr := P281P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-52733, 32560, 90032, 461203, 1119485]
  a := ![-8, 5, 12, 68, 169]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-651410, -918129, 90032, 461203, 1119485]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N1 B_one_repr
lemma NI281N1 : Nat.card (O ⧸ I281N1) = 78961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N1
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![-8359, 3477, -15164, 6863, 17436]] ![![-10487, -26891, -8842, 4677, 10044]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![281, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC281 : ContainsPrimesAboveP 281 ![I281N0, I281N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI281N0
    exact isPrimeI281N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 281 (by decide) (𝕀 ⊙ MulI281N0)
instance hp283 : Fact (Nat.Prime 283) := {out := by norm_num}

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![283, 0, 0, 0, 0]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![283, 0, 0, 0, 0]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![0, 0, 0, 283, 0], ![0, 0, 0, 0, 283]] where
  M :=![![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![0, 0, 0, 283, 0], ![0, 0, 0, 0, 283]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 5 2 8 [48, 34, 214, 91, 145, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [213, 118, 115, 81, 92], [26, 160, 36, 117, 186], [136, 201, 205, 195, 176], [46, 86, 210, 173, 112], [0, 1]]
 g := ![![[84, 190, 263, 210, 211], [251, 180, 275, 101, 207], [90, 160, 180, 251], [9, 173, 115, 237, 36], [79, 256, 16, 274, 215], [274, 275, 138, 1], [], []], ![[245, 92, 141, 79, 181, 172, 89, 4], [69, 121, 214, 72, 158, 165, 6, 116], [101, 125, 281, 136], [180, 251, 75, 228, 192, 151, 251, 1], [209, 48, 58, 13, 163, 101, 152, 57], [203, 78, 81, 207], [153, 209, 98, 96], [205, 103, 279, 257]], ![[135, 119, 78, 11, 59, 233, 267, 108], [84, 42, 92, 150, 190, 282, 151, 102], [67, 104, 188, 113], [65, 54, 101, 187, 101, 178, 32, 58], [21, 227, 246, 95, 100, 16, 267, 200], [99, 73, 14, 203], [72, 189, 197, 7], [21, 122, 263, 70]], ![[17, 62, 53, 112, 244, 76, 180, 116], [232, 39, 15, 246, 249, 21, 227, 246], [0, 147, 104, 106], [37, 161, 251, 21, 238, 26, 100, 157], [263, 158, 224, 33, 14, 32, 205, 100], [209, 271, 23, 41], [13, 187, 62, 23], [240, 225, 127, 129]], ![[101, 230, 119, 41, 253, 199, 113, 116], [144, 230, 7, 178, 144, 129, 256, 23], [86, 214, 179, 70], [84, 178, 277, 2, 269, 243, 280, 66], [230, 111, 16, 66, 28, 251, 120, 134], [97, 68, 116, 195], [43, 39, 18, 160], [5, 31, 225, 92]]]
 h' := ![![[213, 118, 115, 81, 92], [121, 246, 39, 10, 196], [52, 172, 151, 190, 115], [134, 197, 147, 186, 58], [170, 152, 103, 101, 6], [149, 124, 102, 55, 201], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[26, 160, 36, 117, 186], [216, 75, 76, 234, 96], [193, 139, 247, 9, 31], [71, 185, 277, 115, 226], [244, 275, 128, 53, 235], [227, 136, 216, 53, 279], [241, 94, 269, 153, 115], [154, 149, 169, 259, 215], [213, 118, 115, 81, 92]], ![[136, 201, 205, 195, 176], [79, 197, 264, 198, 136], [270, 156, 224, 221, 203], [72, 197, 23, 249, 135], [136, 230, 64, 122, 7], [45, 227, 33, 275, 162], [77, 81, 259, 110, 130], [234, 52, 263, 206, 220], [26, 160, 36, 117, 186]], ![[46, 86, 210, 173, 112], [172, 235, 125, 160, 26], [121, 130, 32, 196, 60], [11, 198, 140, 237, 244], [108, 60, 170, 129, 271], [81, 110, 274, 42, 63], [121, 266, 273, 243, 265], [184, 54, 208, 48, 227], [136, 201, 205, 195, 176]], ![[0, 1], [123, 96, 62, 247, 112], [269, 252, 195, 233, 157], [172, 72, 262, 62, 186], [76, 132, 101, 161, 47], [124, 252, 224, 141, 144], [188, 125, 48, 60, 55], [178, 28, 208, 53, 187], [46, 86, 210, 173, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [255, 194, 225, 129], [], [], []]
 b := ![[], [1, 206, 238, 0, 217], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 5
  hpos := by decide
  P := [48, 34, 214, 91, 145, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-464950840962570, 1088537152745954, 1751296842805916, 8494395960421150, 16655479487900386]
  a := ![-4, 4, 7, 37, 88]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1642935833790, 3846421034438, 6188328066452, 30015533429050, 58853284409542]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 1815232161643 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def PBC283 : ContainsPrimesAboveP 283 ![I283N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI283N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![283, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 283 (by decide) 𝕀

instance hp293 : Fact (Nat.Prime 293) := {out := by norm_num}

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15383, -6375, 27967, -12586, -31914]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![15383, -6375, 27967, -12586, -31914]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![0, 0, 0, 293, 0], ![172, 105, 286, 77, 1]] where
  M :=![![![15383, -6375, 27967, -12586, -31914], ![-6742, 2797, -12219, 5489, 13926], ![2948, -1253, 5338, -2462, -6204], ![-1280, 486, -2435, 708, 2064], ![1216, -491, 2240, -907, -2371]]]
  hmulB := by decide  
  f := ![![![-5, -14, -7, 3, 6]], ![![0, -2, -11, 8, 24]], ![![8, 8, -2, -19, -72]], ![![-34, -11, 23, 107, 426]], ![![-4, -4, -4, 14, 53]]]
  g := ![![![18787, 11415, 31247, 8344, -31914], ![-8198, -4981, -13635, -3641, 13926], ![3652, 2219, 6074, 1622, -6204], ![-1216, -738, -2023, -540, 2064], ![1396, 848, 2322, 620, -2371]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 4 2 8 [203, 238, 197, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [292, 207, 265, 60], [126, 171, 171, 235], [165, 207, 150, 291], [0, 1]]
 g := ![![[153, 219, 19, 59], [212, 264, 253], [49, 287, 136, 87], [151, 18, 46], [236, 120, 254], [283, 132, 276, 9], [1], []], ![[144, 186, 70, 162, 283, 21], [110, 36, 56], [120, 39, 107, 65, 110, 292], [240, 99, 56], [175, 273, 96], [188, 142, 281, 176, 238, 256], [247, 197, 37], [281, 197, 84]], ![[146, 247, 8, 261, 85, 152], [45, 29, 267], [47, 235, 108, 61, 123, 199], [23, 119, 216], [154, 49, 206], [84, 222, 14, 226, 11, 158], [226, 227, 212], [213, 251, 141]], ![[127, 212, 190, 218, 207, 72], [98, 124, 6], [118, 292, 249, 122, 202, 146], [50, 155, 260], [103, 27, 9], [21, 15, 205, 102, 172, 281], [53, 226, 244], [159, 267, 4]]]
 h' := ![![[292, 207, 265, 60], [260, 276, 34, 158], [15, 274, 148, 48], [113, 272, 123, 110], [292, 285, 261, 199], [272, 92, 20, 66], [90, 55, 96, 290], [0, 0, 1], [0, 1]], ![[126, 171, 171, 235], [198, 198, 99, 111], [92, 199, 228, 39], [63, 102, 262, 159], [261, 234, 98, 254], [115, 167, 88, 168], [114, 91, 256, 235], [93, 248, 83, 136], [292, 207, 265, 60]], ![[165, 207, 150, 291], [256, 104, 153, 75], [182, 0, 121, 248], [205, 97, 266, 171], [170, 246, 163, 41], [9, 112, 176, 56], [227, 39, 69, 19], [179, 45, 25, 70], [126, 171, 171, 235]], ![[0, 1], [34, 8, 7, 242], [2, 113, 89, 251], [81, 115, 228, 146], [165, 114, 64, 92], [177, 215, 9, 3], [142, 108, 165, 42], [222, 0, 184, 87], [165, 207, 150, 291]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [78, 198, 259], []]
 b := ![[], [], [72, 176, 98, 252], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 4
  hpos := by decide
  P := [203, 238, 197, 3, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4856860112426, 6988640552330, 13058422714180, 64470773867578, 136695199373614]
  a := ![-11, 10, -4, 98, 238]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-80260857175338, -48962482230980, -133384875761568, -35703275009900, 136695199373614]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 7370050801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 14, 7, -3, -6]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![5, 14, 7, -3, -6]] 
 ![![293, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![257, 0, 1, 0, 0], ![216, 0, 0, 1, 0], ![205, 0, 0, 0, 1]] where
  M :=![![![5, 14, 7, -3, -6], ![0, 2, 11, -8, -24], ![-8, -8, 2, 19, 72], ![34, 11, -23, -107, -426], ![-18, -5, 12, 59, 233]]]
  hmulB := by decide  
  f := ![![![-15383, 6375, -27967, 12586, 31914]], ![![-292, 121, -531, 239, 606]], ![![-13503, 5596, -24549, 11048, 28014]], ![![-11336, 4698, -20609, 9276, 23520]], ![![-10767, 4462, -19575, 8809, 22337]]]
  g := ![![![0, 14, 7, -3, -6], ![13, 2, 11, -8, -24], ![-66, -8, 2, 19, 72], ![397, 11, -23, -107, -426], ![-217, -5, 12, 59, 233]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N1 : Nat.card (O ⧸ I293N1) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N1)

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := prime_ideal_of_norm_prime hp293.out _ NI293N1
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![15383, -6375, 27967, -12586, -31914]] ![![5, 14, 7, -3, -6]]
  ![![293, 0, 0, 0, 0]] where
 M := ![![![-293, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![307, 0, 0, 0, 0]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![307, 0, 0, 0, 0]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![0, 0, 0, 307, 0], ![0, 0, 0, 0, 307]] where
  M :=![![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![0, 0, 0, 307, 0], ![0, 0, 0, 0, 307]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 5 2 8 [284, 215, 53, 277, 40, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [155, 118, 179, 20, 279], [116, 268, 128, 151, 58], [11, 63, 258, 178, 8], [292, 164, 49, 265, 269], [0, 1]]
 g := ![![[247, 0, 3, 195, 54], [181, 54, 27, 108, 58], [262, 297, 286, 46], [257, 305, 121, 176], [57, 198, 64, 212, 89], [264, 166, 95, 267, 1], [], []], ![[69, 5, 132, 46, 220, 148, 15, 43], [72, 46, 281, 1, 148, 32, 50, 136], [19, 178, 6, 260], [60, 57, 279, 39], [57, 181, 43, 252, 253, 165, 44, 8], [38, 194, 35, 277, 234, 100, 252, 241], [140, 221, 199, 49], [25, 57, 62, 170]], ![[75, 222, 74, 149, 201, 94, 145, 68], [193, 77, 76, 221, 279, 153, 132, 25], [125, 18, 279, 295], [70, 280, 250, 222], [92, 143, 280, 203, 28, 201, 156, 133], [14, 283, 230, 85, 209, 102, 218, 54], [150, 180, 211, 49], [1, 122, 230, 294]], ![[198, 273, 24, 144, 25, 154, 147, 34], [97, 126, 41, 306, 125, 25, 211, 218], [238, 281, 241, 179], [264, 279, 133, 171], [114, 283, 238, 197, 180, 123, 244, 84], [128, 95, 18, 290, 24, 239, 218, 95], [138, 275, 128, 145], [96, 117, 288, 64]], ![[18, 120, 247, 49, 126, 207, 299, 99], [46, 112, 1, 283, 173, 253, 88, 176], [269, 269, 77, 133], [287, 297, 66, 37], [194, 157, 287, 153, 29, 254, 126, 273], [217, 217, 97, 121, 206, 212, 290, 94], [175, 280, 73, 141], [281, 172, 78, 216]]]
 h' := ![![[155, 118, 179, 20, 279], [172, 0, 269, 167, 19], [126, 140, 228, 37, 66], [213, 25, 169, 217, 53], [83, 300, 130, 153, 207], [239, 169, 88, 188, 157], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[116, 268, 128, 151, 58], [256, 54, 142, 42, 270], [200, 207, 37, 257, 119], [101, 156, 268, 184, 80], [16, 108, 60, 267, 119], [62, 2, 297, 5, 181], [215, 226, 105, 123, 172], [40, 281, 158, 220, 7], [155, 118, 179, 20, 279]], ![[11, 63, 258, 178, 8], [65, 123, 232, 8, 139], [112, 248, 235, 247, 228], [0, 130, 85, 49, 70], [175, 139, 127, 65, 23], [173, 56, 59, 52, 272], [300, 100, 187, 303, 191], [278, 297, 93, 177, 7], [116, 268, 128, 151, 58]], ![[292, 164, 49, 265, 269], [98, 83, 149, 79, 298], [37, 121, 98, 203, 248], [157, 264, 93, 234, 250], [15, 244, 229, 66, 204], [101, 97, 130, 262, 85], [269, 168, 141, 275, 197], [180, 15, 148, 285, 256], [11, 63, 258, 178, 8]], ![[0, 1], [150, 47, 129, 11, 195], [9, 205, 16, 177, 260], [283, 39, 306, 237, 161], [236, 130, 68, 63, 61], [217, 290, 40, 107, 226], [92, 120, 181, 220, 53], [241, 21, 214, 239, 37], [292, 164, 49, 265, 269]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92, 85, 161, 296], [], [], []]
 b := ![[], [81, 14, 18, 90, 186], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 5
  hpos := by decide
  P := [284, 215, 53, 277, 40, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7265738120712, 17793571836888, 28302951437996, 137076657627618, 266936855437846]
  a := ![-2, 3, -1, 18, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-23666899416, 57959517384, 92192024228, 446503770774, 869501157778]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 2727042318307 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def PBC307 : ContainsPrimesAboveP 307 ![I307N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI307N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![307, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 307 (by decide) 𝕀



lemma PB953I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB953I6 : PrimesBelowBoundCertificateInterval O 251 307 953 where
  m := 9
  g := ![2, 2, 2, 3, 3, 2, 1, 2, 1]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB953I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1]
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1]
    · exact ![I271N0, I271N1, I271N2]
    · exact ![I277N0, I277N1, I277N2]
    · exact ![I281N0, I281N1]
    · exact ![I283N0]
    · exact ![I293N0, I293N1]
    · exact ![I307N0]
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
    · exact ![16974593, 66049]
    · exact ![18191447, 69169]
    · exact ![5236114321, 269]
    · exact ![73441, 73441, 271]
    · exact ![21253933, 277, 277]
    · exact ![22188041, 78961]
    · exact ![1815232161643]
    · exact ![7370050801, 293]
    · exact ![2727042318307]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
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
      exact NI271N2
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
      exact NI277N1
      exact NI277N2
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
      exact NI281N1
    · dsimp ; intro j
      fin_cases j
      exact NI283N0
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
  β := ![I269N1, I271N2, I277N1, I277N2, I293N1]
  Il := ![[], [], [I269N1], [I271N2], [I277N1, I277N2], [], [], [I293N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
