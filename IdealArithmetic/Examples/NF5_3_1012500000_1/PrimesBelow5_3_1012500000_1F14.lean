
import IdealArithmetic.Examples.NF5_3_1012500000_1.RI5_3_1012500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp709 : Fact (Nat.Prime 709) := {out := by norm_num}

def I709N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![371, 609, -228, 79, -81]] i)))

def SI709N0: IdealEqSpanCertificate' Table ![![371, 609, -228, 79, -81]] 
 ![![709, 0, 0, 0, 0], ![0, 709, 0, 0, 0], ![145, 626, 1, 0, 0], ![279, 690, 0, 1, 0], ![192, 689, 0, 0, 1]] where
  M :=![![![371, 609, -228, 79, -81], ![-486, -844, 170, -147, 79], ![474, 699, -503, 39, -147], ![-384, -638, 208, -101, 80], ![-198, -399, -112, -153, -8]]]
  hmulB := by decide  
  f := ![![![47603, 25387, -11250, 2053, -4035]], ![![-24210, -12922, 5724, -1029, 2053]], ![![-11623, -6208, 2749, -488, 986]], ![![-4839, -2591, 1146, -194, 411]], ![![-10644, -5687, 2518, -444, 903]]]
  g := ![![![38, 204, -228, 79, -81], ![1, -85, 170, -147, 79], ![128, 550, -503, 39, -147], ![-25, -164, 208, -101, 80], ![85, 255, -112, -153, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P709P0 : CertificateIrreducibleZModOfList' 709 2 2 9 [642, 413, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [296, 708], [0, 1]]
 g := ![![[15, 582], [560], [602, 214], [201], [245], [405], [35, 543], [494, 409], [1]], ![[0, 127], [560], [136, 495], [201], [245], [405], [529, 166], [319, 300], [1]]]
 h' := ![![[296, 708], [512, 439], [630, 279], [143, 445], [528, 169], [214, 260], [218, 233], [484, 157], [67, 296], [0, 1]], ![[0, 1], [0, 270], [261, 430], [698, 264], [213, 540], [602, 449], [413, 476], [162, 552], [476, 413], [296, 708]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [266]]
 b := ![[], [168, 133]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI709N0 : CertifiedPrimeIdeal' SI709N0 709 where
  n := 2
  hpos := by decide
  P := [642, 413, 1]
  hirr := P709P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1620, 1529, -3430, -4971, -617]
  a := ![0, -1, -4, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2827, 8468, -3430, -4971, -617]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI709N0 : Ideal.IsPrime I709N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI709N0 B_one_repr
lemma NI709N0 : Nat.card (O ⧸ I709N0) = 502681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI709N0

def I709N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53537, 28552, -12653, 2307, -4537]] i)))

def SI709N1: IdealEqSpanCertificate' Table ![![53537, 28552, -12653, 2307, -4537]] 
 ![![709, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![262, 0, 1, 0, 0], ![275, 0, 0, 1, 0], ![245, 0, 0, 0, 1]] where
  M :=![![![53537, 28552, -12653, 2307, -4537], ![-27222, -14518, 6434, -1173, 2307], ![13842, 7383, -3271, 597, -1173], ![-8094, -4317, 1913, -349, 686], ![-6324, -3372, 1495, -273, 536]]]
  hmulB := by decide  
  f := ![![![437, 746, -101, 297, -113]], ![![20, 34, -4, 15, -5]], ![![164, 281, -39, 105, -41]], ![![169, 289, -38, 116, -45]], ![![145, 244, -26, 126, -41]]]
  g := ![![![4055, 28552, -12653, 2307, -4537], ![-2062, -14518, 6434, -1173, 2307], ![1048, 7383, -3271, 597, -1173], ![-613, -4317, 1913, -349, 686], ![-479, -3372, 1495, -273, 536]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI709N1 : Nat.card (O ⧸ I709N1) = 709 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI709N1)

lemma isPrimeI709N1 : Ideal.IsPrime I709N1 := prime_ideal_of_norm_prime hp709.out _ NI709N1

def I709N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67, -26, 13, -3, 5]] i)))

def SI709N2: IdealEqSpanCertificate' Table ![![-67, -26, 13, -3, 5]] 
 ![![709, 0, 0, 0, 0], ![82, 1, 0, 0, 0], ![366, 0, 1, 0, 0], ![487, 0, 0, 1, 0], ![179, 0, 0, 0, 1]] where
  M :=![![![-67, -26, 13, -3, 5], ![30, 8, -4, -3, -3], ![-18, -15, 11, 39, -3], ![6, -3, -7, -19, 8], ![48, 102, -47, -147, 2]]]
  hmulB := by decide  
  f := ![![![-27607, -78676, -75887, -37425, -13127]], ![![-3304, -9416, -9082, -4479, -1571]], ![![-14568, -41517, -40045, -19749, -6927]], ![![-18955, -54019, -52104, -25696, -9013]], ![![-7241, -20636, -19904, -9816, -3443]]]
  g := ![![![-3, -26, 13, -3, 5], ![4, 8, -4, -3, -3], ![-30, -15, 11, 39, -3], ![15, -3, -7, -19, 8], ![113, 102, -47, -147, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI709N2 : Nat.card (O ⧸ I709N2) = 709 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI709N2)

lemma isPrimeI709N2 : Ideal.IsPrime I709N2 := prime_ideal_of_norm_prime hp709.out _ NI709N2

def I709N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 305, 294, 145, 51]] i)))

def SI709N3: IdealEqSpanCertificate' Table ![![107, 305, 294, 145, 51]] 
 ![![709, 0, 0, 0, 0], ![676, 1, 0, 0, 0], ![329, 0, 1, 0, 0], ![227, 0, 0, 1, 0], ![702, 0, 0, 0, 1]] where
  M :=![![![107, 305, 294, 145, 51], ![306, 872, 838, 411, 145], ![870, 2481, 2395, 1185, 411], ![-24, -68, -58, -23, -8], ![750, 2133, 2034, 981, 364]]]
  hmulB := by decide  
  f := ![![![-55261, -24013, 11648, -1421, 4125]], ![![-52654, -22886, 11100, -1355, 3931]], ![![-25655, -11138, 5405, -658, 1914]], ![![-17687, -7693, 3730, -456, 1321]], ![![-54708, -23775, 11532, -1407, 4084]]]
  g := ![![![-524, 305, 294, 145, 51], ![-1495, 872, 838, 411, 145], ![-4262, 2481, 2395, 1185, 411], ![107, -68, -58, -23, -8], ![-3651, 2133, 2034, 981, 364]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI709N3 : Nat.card (O ⧸ I709N3) = 709 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI709N3)

lemma isPrimeI709N3 : Ideal.IsPrime I709N3 := prime_ideal_of_norm_prime hp709.out _ NI709N3
def MulI709N0 : IdealMulLeCertificate' Table 
  ![![371, 609, -228, 79, -81]] ![![53537, 28552, -12653, 2307, -4537]]
  ![![871, 95, -137, -34, -42]] where
 M := ![![![871, 95, -137, -34, -42]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI709N1 : IdealMulLeCertificate' Table 
  ![![871, 95, -137, -34, -42]] ![![-67, -26, 13, -3, 5]]
  ![![-55261, -24013, 11648, -1421, 4125]] where
 M := ![![![-55261, -24013, 11648, -1421, 4125]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI709N2 : IdealMulLeCertificate' Table 
  ![![-55261, -24013, 11648, -1421, 4125]] ![![107, 305, 294, 145, 51]]
  ![![709, 0, 0, 0, 0]] where
 M := ![![![709, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC709 : ContainsPrimesAboveP 709 ![I709N0, I709N1, I709N2, I709N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI709N0
    exact isPrimeI709N1
    exact isPrimeI709N2
    exact isPrimeI709N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 709 (by decide) (𝕀 ⊙ MulI709N0 ⊙ MulI709N1 ⊙ MulI709N2)
instance hp719 : Fact (Nat.Prime 719) := {out := by norm_num}

def I719N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2041, 8119, 12007, 4938, 2290]] i)))

def SI719N0: IdealEqSpanCertificate' Table ![![2041, 8119, 12007, 4938, 2290]] 
 ![![719, 0, 0, 0, 0], ![0, 719, 0, 0, 0], ![0, 0, 719, 0, 0], ![280, 78, 555, 1, 0], ![264, 333, 211, 0, 1]] where
  M :=![![![2041, 8119, 12007, 4938, 2290], ![13740, 36391, 30042, 16008, 4938], ![29628, 87810, 90757, 43344, 16008], ![1194, 1053, -3261, -611, -780], ![28530, 80463, 75975, 37818, 13057]]]
  hmulB := by decide  
  f := ![![![-150013, -80003, 35455, -6462, 12712]], ![![76272, 40667, -18024, 3300, -6462]], ![![-38772, -20658, 9143, -1728, 3300]], ![![-80042, -42673, 18902, -3491, 6794]], ![![-31110, -16590, 7348, -1350, 2641]]]
  g := ![![![-2761, -1585, -4467, 4938, 2290], ![-8028, -3973, -13764, 16008, 4938], ![-22716, -11994, -38029, 43344, 16008], ![526, 429, 696, -611, -780], ![-19482, -10038, -32918, 37818, 13057]]]
  hle1 := by decide   
  hle2 := by decide  


def P719P0 : CertificateIrreducibleZModOfList' 719 3 2 9 [255, 68, 471, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 404, 206], [126, 314, 513], [0, 1]]
 g := ![![[586, 426, 673], [234, 567, 434], [312, 291, 8], [632, 503, 302], [216, 362], [54, 580], [645, 29, 501], [321, 248, 1], []], ![[315, 5, 447, 468], [204, 685, 306, 232], [309, 392, 428, 151], [580, 250, 175, 145], [383, 675], [302, 613], [540, 172, 660, 633], [668, 601, 675, 464], [484, 15]], ![[146, 192, 96, 228], [164, 398, 410, 247], [689, 648, 226, 285], [443, 660, 354, 89], [588, 630], [663, 189], [433, 361, 104, 221], [679, 233, 463, 101], [177, 15]]]
 h' := ![![[122, 404, 206], [7, 7, 229], [249, 237, 437], [615, 621, 71], [626, 341, 320], [669, 228, 346], [176, 611, 193], [111, 493, 655], [0, 0, 1], [0, 1]], ![[126, 314, 513], [509, 378, 10], [444, 149, 538], [349, 308, 668], [301, 597, 323], [358, 372, 308], [559, 473, 247], [625, 408, 215], [33, 5, 314], [122, 404, 206]], ![[0, 1], [220, 334, 480], [426, 333, 463], [292, 509, 699], [390, 500, 76], [543, 119, 65], [268, 354, 279], [695, 537, 568], [220, 714, 404], [126, 314, 513]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [203, 707], []]
 b := ![[], [389, 118, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI719N0 : CertifiedPrimeIdeal' SI719N0 719 where
  n := 3
  hpos := by decide
  P := [255, 68, 471, 1]
  hirr := P719P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-870429, -2286646, 1925974, 970716, -47414]
  a := ![3, -64, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-361827, -86528, -732708, 970716, -47414]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI719N0 : Ideal.IsPrime I719N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI719N0 B_one_repr
lemma NI719N0 : Nat.card (O ⧸ I719N0) = 371694959 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI719N0

def I719N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![150013, 80003, -35455, 6462, -12712]] i)))

def SI719N1: IdealEqSpanCertificate' Table ![![150013, 80003, -35455, 6462, -12712]] 
 ![![719, 0, 0, 0, 0], ![0, 719, 0, 0, 0], ![190, 268, 1, 0, 0], ![286, 150, 0, 1, 0], ![589, 349, 0, 0, 1]] where
  M :=![![![150013, 80003, -35455, 6462, -12712], ![-76272, -40667, 18024, -3300, 6462], ![38772, 20658, -9143, 1728, -3300], ![-22686, -12117, 5355, -971, 1938], ![-17658, -9309, 4089, -1026, 1543]]]
  hmulB := by decide  
  f := ![![![-2041, -8119, -12007, -4938, -2290]], ![![-13740, -36391, -30042, -16008, -4938]], ![![-5702, -15832, -14497, -7332, -2468]], ![![-3680, -10823, -11039, -5303, -1940]], ![![-8381, -24427, -24524, -11868, -4291]]]
  g := ![![![17421, 18149, -35455, 6462, -12712], ![-8850, -9223, 18024, -3300, 6462], ![4486, 4678, -9143, 1728, -3300], ![-2648, -2751, 5355, -971, 1938], ![-1961, -2072, 4089, -1026, 1543]]]
  hle1 := by decide   
  hle2 := by decide  


def P719P1 : CertificateIrreducibleZModOfList' 719 2 2 9 [386, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [669, 718], [0, 1]]
 g := ![![[436, 453], [460, 35], [203, 529], [72, 263], [166], [583], [323, 573], [599, 343], [1]], ![[75, 266], [148, 684], [356, 190], [583, 456], [166], [583], [433, 146], [705, 376], [1]]]
 h' := ![![[669, 718], [33, 328], [13, 85], [249, 696], [11, 601], [567, 413], [428, 326], [304, 309], [333, 669], [0, 1]], ![[0, 1], [170, 391], [77, 634], [680, 23], [159, 118], [49, 306], [665, 393], [672, 410], [676, 50], [669, 718]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [361]]
 b := ![[], [558, 540]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI719N1 : CertifiedPrimeIdeal' SI719N1 719 where
  n := 2
  hpos := by decide
  P := [386, 50, 1]
  hirr := P719P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![725, 430, -554, -1298, 350]
  a := ![1, -3, -2, -1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![377, 308, -554, -1298, 350]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI719N1 : Ideal.IsPrime I719N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI719N1 B_one_repr
lemma NI719N1 : Nat.card (O ⧸ I719N1) = 516961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI719N1
def MulI719N0 : IdealMulLeCertificate' Table 
  ![![2041, 8119, 12007, 4938, 2290]] ![![150013, 80003, -35455, 6462, -12712]]
  ![![719, 0, 0, 0, 0]] where
 M := ![![![-719, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC719 : ContainsPrimesAboveP 719 ![I719N0, I719N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI719N0
    exact isPrimeI719N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 719 (by decide) (𝕀 ⊙ MulI719N0)
instance hp727 : Fact (Nat.Prime 727) := {out := by norm_num}

def I727N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -888, 239, -153, 93]] i)))

def SI727N0: IdealEqSpanCertificate' Table ![![-17, -888, 239, -153, 93]] 
 ![![727, 0, 0, 0, 0], ![0, 727, 0, 0, 0], ![486, 535, 1, 0, 0], ![42, 576, 0, 1, 0], ![571, 212, 0, 0, 1]] where
  M :=![![![-17, -888, 239, -153, 93], ![558, 1378, -390, 219, -153], ![-918, -1737, 601, -243, 219], ![678, 1263, -395, 187, -150], ![216, 480, -93, 87, -44]]]
  hmulB := by decide  
  f := ![![![97, 222, -131, -369, 39]], ![![234, 682, 42, -381, -369]], ![![234, 643, -53, -516, -246]], ![![192, 555, 23, -329, -288]], ![![157, 404, -104, -444, -77]]]
  g := ![![![-224, -83, 239, -153, 93], ![369, 160, -390, 219, -153], ![-561, -316, 601, -243, 219], ![372, 188, -395, 187, -150], ![92, 13, -93, 87, -44]]]
  hle1 := by decide   
  hle2 := by decide  


def P727P0 : CertificateIrreducibleZModOfList' 727 2 2 9 [598, 721, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 726], [0, 1]]
 g := ![![[372, 665], [569, 511], [269, 561], [700], [131, 367], [535], [171, 348], [310, 36], [1]], ![[0, 62], [0, 216], [0, 166], [700], [152, 360], [535], [78, 379], [526, 691], [1]]]
 h' := ![![[6, 726], [701, 489], [532, 396], [575, 510], [178, 492], [156, 499], [249, 142], [5, 608], [129, 6], [0, 1]], ![[0, 1], [0, 238], [0, 331], [0, 217], [222, 235], [242, 228], [374, 585], [18, 119], [165, 721], [6, 726]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [511]]
 b := ![[], [324, 619]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI727N0 : CertifiedPrimeIdeal' SI727N0 727 where
  n := 2
  hpos := by decide
  P := [598, 721, 1]
  hirr := P727P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3942, 19789, -164, -9643, 6039]
  a := ![1, 19, 3, -1, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4071, 6027, -164, -9643, 6039]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI727N0 : Ideal.IsPrime I727N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI727N0 B_one_repr
lemma NI727N0 : Nat.card (O ⧸ I727N0) = 528529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI727N0

def I727N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![377, 607, 433, 246, 66]] i)))

def SI727N1: IdealEqSpanCertificate' Table ![![377, 607, 433, 246, 66]] 
 ![![727, 0, 0, 0, 0], ![120, 1, 0, 0, 0], ![140, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![56, 0, 0, 0, 1]] where
  M :=![![![377, 607, 433, 246, 66], ![396, 1367, 1396, 672, 246], ![1476, 4086, 3899, 1932, 672], ![-66, -117, -89, -49, -14], ![1194, 3459, 3353, 1650, 581]]]
  hmulB := by decide  
  f := ![![![155, 53, 157, 1230, -192]], ![![24, 5, 26, 204, -30]], ![![40, 34, 19, 204, -36]], ![![4, -5, 17, 83, -16]], ![![-26, -89, 51, 222, -13]]]
  g := ![![![-201, 607, 433, 246, 66], ![-548, 1367, 1396, 672, 246], ![-1576, 4086, 3899, 1932, 672], ![40, -117, -89, -49, -14], ![-1346, 3459, 3353, 1650, 581]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI727N1 : Nat.card (O ⧸ I727N1) = 727 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI727N1)

lemma isPrimeI727N1 : Ideal.IsPrime I727N1 := prime_ideal_of_norm_prime hp727.out _ NI727N1

def I727N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1079, 943, -350, 111, -129]] i)))

def SI727N2: IdealEqSpanCertificate' Table ![![1079, 943, -350, 111, -129]] 
 ![![727, 0, 0, 0, 0], ![212, 1, 0, 0, 0], ![130, 0, 1, 0, 0], ![673, 0, 0, 1, 0], ![511, 0, 0, 0, 1]] where
  M :=![![![1079, 943, -350, 111, -129], ![-774, -856, 298, -111, 111], ![666, 891, -295, 123, -111], ![-444, -612, 202, -85, 76], ![-210, -249, 86, -33, 32]]]
  hmulB := by decide  
  f := ![![![-43, -49, 256, 447, -177]], ![![-14, -18, 76, 135, -51]], ![![-4, -1, 39, 63, -27]], ![![-37, -37, 238, 410, -169]], ![![-49, -76, 212, 396, -139]]]
  g := ![![![-223, 943, -350, 111, -129], ![220, -856, 298, -111, 111], ![-242, 891, -295, 123, -111], ![167, -612, 202, -85, 76], ![65, -249, 86, -33, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI727N2 : Nat.card (O ⧸ I727N2) = 727 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI727N2)

lemma isPrimeI727N2 : Ideal.IsPrime I727N2 := prime_ideal_of_norm_prime hp727.out _ NI727N2

def I727N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 29, -6, 7, -3]] i)))

def SI727N3: IdealEqSpanCertificate' Table ![![17, 29, -6, 7, -3]] 
 ![![727, 0, 0, 0, 0], ![587, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![541, 0, 0, 1, 0], ![330, 0, 0, 0, 1]] where
  M :=![![![17, 29, -6, 7, -3], ![-18, -28, 16, -3, 7], ![42, 87, -5, -21, -3], ![-24, -44, 20, 25, -2], ![-42, -99, 54, 135, 16]]]
  hmulB := by decide  
  f := ![![![-1701181, -907231, 402056, -73301, 144165]], ![![-1372391, -731889, 324350, -59134, 116302]], ![![-68465, -36512, 16181, -2950, 5802]], ![![-1265587, -674931, 299108, -54532, 107251]], ![![-771924, -411663, 182436, -33261, 65416]]]
  g := ![![![-27, 29, -6, 7, -3], ![21, -28, 16, -3, 7], ![-53, 87, -5, -21, -3], ![17, -44, 20, 25, -2], ![-30, -99, 54, 135, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI727N3 : Nat.card (O ⧸ I727N3) = 727 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI727N3)

lemma isPrimeI727N3 : Ideal.IsPrime I727N3 := prime_ideal_of_norm_prime hp727.out _ NI727N3
def MulI727N0 : IdealMulLeCertificate' Table 
  ![![-17, -888, 239, -153, 93]] ![![377, 607, 433, 246, 66]]
  ![![115847, 91927, 10298, 21777, -2787]] where
 M := ![![![115847, 91927, 10298, 21777, -2787]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI727N1 : IdealMulLeCertificate' Table 
  ![![115847, 91927, 10298, 21777, -2787]] ![![1079, 943, -350, 111, -129]]
  ![![51622165, 27096166, -12030842, 2162700, -4317576]] where
 M := ![![![51622165, 27096166, -12030842, 2162700, -4317576]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI727N2 : IdealMulLeCertificate' Table 
  ![![51622165, 27096166, -12030842, 2162700, -4317576]] ![![17, 29, -6, 7, -3]]
  ![![727, 0, 0, 0, 0]] where
 M := ![![![13983845, 23948107, -5935228, 3909079, -2507423]]]
 hmul := by decide  
 g := ![![![![19235, 32941, -8164, 5377, -3449]]]]
 hle2 := by decide  


def PBC727 : ContainsPrimesAboveP 727 ![I727N0, I727N1, I727N2, I727N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI727N0
    exact isPrimeI727N1
    exact isPrimeI727N2
    exact isPrimeI727N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 727 (by decide) (𝕀 ⊙ MulI727N0 ⊙ MulI727N1 ⊙ MulI727N2)
instance hp733 : Fact (Nat.Prime 733) := {out := by norm_num}

def I733N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11228591, -5988740, 2653870, -483930, 951606]] i)))

def SI733N0: IdealEqSpanCertificate' Table ![![-11228591, -5988740, 2653870, -483930, 951606]] 
 ![![733, 0, 0, 0, 0], ![0, 733, 0, 0, 0], ![0, 0, 733, 0, 0], ![286, 322, 417, 1, 0], ![694, 442, 349, 0, 1]] where
  M :=![![![-11228591, -5988740, 2653870, -483930, 951606], ![5709636, 3045499, -1349624, 246102, -483930], ![-2903580, -1549314, 686245, -125310, 246102], ![1697892, 905982, -401402, 73249, -143936], ![1326480, 707484, -313690, 57126, -112457]]]
  hmulB := by decide  
  f := ![![![-659, -1588, 762, 2346, -78]], ![![-468, -1829, -1336, -1062, 2346]], ![![14076, 34722, -14159, -47058, -1062]], ![![7534, 18306, -8325, -26273, 386]], ![![5722, 13740, -6761, -20592, 853]]]
  g := ![![![-727475, -369404, -174158, -483930, 951606], ![369948, 187855, 88564, 246102, -483930], ![-188076, -95466, -44951, -125310, 246102], ![110014, 55852, 26313, 73249, -143936], ![85994, 43682, 20617, 57126, -112457]]]
  hle1 := by decide   
  hle2 := by decide  


def P733P0 : CertificateIrreducibleZModOfList' 733 3 2 9 [333, 445, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 696, 298], [620, 36, 435], [0, 1]]
 g := ![![[396, 645, 672], [335, 124], [380, 490, 507], [537, 419, 454], [720, 328, 642], [348, 153], [491, 51, 463], [503, 692, 1], []], ![[82, 581, 613, 181], [193, 554], [372, 355, 152, 97], [277, 683, 539, 231], [513, 473, 564, 529], [254, 499], [625, 456, 102, 636], [16, 6, 211, 650], [518, 111]], ![[24, 635, 273, 126], [711, 140], [341, 252, 37, 55], [392, 469, 269, 471], [75, 157, 374, 223], [500, 495], [345, 547, 279, 613], [187, 521, 708, 319], [381, 111]]]
 h' := ![![[72, 696, 298], [388, 314, 632], [269, 7, 230], [31, 99, 548], [664, 120, 626], [400, 557, 195], [689, 437, 624], [358, 189, 221], [0, 0, 1], [0, 1]], ![[620, 36, 435], [1, 274, 510], [507, 311, 104], [521, 404, 119], [619, 139, 389], [569, 462, 18], [384, 388, 226], [714, 566, 507], [547, 608, 36], [72, 696, 298]], ![[0, 1], [368, 145, 324], [623, 415, 399], [145, 230, 66], [578, 474, 451], [432, 447, 520], [211, 641, 616], [673, 711, 5], [244, 125, 696], [620, 36, 435]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [564, 97], []]
 b := ![[], [69, 164, 499], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI733N0 : CertifiedPrimeIdeal' SI733N0 733 where
  n := 3
  hpos := by decide
  P := [333, 445, 41, 1]
  hirr := P733P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1651074, -3885468, 2151486, 6237366, -525609]
  a := ![-1, 0, -2, 2, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1938288, -2428374, -3295215, 6237366, -525609]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI733N0 : Ideal.IsPrime I733N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI733N0 B_one_repr
lemma NI733N0 : Nat.card (O ⧸ I733N0) = 393832837 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI733N0

def I733N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-659, -1588, 762, 2346, -78]] i)))

def SI733N1: IdealEqSpanCertificate' Table ![![-659, -1588, 762, 2346, -78]] 
 ![![733, 0, 0, 0, 0], ![0, 733, 0, 0, 0], ![123, 433, 1, 0, 0], ![591, 197, 0, 1, 0], ![388, 609, 0, 0, 1]] where
  M :=![![![-659, -1588, 762, 2346, -78], ![-468, -1829, -1336, -1062, 2346], ![14076, 34722, -14159, -47058, -1062], ![-8100, -17670, 14338, 36085, -7312], ![-54096, -136068, 47362, 170586, 13087]]]
  hmulB := by decide  
  f := ![![![-11228591, -5988740, 2653870, -483930, 951606]], ![![5709636, 3045499, -1349624, 246102, -483930]], ![![1484655, 792001, -350989, 64002, -125850]], ![![-7516509, -4008835, 1776480, -323939, 637000]], ![![-1198088, -638765, 283038, -51612, 101497]]]
  g := ![![![-1979, -1018, 762, 2346, -78], ![-162, -877, -1336, -1062, 2346], ![40899, 21941, -14159, -47058, -1062], ![-27641, -12117, 14338, 36085, -7312], ![-152488, -84883, 47362, 170586, 13087]]]
  hle1 := by decide   
  hle2 := by decide  


def P733P1 : CertificateIrreducibleZModOfList' 733 2 2 9 [710, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [696, 732], [0, 1]]
 g := ![![[94, 184], [124], [708, 652], [13, 292], [715, 361], [410], [213, 480], [421, 636], [1]], ![[616, 549], [124], [40, 81], [204, 441], [552, 372], [410], [45, 253], [345, 97], [1]]]
 h' := ![![[696, 732], [695, 430], [158, 503], [299, 245], [319, 650], [216, 19], [501, 487], [154, 313], [23, 696], [0, 1]], ![[0, 1], [178, 303], [605, 230], [30, 488], [458, 83], [246, 714], [74, 246], [301, 420], [659, 37], [696, 732]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [294]]
 b := ![[], [154, 147]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI733N1 : CertifiedPrimeIdeal' SI733N1 733 where
  n := 2
  hpos := by decide
  P := [710, 37, 1]
  hirr := P733P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-130, -2288, 474, 2086, 968]
  a := ![0, 0, -6, -10, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2274, -1648, 474, 2086, 968]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI733N1 : Ideal.IsPrime I733N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI733N1 B_one_repr
lemma NI733N1 : Nat.card (O ⧸ I733N1) = 537289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI733N1
def MulI733N0 : IdealMulLeCertificate' Table 
  ![![-11228591, -5988740, 2653870, -483930, 951606]] ![![-659, -1588, 762, 2346, -78]]
  ![![733, 0, 0, 0, 0]] where
 M := ![![![733, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC733 : ContainsPrimesAboveP 733 ![I733N0, I733N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI733N0
    exact isPrimeI733N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 733 (by decide) (𝕀 ⊙ MulI733N0)
instance hp739 : Fact (Nat.Prime 739) := {out := by norm_num}

def I739N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32441, 54201, -17237, 7890, -6498]] i)))

def SI739N0: IdealEqSpanCertificate' Table ![![32441, 54201, -17237, 7890, -6498]] 
 ![![739, 0, 0, 0, 0], ![0, 739, 0, 0, 0], ![0, 0, 739, 0, 0], ![113, 343, 2, 1, 0], ![461, 721, 330, 0, 1]] where
  M :=![![![32441, 54201, -17237, 7890, -6498], ![-38988, -65029, 20592, -10128, 7890], ![47340, 79362, -24685, 11916, -10128], ![-33798, -57111, 17993, -6217, 7050], ![-11754, -20019, 4179, -7026, 4805]]]
  hmulB := by decide  
  f := ![![![-27025, -16689, 3455, -2454, 1740]], ![![10440, -925, -10830, -3228, -2454]], ![![-14724, -26370, -20371, -11124, -3228]], ![![679, -3049, -4554, -1903, -882]], ![![-13253, -23113, -17534, -9660, -2755]]]
  g := ![![![2891, 2751, 2857, 7890, -6498], ![-3426, -3085, -3468, -10128, 7890], ![4560, 4458, 4457, 11916, -10128], ![-3493, -4070, -3107, -6217, 7050], ![-1939, -1454, -2121, -7026, 4805]]]
  hle1 := by decide   
  hle2 := by decide  


def P739P0 : CertificateIrreducibleZModOfList' 739 3 2 9 [40, 473, 586, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 170, 604], [21, 568, 135], [0, 1]]
 g := ![![[514, 686, 500], [27, 319, 710], [548, 603], [34, 657], [437, 529], [624, 410, 692], [184, 198, 593], [27, 153, 1], []], ![[298, 637, 717, 186], [153, 620, 129, 159], [308, 234], [36, 716], [137, 280], [649, 319, 283, 710], [114, 199, 564, 371], [203, 322, 253, 203], [96, 489]], ![[265, 32, 600, 319], [111, 702, 180, 171], [79, 571], [695, 518], [488, 712], [191, 604, 434, 163], [289, 504, 274, 137], [518, 380, 550, 319], [565, 489]]]
 h' := ![![[132, 170, 604], [398, 383, 586], [7, 729, 649], [596, 229, 663], [469, 344, 246], [166, 467, 23], [30, 637, 133], [398, 323, 449], [0, 0, 1], [0, 1]], ![[21, 568, 135], [418, 41, 323], [650, 104, 482], [524, 416, 556], [704, 144, 174], [308, 168, 271], [424, 177, 634], [421, 207, 73], [282, 604, 568], [132, 170, 604]], ![[0, 1], [107, 315, 569], [285, 645, 347], [135, 94, 259], [53, 251, 319], [619, 104, 445], [90, 664, 711], [296, 209, 217], [11, 135, 170], [21, 568, 135]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [516, 729], []]
 b := ![[], [6, 173, 301], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI739N0 : CertifiedPrimeIdeal' SI739N0 739 where
  n := 3
  hpos := by decide
  P := [40, 473, 586, 1]
  hirr := P739P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-119038, -758977, -130478, 253213, 663273]
  a := ![13, -1, -2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-452640, -765671, -297046, 253213, 663273]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI739N0 : Ideal.IsPrime I739N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI739N0 B_one_repr
lemma NI739N0 : Nat.card (O ⧸ I739N0) = 403583419 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI739N0

def I739N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2017, 3372, -1054, 494, -402]] i)))

def SI739N1: IdealEqSpanCertificate' Table ![![2017, 3372, -1054, 494, -402]] 
 ![![739, 0, 0, 0, 0], ![113, 1, 0, 0, 0], ![533, 0, 1, 0, 0], ![534, 0, 0, 1, 0], ![174, 0, 0, 0, 1]] where
  M :=![![![2017, 3372, -1054, 494, -402], ![-2412, -4013, 1324, -570, 494], ![2964, 4998, -1447, 762, -570], ![-2052, -3430, 1086, -499, 412], ![-720, -1164, 490, -138, 167]]]
  hmulB := by decide  
  f := ![![![835, 1364, -326, -1138, -330]], ![![125, 203, -46, -164, -52]], ![![593, 958, -233, -800, -228]], ![![618, 1022, -250, -871, -240]], ![![222, 396, -70, -306, -121]]]
  g := ![![![-15, 3372, -1054, 494, -402], ![-49, -4013, 1324, -570, 494], ![-133, 4998, -1447, 762, -570], ![2, -3430, 1086, -499, 412], ![-116, -1164, 490, -138, 167]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI739N1 : Nat.card (O ⧸ I739N1) = 739 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI739N1)

lemma isPrimeI739N1 : Ideal.IsPrime I739N1 := prime_ideal_of_norm_prime hp739.out _ NI739N1

def I739N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1150549, -613507, 271899, -49562, 97494]] i)))

def SI739N2: IdealEqSpanCertificate' Table ![![-1150549, -613507, 271899, -49562, 97494]] 
 ![![739, 0, 0, 0, 0], ![617, 1, 0, 0, 0], ![635, 0, 1, 0, 0], ![647, 0, 0, 1, 0], ![220, 0, 0, 0, 1]] where
  M :=![![![-1150549, -613507, 271899, -49562, 97494], ![584964, 311861, -138224, 25188, -49562], ![-297372, -158466, 70249, -12792, 25188], ![173874, 92641, -41071, 7477, -14726], ![135894, 72441, -32109, 5850, -11513]]]
  hmulB := by decide  
  f := ![![![749, 2339, 4139, 3622, 696]], ![![631, 1968, 3467, 3026, 586]], ![![673, 2089, 3584, 3086, 600]], ![![643, 2018, 3640, 3219, 604]], ![![182, 593, 1301, 1246, 241]]]
  g := ![![![291401, -613507, 271899, -49562, 97494], ![-148111, 311861, -138224, 25188, -49562], ![75241, -158466, 70249, -12792, 25188], ![-43983, 92641, -41071, 7477, -14726], ![-34402, 72441, -32109, 5850, -11513]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI739N2 : Nat.card (O ⧸ I739N2) = 739 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI739N2)

lemma isPrimeI739N2 : Ideal.IsPrime I739N2 := prime_ideal_of_norm_prime hp739.out _ NI739N2
def MulI739N0 : IdealMulLeCertificate' Table 
  ![![32441, 54201, -17237, 7890, -6498]] ![![2017, 3372, -1054, 494, -402]]
  ![![-127901503, -213767115, 67895769, -31043696, 25724616]] where
 M := ![![![-127901503, -213767115, 67895769, -31043696, 25724616]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI739N1 : IdealMulLeCertificate' Table 
  ![![-127901503, -213767115, 67895769, -31043696, 25724616]] ![![-1150549, -613507, 271899, -49562, 97494]]
  ![![739, 0, 0, 0, 0]] where
 M := ![![![18708465619, 31268086172, -9931240684, 4540810626, -3762786992]]]
 hmul := by decide  
 g := ![![![![25315921, 42311348, -13438756, 6144534, -5091728]]]]
 hle2 := by decide  


def PBC739 : ContainsPrimesAboveP 739 ![I739N0, I739N1, I739N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI739N0
    exact isPrimeI739N1
    exact isPrimeI739N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 739 (by decide) (𝕀 ⊙ MulI739N0 ⊙ MulI739N1)
instance hp743 : Fact (Nat.Prime 743) := {out := by norm_num}

def I743N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![210001, 111395, -50402, 8711, -17941]] i)))

def SI743N0: IdealEqSpanCertificate' Table ![![210001, 111395, -50402, 8711, -17941]] 
 ![![743, 0, 0, 0, 0], ![0, 743, 0, 0, 0], ![0, 0, 743, 0, 0], ![0, 0, 0, 743, 0], ![391, 205, 626, 629, 1]] where
  M :=![![![210001, 111395, -50402, 8711, -17941], ![-107646, -59114, 23242, -5607, 8711], ![52266, 23019, -18625, -525, -5607], ![-31740, -16816, 7662, -1279, 2716], ![-26658, -18429, 946, -3441, 1262]]]
  hmulB := by decide  
  f := ![![![-709, -1185, 376, -173, 143]], ![![858, 1436, -456, 201, -173]], ![![-1038, -1737, 559, -225, 201]], ![![720, 1198, -386, 181, -138]], ![![-401, -676, 216, -72, 80]]]
  g := ![![![9724, 5100, 15048, 15200, -17941], ![-4729, -2483, -7308, -7382, 8711], ![3021, 1578, 4699, 4746, -5607], ![-1472, -772, -2278, -2301, 2716], ![-700, -373, -1062, -1073, 1262]]]
  hle1 := by decide   
  hle2 := by decide  


def P743P0 : CertificateIrreducibleZModOfList' 743 4 2 9 [271, 487, 358, 241, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [547, 237, 67, 284], [495, 333, 122, 166], [203, 172, 554, 293], [0, 1]]
 g := ![![[157, 111, 500, 641], [229, 121, 259, 33], [609, 242, 410, 542], [740, 280, 373], [242, 458, 365], [28, 244, 510, 94], [155, 75, 479, 608], [502, 1], []], ![[374, 88, 157, 734, 107, 691], [48, 552, 345, 457, 54, 171], [83, 40, 461, 732, 27, 523], [142, 164, 607], [388, 316, 659], [64, 548, 540, 588, 522, 633], [665, 417, 680, 275, 471, 81], [462, 338, 534, 51, 528, 279], [192, 433, 412]], ![[143, 390, 208, 454, 733, 132], [52, 311, 310, 198, 334, 150], [562, 102, 306, 633, 415, 589], [416, 630, 368], [280, 86, 23], [699, 524, 465, 430, 603, 381], [140, 263, 610, 302, 365, 105], [403, 556, 671, 442, 115, 35], [531, 320, 65]], ![[182, 263, 91, 659, 627, 661], [37, 276, 270, 293, 299, 113], [255, 404, 553, 356, 733, 61], [392, 625, 57], [273, 411, 506], [721, 157, 665, 471, 234, 317], [536, 298, 599, 556, 281, 669], [8, 148, 134, 194, 219, 711], [277, 665, 404]]]
 h' := ![![[547, 237, 67, 284], [353, 304, 644, 677], [650, 52, 297, 274], [153, 692, 222, 101], [247, 692, 227, 341], [585, 577, 176, 114], [346, 165, 4, 295], [670, 445, 346, 512], [0, 0, 1], [0, 1]], ![[495, 333, 122, 166], [658, 581, 677, 295], [624, 279, 16, 92], [360, 742, 574, 146], [367, 587, 138, 571], [740, 79, 468, 582], [259, 95, 233, 16], [428, 406, 201, 545], [501, 136, 487, 707], [547, 237, 67, 284]], ![[203, 172, 554, 293], [616, 7, 702, 314], [663, 304, 11, 72], [201, 78, 344, 255], [742, 536, 226, 385], [346, 195, 542, 461], [569, 156, 616, 305], [64, 73, 386, 484], [76, 699, 370, 383], [495, 333, 122, 166]], ![[0, 1], [128, 594, 206, 200], [200, 108, 419, 305], [702, 717, 346, 241], [296, 414, 152, 189], [291, 635, 300, 329], [405, 327, 633, 127], [350, 562, 553, 688], [320, 651, 628, 396], [203, 172, 554, 293]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [385, 175, 655], []]
 b := ![[], [], [199, 219, 694, 99], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI743N0 : CertifiedPrimeIdeal' SI743N0 743 where
  n := 4
  hpos := by decide
  P := [271, 487, 358, 241, 1]
  hirr := P743P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10415296, 24825782, -12779875, -38222436, 2249057]
  a := ![-1, -3, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1169537, -587121, -1912099, -1955423, 2249057]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI743N0 : Ideal.IsPrime I743N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI743N0 B_one_repr
lemma NI743N0 : Nat.card (O ⧸ I743N0) = 304758098401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI743N0

def I743N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![709, 1185, -376, 173, -143]] i)))

def SI743N1: IdealEqSpanCertificate' Table ![![709, 1185, -376, 173, -143]] 
 ![![743, 0, 0, 0, 0], ![114, 1, 0, 0, 0], ![378, 0, 1, 0, 0], ![59, 0, 0, 1, 0], ![516, 0, 0, 0, 1]] where
  M :=![![![709, 1185, -376, 173, -143], ![-858, -1436, 456, -201, 173], ![1038, 1737, -559, 225, -201], ![-720, -1198, 386, -181, 138], ![-294, -507, 188, 57, 32]]]
  hmulB := by decide  
  f := ![![![-210001, -111395, 50402, -8711, 17941]], ![![-32076, -17012, 7702, -1329, 2741]], ![![-106908, -56703, 25667, -4431, 9135]], ![![-16633, -8823, 3992, -690, 1421]], ![![-145806, -77337, 35002, -6045, 12458]]]
  g := ![![![96, 1185, -376, 173, -143], ![-117, -1436, 456, -201, 173], ![141, 1737, -559, 225, -201], ![-95, -1198, 386, -181, 138], ![-45, -507, 188, 57, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI743N1 : Nat.card (O ⧸ I743N1) = 743 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI743N1)

lemma isPrimeI743N1 : Ideal.IsPrime I743N1 := prime_ideal_of_norm_prime hp743.out _ NI743N1
def MulI743N0 : IdealMulLeCertificate' Table 
  ![![210001, 111395, -50402, 8711, -17941]] ![![709, 1185, -376, 173, -143]]
  ![![743, 0, 0, 0, 0]] where
 M := ![![![-743, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC743 : ContainsPrimesAboveP 743 ![I743N0, I743N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI743N0
    exact isPrimeI743N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 743 (by decide) (𝕀 ⊙ MulI743N0)
instance hp751 : Fact (Nat.Prime 751) := {out := by norm_num}

def I751N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![96587, 161680, -50587, 23677, -19285]] i)))

def SI751N0: IdealEqSpanCertificate' Table ![![96587, 161680, -50587, 23677, -19285]] 
 ![![751, 0, 0, 0, 0], ![0, 751, 0, 0, 0], ![0, 0, 751, 0, 0], ![0, 0, 0, 751, 0], ![675, 272, 619, 494, 1]] where
  M :=![![![96587, 161680, -50587, 23677, -19285], ![-115710, -192688, 63382, -27423, 23677], ![142062, 239445, -69827, 36375, -27423], ![-98454, -164603, 52127, -23933, 19774], ![-34656, -56208, 23169, -6795, 7966]]]
  hmulB := by decide  
  f := ![![![-571, -306, 135, -23, 49]], ![![294, 164, -74, -3, -23]], ![![-138, -51, 37, -21, -3]], ![![66, -5, -3, 67, -2]], ![![-477, -261, 123, 5, 32]]]
  g := ![![![17462, 7200, 15828, 12717, -19285], ![-21435, -8832, -19431, -15611, 23677], ![24837, 10251, 22510, 18087, -27423], ![-17904, -7381, -16229, -13039, 19774], ![-7206, -2960, -6535, -5249, 7966]]]
  hle1 := by decide   
  hle2 := by decide  


def P751P0 : CertificateIrreducibleZModOfList' 751 4 2 9 [150, 59, 64, 449, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [455, 150, 475, 581], [91, 500, 312, 434], [507, 100, 715, 487], [0, 1]]
 g := ![![[22, 75, 540, 652], [112, 88, 325, 419], [205, 0, 133, 535], [393, 484, 396, 151], [66, 233, 678], [194, 747, 218, 627], [575, 666, 106, 265], [302, 1], []], ![[424, 566, 712, 501, 278, 479], [37, 71, 663, 541, 709, 673], [470, 383, 375, 698, 124, 26], [470, 574, 663, 341, 219, 265], [69, 250, 538], [576, 43, 399, 240, 534, 616], [279, 314, 393, 13, 164, 338], [210, 302, 478, 588, 161, 65], [85, 394, 362]], ![[15, 605, 277, 735, 478, 490], [455, 478, 275, 266, 735, 523], [409, 524, 545, 114, 441, 1], [59, 424, 586, 326, 689, 625], [394, 622, 47], [590, 697, 202, 330, 13, 433], [500, 18, 16, 54, 464, 132], [699, 732, 464, 518, 317, 479], [713, 224, 606]], ![[163, 610, 355, 321, 14, 221], [1, 592, 284, 183, 138, 27], [96, 427, 440, 22, 299, 252], [112, 69, 534, 711, 206, 409], [172, 298, 717], [596, 239, 726, 388, 476, 440], [311, 122, 265, 487, 209, 664], [499, 495, 404, 551, 46, 83], [347, 148, 604]]]
 h' := ![![[455, 150, 475, 581], [473, 648, 631, 305], [41, 121, 674, 249], [379, 100, 95, 680], [287, 523, 29, 619], [189, 126, 525, 72], [115, 377, 535, 410], [511, 56, 139, 269], [0, 0, 1], [0, 1]], ![[91, 500, 312, 434], [397, 543, 128, 647], [580, 376, 285, 298], [701, 651, 416, 635], [354, 46, 268, 131], [377, 104, 734, 177], [154, 551, 98, 81], [348, 134, 592, 245], [517, 289, 19, 691], [455, 150, 475, 581]], ![[507, 100, 715, 487], [102, 682, 593, 300], [93, 232, 45, 496], [742, 739, 414, 495], [479, 452, 106, 392], [549, 190, 108, 563], [322, 150, 81, 81], [644, 326, 688, 684], [463, 313, 77, 484], [91, 500, 312, 434]], ![[0, 1], [591, 380, 150, 250], [466, 22, 498, 459], [558, 12, 577, 443], [695, 481, 348, 360], [720, 331, 135, 690], [0, 424, 37, 179], [143, 235, 83, 304], [727, 149, 654, 327], [507, 100, 715, 487]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [731, 364, 171], []]
 b := ![[], [], [99, 75, 231, 517], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI751N0 : CertifiedPrimeIdeal' SI751N0 751 where
  n := 4
  hpos := by decide
  P := [150, 59, 64, 449, 1]
  hirr := P751P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25991217, 72779602, 1336731, -48870402, -28037259]
  a := ![3, 0, 3, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![25234542, 10251550, 23111052, 18377544, -28037259]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI751N0 : Ideal.IsPrime I751N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI751N0 B_one_repr
lemma NI751N0 : Nat.card (O ⧸ I751N0) = 318097128001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI751N0

def I751N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-571, -306, 135, -23, 49]] i)))

def SI751N1: IdealEqSpanCertificate' Table ![![-571, -306, 135, -23, 49]] 
 ![![751, 0, 0, 0, 0], ![257, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![563, 0, 0, 1, 0], ![478, 0, 0, 0, 1]] where
  M :=![![![-571, -306, 135, -23, 49], ![294, 164, -74, -3, -23], ![-138, -51, 37, -21, -3], ![66, -5, -3, 67, -2], ![48, -30, -45, -3, 58]]]
  hmulB := by decide  
  f := ![![![96587, 161680, -50587, 23677, -19285]], ![![32899, 55072, -17227, 8066, -6568]], ![![5205, 8715, -2720, 1278, -1038]], ![![72277, 120987, -37854, 17718, -14431]], ![![61430, 102832, -32167, 15061, -12264]]]
  g := ![![![83, -306, 135, -23, 49], ![-35, 164, -74, -3, -23], ![33, -51, 37, -21, -3], ![-47, -5, -3, 67, -2], ![-22, -30, -45, -3, 58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI751N1 : Nat.card (O ⧸ I751N1) = 751 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI751N1)

lemma isPrimeI751N1 : Ideal.IsPrime I751N1 := prime_ideal_of_norm_prime hp751.out _ NI751N1
def MulI751N0 : IdealMulLeCertificate' Table 
  ![![96587, 161680, -50587, 23677, -19285]] ![![-571, -306, 135, -23, 49]]
  ![![751, 0, 0, 0, 0]] where
 M := ![![![751, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC751 : ContainsPrimesAboveP 751 ![I751N0, I751N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI751N0
    exact isPrimeI751N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 751 (by decide) (𝕀 ⊙ MulI751N0)
instance hp757 : Fact (Nat.Prime 757) := {out := by norm_num}

def I757N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-125, -1164, -2149, -2871, 2923]] i)))

def SI757N0: IdealEqSpanCertificate' Table ![![-125, -1164, -2149, -2871, 2923]] 
 ![![757, 0, 0, 0, 0], ![0, 757, 0, 0, 0], ![0, 0, 757, 0, 0], ![220, 363, 107, 1, 0], ![222, 662, 440, 0, 1]] where
  M :=![![![-125, -1164, -2149, -2871, 2923], ![17538, 43720, -16432, -56895, -2871], ![-17226, -25527, 62803, 123771, -56895], ![-48282, -132345, 13047, 109717, 49076], ![132384, 265296, -297281, -681315, 200050]]]
  hmulB := by decide  
  f := ![![![7421863, 3958122, -1754113, 319803, -628969]], ![![-3773814, -2012672, 891856, -162645, 319803]], ![![1918818, 1023231, -453671, 82617, -162645]], ![![617050, 329028, -145890, 26563, -52302]], ![![-9522, -5194, 2097, -477, 778]]]
  g := ![![![-23, -1181, -1296, -2871, 2923], ![17400, 29851, 9689, -56895, -2871], ![-19308, -9630, 15658, 123771, -56895], ![-46342, -95704, -44016, 109717, 49076], ![139512, 152113, -20368, -681315, 200050]]]
  hle1 := by decide   
  hle2 := by decide  


def P757P0 : CertificateIrreducibleZModOfList' 757 3 2 9 [325, 594, 683, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [364, 243, 45], [467, 513, 712], [0, 1]]
 g := ![![[120, 265, 681], [353, 549], [75, 120, 756], [299, 572], [328, 287, 190], [622, 55, 567], [645, 674, 566], [340, 74, 1], []], ![[655, 33, 147, 118], [292, 10], [347, 645, 5, 114], [592, 74], [656, 624, 375, 197], [668, 303, 26, 631], [477, 375, 601, 584], [698, 108, 2, 97], [638, 511]], ![[216, 409, 284, 295], [60, 598], [2, 646, 86, 714], [698, 524], [459, 67, 509, 327], [605, 389, 640, 464], [118, 46, 754, 702], [206, 123, 197, 622], [728, 511]]]
 h' := ![![[364, 243, 45], [430, 747, 349], [606, 452, 241], [322, 645, 87], [137, 514, 60], [726, 552, 257], [64, 119, 406], [22, 333, 561], [0, 0, 1], [0, 1]], ![[467, 513, 712], [599, 516, 692], [361, 279, 143], [605, 265, 227], [295, 677, 163], [455, 284, 739], [29, 715, 159], [81, 222, 735], [89, 516, 513], [364, 243, 45]], ![[0, 1], [201, 251, 473], [337, 26, 373], [690, 604, 443], [65, 323, 534], [34, 678, 518], [406, 680, 192], [203, 202, 218], [414, 241, 243], [467, 513, 712]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [419, 667], []]
 b := ![[], [229, 488, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI757N0 : CertifiedPrimeIdeal' SI757N0 757 where
  n := 3
  hpos := by decide
  P := [325, 594, 683, 1]
  hirr := P757P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![792469, 1745485, -1259782, -3347767, 716609]
  a := ![1, 1, 1, -1, 4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![763823, 980964, 55011, -3347767, 716609]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI757N0 : Ideal.IsPrime I757N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI757N0 B_one_repr
lemma NI757N0 : Nat.card (O ⧸ I757N0) = 433798093 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI757N0

def I757N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7421863, 3958122, -1754113, 319803, -628969]] i)))

def SI757N1: IdealEqSpanCertificate' Table ![![7421863, 3958122, -1754113, 319803, -628969]] 
 ![![757, 0, 0, 0, 0], ![0, 757, 0, 0, 0], ![406, 118, 1, 0, 0], ![644, 716, 0, 1, 0], ![59, 178, 0, 0, 1]] where
  M :=![![![7421863, 3958122, -1754113, 319803, -628969], ![-3773814, -2012672, 891856, -162645, 319803], ![1918818, 1023231, -453671, 82617, -162645], ![-1122054, -598425, 265199, -48353, 95092], ![-876792, -467718, 207083, -37845, 74278]]]
  hmulB := by decide  
  f := ![![![-125, -1164, -2149, -2871, 2923]], ![![17538, 43720, -16432, -56895, -2871]], ![![2644, 6157, -3631, -10245, 1045]], ![![16418, 40187, -17353, -56111, -164]], ![![4289, 10540, -4424, -14502, -183]]]
  g := ![![![727540, 124070, -1754113, 319803, -628969], ![-369871, -63042, 891856, -162645, 319803], ![188243, 32171, -453671, 82617, -162645], ![-109992, -18755, 265199, -48353, 95092], ![-85816, -14568, 207083, -37845, 74278]]]
  hle1 := by decide   
  hle2 := by decide  


def P757P1 : CertificateIrreducibleZModOfList' 757 2 2 9 [682, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [695, 756], [0, 1]]
 g := ![![[413, 434], [717], [354, 94], [636], [576, 547], [16, 459], [656, 747], [668, 59], [1]], ![[0, 323], [717], [582, 663], [636], [727, 210], [324, 298], [519, 10], [38, 698], [1]]]
 h' := ![![[695, 756], [25, 501], [55, 99], [339, 650], [51, 200], [443, 150], [752, 332], [138, 428], [75, 695], [0, 1]], ![[0, 1], [0, 256], [730, 658], [160, 107], [520, 557], [227, 607], [607, 425], [97, 329], [134, 62], [695, 756]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [369]]
 b := ![[], [42, 563]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI757N1 : CertifiedPrimeIdeal' SI757N1 757 where
  n := 2
  hpos := by decide
  P := [682, 62, 1]
  hirr := P757P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![940, -14, 7, 90, -1]
  a := ![4, 0, 0, 1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-79, -86, 7, 90, -1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI757N1 : Ideal.IsPrime I757N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI757N1 B_one_repr
lemma NI757N1 : Nat.card (O ⧸ I757N1) = 573049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI757N1
def MulI757N0 : IdealMulLeCertificate' Table 
  ![![-125, -1164, -2149, -2871, 2923]] ![![7421863, 3958122, -1754113, 319803, -628969]]
  ![![757, 0, 0, 0, 0]] where
 M := ![![![757, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC757 : ContainsPrimesAboveP 757 ![I757N0, I757N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI757N0
    exact isPrimeI757N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 757 (by decide) (𝕀 ⊙ MulI757N0)
instance hp761 : Fact (Nat.Prime 761) := {out := by norm_num}

def I761N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![761, 0, 0, 0, 0]] i)))

def SI761N0: IdealEqSpanCertificate' Table ![![761, 0, 0, 0, 0]] 
 ![![761, 0, 0, 0, 0], ![0, 761, 0, 0, 0], ![0, 0, 761, 0, 0], ![0, 0, 0, 761, 0], ![0, 0, 0, 0, 761]] where
  M :=![![![761, 0, 0, 0, 0], ![0, 761, 0, 0, 0], ![0, 0, 761, 0, 0], ![0, 0, 0, 761, 0], ![0, 0, 0, 0, 761]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P761P0 : CertificateIrreducibleZModOfList' 761 5 2 9 [208, 604, 451, 695, 412, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [670, 655, 340, 453, 438], [23, 349, 128, 416, 426], [441, 429, 1, 694, 151], [737, 88, 292, 720, 507], [0, 1]]
 g := ![![[48, 50, 741, 205, 403], [142, 539, 695, 182], [339, 0, 714, 93], [512, 329, 347, 601, 703], [39, 696, 420, 536, 498], [338, 539, 156, 679, 627], [547, 638, 713, 258, 41], [1], []], ![[81, 549, 71, 187, 259, 655, 496, 144], [562, 586, 532, 381], [27, 116, 224, 132], [614, 652, 651, 562, 96, 92, 419, 676], [88, 312, 423, 57, 498, 625, 56, 214], [293, 148, 117, 519, 28, 79, 14, 695], [693, 170, 581, 366, 554, 482, 540, 185], [456, 570, 407, 417, 237, 418, 437, 312], [103, 226, 362, 72]], ![[639, 251, 211, 594, 643, 477, 166, 200], [427, 546, 558, 627], [583, 358, 522, 78], [361, 122, 223, 595, 230, 32, 446, 94], [495, 13, 290, 190, 506, 173, 682, 8], [109, 331, 37, 175, 377, 272, 148, 185], [370, 222, 33, 656, 58, 30, 261, 666], [676, 224, 303, 288, 245, 181, 373, 525], [129, 60, 705, 358]], ![[464, 263, 479, 83, 719, 552, 158, 253], [400, 148, 16, 304], [489, 756, 593, 58], [735, 583, 541, 535, 65, 58, 0, 62], [563, 432, 598, 151, 754, 198, 222, 506], [205, 507, 726, 551, 569, 669, 457, 491], [52, 195, 24, 260, 48, 389, 744, 458], [588, 210, 232, 537, 111, 480, 56, 653], [473, 580, 85, 732]], ![[648, 575, 489, 386, 715, 186, 3, 280], [292, 552, 278, 42], [323, 174, 38, 470], [105, 167, 182, 275, 461, 362, 79, 321], [631, 686, 656, 719, 136, 175, 394, 387], [286, 112, 157, 748, 126, 651, 332, 494], [429, 316, 435, 166, 674, 351, 274, 257], [623, 71, 148, 719, 635, 603, 127, 530], [106, 299, 658, 592]]]
 h' := ![![[670, 655, 340, 453, 438], [690, 262, 91, 147, 128], [675, 78, 721, 297, 121], [44, 650, 33, 309, 669], [259, 650, 628, 443, 392], [469, 164, 61, 19, 487], [374, 244, 567, 642, 373], [553, 157, 310, 66, 349], [0, 0, 1], [0, 1]], ![[23, 349, 128, 416, 426], [660, 327, 758, 578, 203], [357, 38, 491, 459, 344], [307, 232, 470, 542, 612], [653, 395, 487, 289, 313], [602, 306, 337, 47, 717], [475, 753, 540, 222, 350], [676, 514, 613, 515, 614], [555, 631, 69, 718, 85], [670, 655, 340, 453, 438]], ![[441, 429, 1, 694, 151], [100, 476, 141, 200, 359], [429, 210, 574, 669, 388], [297, 306, 214, 524, 721], [688, 622, 638, 611, 232], [176, 472, 148, 637, 224], [35, 7, 721, 175, 701], [438, 665, 460, 627, 28], [332, 236, 19, 590, 191], [23, 349, 128, 416, 426]], ![[737, 88, 292, 720, 507], [511, 677, 133, 107, 700], [1, 692, 310, 63, 209], [453, 628, 478, 264, 68], [45, 174, 691, 155, 300], [476, 447, 425, 189, 113], [522, 47, 373, 291, 15], [178, 246, 561, 211, 54], [211, 203, 81, 173, 256], [441, 429, 1, 694, 151]], ![[0, 1], [98, 541, 399, 490, 132], [189, 504, 187, 34, 460], [636, 467, 327, 644, 213], [57, 442, 600, 24, 285], [727, 133, 551, 630, 742], [683, 471, 82, 192, 83], [371, 701, 339, 103, 477], [597, 452, 591, 41, 229], [737, 88, 292, 720, 507]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [199, 575, 530, 737], [], [], []]
 b := ![[], [689, 119, 688, 336, 146], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI761N0 : CertifiedPrimeIdeal' SI761N0 761 where
  n := 5
  hpos := by decide
  P := [208, 604, 451, 695, 412, 1]
  hirr := P761P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-41262428540363, -109891609251150, 19845530281268, 106411888923822, 30961143746985]
  a := ![7, 2, -24, 0, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-54221325283, -144404217150, 26078226388, 139831654302, 40684814385]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI761N0 : Ideal.IsPrime I761N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI761N0 B_one_repr
lemma NI761N0 : Nat.card (O ⧸ I761N0) = 255225041939801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI761N0

def PBC761 : ContainsPrimesAboveP 761 ![I761N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI761N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![761, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 761 (by decide) 𝕀



lemma PB1556I14_primes (p : ℕ) :
  p ∈ Set.range ![709, 719, 727, 733, 739, 743, 751, 757, 761] ↔ Nat.Prime p ∧ 701 < p ∧ p ≤ 761 := by
  rw [← List.mem_ofFn']
  convert primes_range 701 761 (by omega)

def PB1556I14 : PrimesBelowBoundCertificateInterval O 701 761 1556 where
  m := 9
  g := ![4, 2, 4, 2, 3, 2, 2, 2, 1]
  P := ![709, 719, 727, 733, 739, 743, 751, 757, 761]
  hP := PB1556I14_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I709N0, I709N1, I709N2, I709N3]
    · exact ![I719N0, I719N1]
    · exact ![I727N0, I727N1, I727N2, I727N3]
    · exact ![I733N0, I733N1]
    · exact ![I739N0, I739N1, I739N2]
    · exact ![I743N0, I743N1]
    · exact ![I751N0, I751N1]
    · exact ![I757N0, I757N1]
    · exact ![I761N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC709
    · exact PBC719
    · exact PBC727
    · exact PBC733
    · exact PBC739
    · exact PBC743
    · exact PBC751
    · exact PBC757
    · exact PBC761
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![502681, 709, 709, 709]
    · exact ![371694959, 516961]
    · exact ![528529, 727, 727, 727]
    · exact ![393832837, 537289]
    · exact ![403583419, 739, 739]
    · exact ![304758098401, 743]
    · exact ![318097128001, 751]
    · exact ![433798093, 573049]
    · exact ![255225041939801]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI709N0
      exact NI709N1
      exact NI709N2
      exact NI709N3
    · dsimp ; intro j
      fin_cases j
      exact NI719N0
      exact NI719N1
    · dsimp ; intro j
      fin_cases j
      exact NI727N0
      exact NI727N1
      exact NI727N2
      exact NI727N3
    · dsimp ; intro j
      fin_cases j
      exact NI733N0
      exact NI733N1
    · dsimp ; intro j
      fin_cases j
      exact NI739N0
      exact NI739N1
      exact NI739N2
    · dsimp ; intro j
      fin_cases j
      exact NI743N0
      exact NI743N1
    · dsimp ; intro j
      fin_cases j
      exact NI751N0
      exact NI751N1
    · dsimp ; intro j
      fin_cases j
      exact NI757N0
      exact NI757N1
    · dsimp ; intro j
      fin_cases j
      exact NI761N0
  β := ![I709N1, I709N2, I709N3, I727N1, I727N2, I727N3, I739N1, I739N2, I743N1, I751N1]
  Il := ![[I709N1, I709N2, I709N3], [], [I727N1, I727N2, I727N3], [], [I739N1, I739N2], [I743N1], [I751N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
