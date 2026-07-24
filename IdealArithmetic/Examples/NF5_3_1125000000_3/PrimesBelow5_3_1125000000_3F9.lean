
import IdealArithmetic.Examples.NF5_3_1125000000_3.RI5_3_1125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp421 : Fact (Nat.Prime 421) := {out := by norm_num}

def I421N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4198, -4164, 1393, -6215, -5734]] i)))

def SI421N0: IdealEqSpanCertificate' Table ![![-4198, -4164, 1393, -6215, -5734]] 
 ![![421, 0, 0, 0, 0], ![0, 421, 0, 0, 0], ![0, 0, 421, 0, 0], ![298, 9, 360, 1, 0], ![98, 242, 381, 0, 1]] where
  M :=![![![-4198, -4164, 1393, -6215, -5734], ![-27970, -27827, 9228, -41586, -38252], ![-187480, -186426, 62013, -278452, -256184], ![-90755, -90274, 30043, -134750, -124132], ![-130843, -130108, 43243, -194393, -178783]]]
  hmulB := by decide  
  f := ![![![19962, 47712, 27075, -15355, -38984]], ![![23062, 54933, 31164, -17682, -44872]], ![![26512, 63282, 35917, -20372, -51712]], ![![37253, 88963, 50489, -28636, -72694]], ![![41881, 99916, 56700, -32163, -81637]]]
  g := ![![![5724, 3419, 10507, -6215, -5734], ![38274, 22811, 70200, -41586, -38252], ![256288, 152770, 470097, -278452, -256184], ![124061, 74020, 227635, -134750, -124132], ![178905, 106615, 328126, -194393, -178783]]]
  hle1 := by decide   
  hle2 := by decide  


def P421P0 : CertificateIrreducibleZModOfList' 421 3 2 8 [299, 404, 204, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 210, 15], [174, 210, 406], [0, 1]]
 g := ![![[411, 195, 85], [378, 94], [18, 275, 269], [230, 317], [205, 192], [328, 201, 79], [22, 358], [1]], ![[32, 376, 116, 55], [53, 187], [298, 264, 410, 272], [382, 258], [243, 395], [332, 13, 195, 279], [136, 307], [201, 208, 129, 7]], ![[229, 162, 260, 182], [312, 60], [188, 11, 242, 149], [307, 376], [20, 327], [408, 71, 154, 358], [132, 254], [218, 213, 38, 414]]]
 h' := ![![[43, 210, 15], [88, 193, 341], [91, 141, 141], [128, 0, 351], [191, 34, 100], [21, 152, 250], [307, 204, 105], [122, 17, 217], [0, 1]], ![[174, 210, 406], [136, 118, 409], [220, 154, 150], [118, 214, 35], [284, 399, 39], [398, 122, 50], [253, 419, 271], [42, 128, 357], [43, 210, 15]], ![[0, 1], [36, 110, 92], [368, 126, 130], [63, 207, 35], [366, 409, 282], [118, 147, 121], [326, 219, 45], [124, 276, 268], [174, 210, 406]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [205, 3], []]
 b := ![[], [4, 403, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI421N0 : CertifiedPrimeIdeal' SI421N0 421 where
  n := 3
  hpos := by decide
  P := [299, 404, 204, 1]
  hirr := P421P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6192886165, -6223167634, 2350148807, -8689942037, -8796861618]
  a := ![-176, -194, 145, -109, -324]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8184090925, 5227617155, 15397466885, -8689942037, -8796861618]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI421N0 : Ideal.IsPrime I421N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI421N0 B_one_repr
lemma NI421N0 : Nat.card (O ⧸ I421N0) = 74618461 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI421N0

def I421N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1480, -535, -434, 105, 616]] i)))

def SI421N1: IdealEqSpanCertificate' Table ![![1480, -535, -434, 105, 616]] 
 ![![421, 0, 0, 0, 0], ![135, 1, 0, 0, 0], ![299, 0, 1, 0, 0], ![159, 0, 0, 1, 0], ![254, 0, 0, 0, 1]] where
  M :=![![![1480, -535, -434, 105, 616], ![-952, 346, 277, -70, -392], ![598, -239, -158, 48, 224], ![-369, 142, 103, -24, -150], ![155, -73, -34, 11, 51]]]
  hmulB := by decide  
  f := ![![![28584, 68185, 38698, -21963, -55726]], ![![9244, 22051, 12515, -7103, -18022]], ![![20390, 48640, 27606, -15669, -39754]], ![![10737, 25613, 14537, -8251, -20934]], ![![17223, 41085, 23318, -13235, -33579]]]
  g := ![![![72, -535, -434, 105, 616], ![-47, 346, 277, -70, -392], ![37, -239, -158, 48, 224], ![-20, 142, 103, -24, -150], ![13, -73, -34, 11, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI421N1 : Nat.card (O ⧸ I421N1) = 421 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI421N1)

lemma isPrimeI421N1 : Ideal.IsPrime I421N1 := prime_ideal_of_norm_prime hp421.out _ NI421N1

def I421N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46, 14, -37, -5, 52]] i)))

def SI421N2: IdealEqSpanCertificate' Table ![![46, 14, -37, -5, 52]] 
 ![![421, 0, 0, 0, 0], ![176, 1, 0, 0, 0], ![178, 0, 1, 0, 0], ![53, 0, 0, 1, 0], ![401, 0, 0, 0, 1]] where
  M :=![![![46, 14, -37, -5, 52], ![-138, -107, 138, -38, -144], ![388, 256, -243, 428, -16], ![53, 110, -163, -164, 322], ![103, 10, 45, 313, -287]]]
  hmulB := by decide  
  f := ![![![-39010, -38658, 13089, -58217, -53718]], ![![-16930, -16779, 5678, -25262, -23308]], ![![-20656, -20484, 6911, -30798, -28404]], ![![-6927, -6872, 2314, -10323, -9518]], ![![-40063, -39712, 13428, -59768, -55139]]]
  g := ![![![-39, 14, -37, -5, 52], ![128, -107, 138, -38, -144], ![-42, 256, -243, 428, -16], ![-263, 110, -163, -164, 322], ![211, 10, 45, 313, -287]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI421N2 : Nat.card (O ⧸ I421N2) = 421 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI421N2)

lemma isPrimeI421N2 : Ideal.IsPrime I421N2 := prime_ideal_of_norm_prime hp421.out _ NI421N2
def MulI421N0 : IdealMulLeCertificate' Table 
  ![![-4198, -4164, 1393, -6215, -5734]] ![![1480, -535, -434, 105, 616]]
  ![![-11333, 8311, 3221, 3640, -1832]] where
 M := ![![![-11333, 8311, 3221, 3640, -1832]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI421N1 : IdealMulLeCertificate' Table 
  ![![-11333, 8311, 3221, 3640, -1832]] ![![46, 14, -37, -5, 52]]
  ![![421, 0, 0, 0, 0]] where
 M := ![![![-414264, 158717, 107776, -50941, -139772]]]
 hmul := by decide  
 g := ![![![![-984, 377, 256, -121, -332]]]]
 hle2 := by decide  


def PBC421 : ContainsPrimesAboveP 421 ![I421N0, I421N1, I421N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI421N0
    exact isPrimeI421N1
    exact isPrimeI421N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 421 (by decide) (𝕀 ⊙ MulI421N0 ⊙ MulI421N1)
instance hp431 : Fact (Nat.Prime 431) := {out := by norm_num}

def I431N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![66916, -17026, -15353, 2615, 21780]] i)))

def SI431N0: IdealEqSpanCertificate' Table ![![66916, -17026, -15353, 2615, 21780]] 
 ![![431, 0, 0, 0, 0], ![0, 431, 0, 0, 0], ![0, 0, 431, 0, 0], ![0, 0, 0, 431, 0], ![186, 312, 145, 2, 1]] where
  M :=![![![66916, -17026, -15353, 2615, 21780], ![-38098, 22391, 16074, -4766, -22640], ![32100, 568, -3825, 2236, 7152], ![-17559, 1606, 1473, 1994, -1158], ![7843, -3222, -3727, 3245, 6579]]]
  hmulB := by decide  
  f := ![![![-20, 42, -93, -215, 274]], ![![-870, -1071, 1450, 646, -2268]], ![![6748, 6696, -8191, 548, 9704]], ![![-1923, -1434, 1435, -1792, -444]], ![![1633, 1498, -1750, 555, 1749]]]
  g := ![![![-9244, -15806, -7363, -95, 21780], ![9682, 16441, 7654, 94, -22640], ![-3012, -5176, -2415, -28, 7152], ![459, 842, 393, 10, -1158], ![-2821, -4770, -2222, -23, 6579]]]
  hle1 := by decide   
  hle2 := by decide  


def P431P0 : CertificateIrreducibleZModOfList' 431 4 2 8 [1, 208, 419, 245, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [412, 89, 293, 182], [227, 120, 124, 325], [409, 221, 14, 355], [0, 1]]
 g := ![![[19, 196, 249, 138], [97, 239, 54, 250], [429, 295, 385, 177], [52, 377, 210, 58], [89, 162, 396], [115, 157, 277, 353], [128, 186, 1], []], ![[21, 302, 221, 25, 122, 16], [193, 79, 76, 199, 30, 301], [366, 70, 269, 72, 42, 243], [235, 39, 118, 306, 139, 30], [121, 135, 88], [387, 245, 418, 131, 177, 363], [82, 154, 24], [38, 415, 199, 391, 134, 171]], ![[187, 128, 164, 3, 236, 421], [261, 394, 100, 160, 56, 254], [9, 193, 425, 252, 199, 156], [156, 344, 220, 343, 248, 203], [219, 343, 38], [170, 53, 137, 360, 289, 402], [303, 360, 33], [150, 348, 66, 40, 237, 268]], ![[65, 225, 418, 101, 88, 166], [233, 359, 234, 236, 214, 402], [365, 376, 3, 258, 400, 378], [264, 156, 359, 173, 287, 280], [369, 95, 132], [352, 322, 70, 38, 2, 51], [272, 172, 414], [86, 270, 8, 160, 336, 213]]]
 h' := ![![[412, 89, 293, 182], [334, 277, 195, 210], [2, 239, 332, 326], [379, 211, 123, 311], [206, 425, 132, 244], [316, 65, 26, 62], [303, 343, 344, 403], [0, 0, 0, 1], [0, 1]], ![[227, 120, 124, 325], [290, 62, 330, 17], [150, 52, 410, 299], [120, 339, 301, 347], [429, 65, 411, 235], [375, 420, 136, 281], [350, 173, 8, 390], [430, 144, 0, 256], [412, 89, 293, 182]], ![[409, 221, 14, 355], [193, 281, 99, 67], [188, 430, 90, 356], [344, 323, 353, 158], [303, 60, 105, 186], [301, 362, 148, 401], [273, 321, 80, 319], [24, 115, 385, 372], [227, 120, 124, 325]], ![[0, 1], [116, 242, 238, 137], [268, 141, 30, 312], [325, 420, 85, 46], [110, 312, 214, 197], [144, 15, 121, 118], [116, 25, 430, 181], [41, 172, 46, 233], [409, 221, 14, 355]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [299, 119, 429], []]
 b := ![[], [], [124, 232, 175, 309], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI431N0 : CertifiedPrimeIdeal' SI431N0 431 where
  n := 4
  hpos := by decide
  P := [1, 208, 419, 245, 1]
  hirr := P431P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2077661304378259544, 2064291353314914950, -671769406779377120, 3111227892695290110, 2829424591275213065]
  a := ![-2547, -2778, 1994, -1752, -4457]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1216230423834829166, -2043425014210096430, -953453213785812695, -5910954268805420, 2829424591275213065]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI431N0 : Ideal.IsPrime I431N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI431N0 B_one_repr
lemma NI431N0 : Nat.card (O ⧸ I431N0) = 34507149121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI431N0

def I431N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20, -42, 93, 215, -274]] i)))

def SI431N1: IdealEqSpanCertificate' Table ![![20, -42, 93, 215, -274]] 
 ![![431, 0, 0, 0, 0], ![417, 1, 0, 0, 0], ![235, 0, 1, 0, 0], ![65, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![20, -42, 93, 215, -274], ![870, 1071, -1450, -646, 2268], ![-6748, -6696, 8191, -548, -9704], ![1923, 1434, -1435, 1792, 444], ![-4369, -3926, 4527, -1767, -4279]]]
  hmulB := by decide  
  f := ![![![-66916, 17026, 15353, -2615, -21780]], ![![-64654, 16421, 14817, -2519, -21020]], ![![-36560, 9282, 8380, -1431, -11892]], ![![-10051, 2564, 2312, -399, -3282]], ![![-1105, 284, 258, -50, -369]]]
  g := ![![![-38, -42, 93, 215, -274], ![-183, 1071, -1450, -646, 2268], ![2237, -6696, 8191, -548, -9704], ![-878, 1434, -1435, 1792, 444], ![1656, -3926, 4527, -1767, -4279]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI431N1 : Nat.card (O ⧸ I431N1) = 431 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI431N1)

lemma isPrimeI431N1 : Ideal.IsPrime I431N1 := prime_ideal_of_norm_prime hp431.out _ NI431N1
def MulI431N0 : IdealMulLeCertificate' Table 
  ![![66916, -17026, -15353, 2615, 21780]] ![![20, -42, 93, 215, -274]]
  ![![431, 0, 0, 0, 0]] where
 M := ![![![-431, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC431 : ContainsPrimesAboveP 431 ![I431N0, I431N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI431N0
    exact isPrimeI431N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 431 (by decide) (𝕀 ⊙ MulI431N0)
instance hp433 : Fact (Nat.Prime 433) := {out := by norm_num}

def I433N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16238, -38882, -22161, 12715, 32008]] i)))

def SI433N0: IdealEqSpanCertificate' Table ![![-16238, -38882, -22161, 12715, 32008]] 
 ![![433, 0, 0, 0, 0], ![0, 433, 0, 0, 0], ![0, 0, 433, 0, 0], ![0, 0, 0, 433, 0], ![121, 354, 257, 301, 1]] where
  M :=![![![-16238, -38882, -22161, 12715, 32008], ![-18090, -44175, -25726, 15562, 37704], ![-16700, -46768, -31015, 24044, 49088], ![16345, 35638, 18069, -7124, -23866], ![8751, 16026, 5969, 1121, -5503]]]
  hmulB := by decide  
  f := ![![![834, -298, -247, 59, 350]], ![![-546, 185, 166, -46, -228]], ![![356, -128, -87, 76, 88]], ![![-193, 98, 33, -26, -44]], ![![-136, 60, 38, 6, -67]]]
  g := ![![![-8982, -26258, -19049, -22221, 32008], ![-10578, -30927, -22438, -26174, 37704], ![-13756, -40240, -29207, -34068, 49088], ![6707, 19594, 14207, 16574, -23866], ![1558, 4536, 3280, 3828, -5503]]]
  hle1 := by decide   
  hle2 := by decide  


def P433P0 : CertificateIrreducibleZModOfList' 433 4 2 8 [49, 195, 96, 52, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 42, 115, 208], [429, 94, 38, 217], [324, 296, 280, 8], [0, 1]]
 g := ![![[202, 393, 64, 345], [376, 7, 382], [123, 151, 272], [285, 270, 389], [63, 68, 305, 162], [28, 237, 155, 211], [10, 381, 1], []], ![[282, 278, 389, 207, 100, 288], [184, 186, 3], [306, 203, 246], [274, 365, 389], [431, 158, 138, 115, 150, 74], [384, 407, 274, 102, 116, 158], [99, 335, 293], [381, 377, 177, 346, 246, 306]], ![[106, 238, 378, 138, 30, 22], [285, 325, 337], [86, 148, 127], [101, 236, 169], [23, 217, 76, 411, 276, 398], [241, 195, 131, 302, 102, 429], [19, 54, 109], [198, 412, 64, 431, 22, 379]], ![[162, 309, 114, 59, 7, 137], [11, 289, 74], [358, 145, 148], [297, 253, 139], [211, 245, 273, 239, 164, 25], [190, 230, 120, 148, 96, 277], [284, 162, 234], [152, 180, 320, 176, 290, 79]]]
 h' := ![![[61, 42, 115, 208], [198, 301, 357, 212], [51, 411, 142, 41], [429, 85, 233, 197], [377, 104, 45, 247], [360, 32, 34, 122], [376, 165, 38, 380], [0, 0, 0, 1], [0, 1]], ![[429, 94, 38, 217], [7, 75, 17, 315], [305, 306, 124, 382], [421, 316, 401, 142], [329, 353, 295, 247], [62, 403, 28, 142], [134, 285, 167, 80], [39, 234, 5, 388], [61, 42, 115, 208]], ![[324, 296, 280, 8], [373, 413, 275, 47], [7, 219, 110, 213], [18, 84, 181, 344], [389, 190, 419, 420], [342, 271, 347, 128], [379, 350, 168, 295], [193, 272, 282, 242], [429, 94, 38, 217]], ![[0, 1], [288, 77, 217, 292], [350, 363, 57, 230], [48, 381, 51, 183], [196, 219, 107, 385], [290, 160, 24, 41], [109, 66, 60, 111], [420, 360, 146, 235], [324, 296, 280, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 63, 118], []]
 b := ![[], [], [61, 377, 342, 197], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI433N0 : CertifiedPrimeIdeal' SI433N0 433 where
  n := 4
  hpos := by decide
  P := [49, 195, 96, 52, 1]
  hirr := P433P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18542259519210, 18428808302675, -6009769502360, 27740787279465, 25280481555010]
  a := ![-139, -151, 107, -99, -239]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7021699789000, -20625546563905, -15018691753210, -17509663188865, 25280481555010]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI433N0 : Ideal.IsPrime I433N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI433N0 B_one_repr
lemma NI433N0 : Nat.card (O ⧸ I433N0) = 35152125121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI433N0

def I433N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![834, -298, -247, 59, 350]] i)))

def SI433N1: IdealEqSpanCertificate' Table ![![834, -298, -247, 59, 350]] 
 ![![433, 0, 0, 0, 0], ![192, 1, 0, 0, 0], ![374, 0, 1, 0, 0], ![215, 0, 0, 1, 0], ![182, 0, 0, 0, 1]] where
  M :=![![![834, -298, -247, 59, 350], ![-546, 185, 166, -46, -228], ![356, -128, -87, 76, 88], ![-193, 98, 33, -26, -44], ![83, -54, 3, 37, -21]]]
  hmulB := by decide  
  f := ![![![-16238, -38882, -22161, 12715, 32008]], ![![-7242, -17343, -9886, 5674, 14280]], ![![-14064, -33692, -19213, 11038, 27760]], ![![-8025, -19224, -10962, 6297, 15838]], ![![-6805, -16306, -9301, 5347, 13441]]]
  g := ![![![171, -298, -247, 59, 350], ![-108, 185, 166, -46, -228], ![58, -128, -87, 76, 88], ![-41, 98, 33, -26, -44], ![12, -54, 3, 37, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI433N1 : Nat.card (O ⧸ I433N1) = 433 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI433N1)

lemma isPrimeI433N1 : Ideal.IsPrime I433N1 := prime_ideal_of_norm_prime hp433.out _ NI433N1
def MulI433N0 : IdealMulLeCertificate' Table 
  ![![-16238, -38882, -22161, 12715, 32008]] ![![834, -298, -247, 59, 350]]
  ![![433, 0, 0, 0, 0]] where
 M := ![![![433, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC433 : ContainsPrimesAboveP 433 ![I433N0, I433N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI433N0
    exact isPrimeI433N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 433 (by decide) (𝕀 ⊙ MulI433N0)
instance hp439 : Fact (Nat.Prime 439) := {out := by norm_num}

def I439N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![136, 386, 291, -147, -402]] i)))

def SI439N0: IdealEqSpanCertificate' Table ![![136, 386, 291, -147, -402]] 
 ![![439, 0, 0, 0, 0], ![0, 439, 0, 0, 0], ![0, 0, 439, 0, 0], ![60, 308, 62, 1, 0], ![159, 190, 183, 0, 1]] where
  M :=![![![136, 386, 291, -147, -402], ![354, 601, 170, -18, -372], ![204, 760, -71, -972, 600], ![-475, -730, 271, 248, -392], ![205, 254, -647, -389, 1131]]]
  hmulB := by decide  
  f := ![![![-12848, 4646, 3767, -909, -5352]], ![![8262, -3001, -2422, 570, 3432]], ![![-5388, 1864, 1583, -468, -2304]], ![![3287, -1210, -963, 210, 1354]], ![![-3327, 1162, 977, -278, -1415]]]
  g := ![![![166, 278, 189, -147, -402], ![138, 175, 158, -18, -372], ![-84, 424, -113, -972, 600], ![107, -6, 129, 248, -392], ![-356, -216, -418, -389, 1131]]]
  hle1 := by decide   
  hle2 := by decide  


def P439P0 : CertificateIrreducibleZModOfList' 439 3 2 8 [79, 229, 147, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [204, 178, 116], [88, 260, 323], [0, 1]]
 g := ![![[103, 134, 56], [205, 33, 22], [416, 198, 80], [329, 16], [28, 427, 412], [79, 375, 282], [240, 98], [1]], ![[351, 404, 255, 354], [97, 162, 14, 206], [192, 89, 35, 64], [12, 422], [403, 152, 392, 70], [244, 262, 112, 209], [71, 224], [20, 55, 370, 251]], ![[253, 422, 235, 233], [68, 303, 332, 202], [73, 88, 356, 24], [167, 162], [268, 154, 159, 178], [186, 421, 115, 231], [422, 364], [364, 385, 89, 188]]]
 h' := ![![[204, 178, 116], [48, 264, 94], [61, 252, 30], [199, 310, 117], [422, 49, 435], [344, 279, 151], [12, 259, 385], [360, 210, 292], [0, 1]], ![[88, 260, 323], [376, 47, 189], [237, 171, 156], [251, 97, 91], [245, 193, 254], [425, 128, 67], [20, 103, 200], [19, 180, 188], [204, 178, 116]], ![[0, 1], [385, 128, 156], [331, 16, 253], [257, 32, 231], [104, 197, 189], [153, 32, 221], [248, 77, 293], [362, 49, 398], [88, 260, 323]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [337, 264], []]
 b := ![[], [89, 161, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI439N0 : CertifiedPrimeIdeal' SI439N0 439 where
  n := 3
  hpos := by decide
  P := [79, 229, 147, 1]
  hirr := P439P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1283102445817, 1286088205927, -475047107914, 1820787557449, 1805995343977]
  a := ![1030, 1133, -838, 655, 1873]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-900039659894, -2056163086205, -1011072946737, 1820787557449, 1805995343977]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI439N0 : Ideal.IsPrime I439N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI439N0 B_one_repr
lemma NI439N0 : Nat.card (O ⧸ I439N0) = 84604519 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI439N0

def I439N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12848, -4646, -3767, 909, 5352]] i)))

def SI439N1: IdealEqSpanCertificate' Table ![![12848, -4646, -3767, 909, 5352]] 
 ![![439, 0, 0, 0, 0], ![0, 439, 0, 0, 0], ![192, 134, 1, 0, 0], ![271, 20, 0, 1, 0], ![317, 365, 0, 0, 1]] where
  M :=![![![12848, -4646, -3767, 909, 5352], ![-8262, 3001, 2422, -570, -3432], ![5388, -1864, -1583, 468, 2304], ![-3233, 1210, 947, -186, -1318], ![1497, -482, -441, 167, 665]]]
  hmulB := by decide  
  f := ![![![-136, -386, -291, 147, 402]], ![![-354, -601, -170, 18, 372]], ![![-168, -354, -179, 72, 288]], ![![-99, -264, -188, 91, 266]], ![![-393, -779, -350, 122, 597]]]
  g := ![![![-2749, -3352, -3767, 909, 5352], ![1752, 2147, 2422, -570, -3432], ![-1248, -1458, -1583, 468, 2304], ![645, 818, 947, -186, -1318], ![-387, -427, -441, 167, 665]]]
  hle1 := by decide   
  hle2 := by decide  


def P439P1 : CertificateIrreducibleZModOfList' 439 2 2 8 [209, 311, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [128, 438], [0, 1]]
 g := ![![[54, 418], [188, 122], [189, 146], [109], [14, 38], [338, 88], [234], [128, 1]], ![[0, 21], [0, 317], [0, 293], [109], [49, 401], [188, 351], [234], [256, 438]]]
 h' := ![![[128, 438], [218, 403], [9, 216], [145, 407], [147, 48], [37, 326], [113, 379], [27, 371], [0, 1]], ![[0, 1], [0, 36], [0, 223], [0, 32], [145, 391], [60, 113], [335, 60], [103, 68], [128, 438]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [391]]
 b := ![[], [219, 415]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI439N1 : CertifiedPrimeIdeal' SI439N1 439 where
  n := 2
  hpos := by decide
  P := [209, 311, 1]
  hirr := P439P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1206141, 1054773, 60521, 2586602, 924014]
  a := ![-241, -275, 228, -100, -509]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2287689, -902169, 60521, 2586602, 924014]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI439N1 : Ideal.IsPrime I439N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI439N1 B_one_repr
lemma NI439N1 : Nat.card (O ⧸ I439N1) = 192721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI439N1
def MulI439N0 : IdealMulLeCertificate' Table 
  ![![136, 386, 291, -147, -402]] ![![12848, -4646, -3767, 909, 5352]]
  ![![439, 0, 0, 0, 0]] where
 M := ![![![-439, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC439 : ContainsPrimesAboveP 439 ![I439N0, I439N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI439N0
    exact isPrimeI439N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 439 (by decide) (𝕀 ⊙ MulI439N0)
instance hp443 : Fact (Nat.Prime 443) := {out := by norm_num}

def I443N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23384, 8558, 6917, -1685, -9828]] i)))

def SI443N0: IdealEqSpanCertificate' Table ![![-23384, 8558, 6917, -1685, -9828]] 
 ![![443, 0, 0, 0, 0], ![0, 443, 0, 0, 0], ![254, 265, 1, 0, 0], ![298, 150, 0, 1, 0], ![385, 37, 0, 0, 1]] where
  M :=![![![-23384, 8558, 6917, -1685, -9828], ![15106, -5367, -4358, 1010, 6176], ![-9756, 3532, 2945, -868, -4272], ![5869, -2274, -1771, 374, 2474], ![-2729, 862, 783, -279, -1173]]]
  hmulB := by decide  
  f := ![![![-1720, -1462, 1625, -983, -1278]], ![![3262, 1195, -86, 7310, -5308]], ![![1006, -63, 793, 3744, -3752]], ![![-93, -620, 1115, 1814, -2720]], ![![-1171, -1111, 1326, -270, -1437]]]
  g := ![![![5656, -2727, 6917, -1685, -9828], ![-3514, 1737, -4358, 1010, 6176], ![2586, -1103, 2945, -868, -4272], ![-1373, 721, -1771, 374, 2474], ![752, -274, 783, -279, -1173]]]
  hle1 := by decide   
  hle2 := by decide  


def P443P0 : CertificateIrreducibleZModOfList' 443 2 2 8 [200, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [407, 442], [0, 1]]
 g := ![![[328, 181], [130, 315], [314], [274, 39], [302, 358], [10, 424], [243], [407, 1]], ![[14, 262], [308, 128], [314], [199, 404], [261, 85], [251, 19], [243], [371, 442]]]
 h' := ![![[407, 442], [137, 316], [253, 168], [132, 124], [291, 79], [215, 144], [270, 194], [112, 210], [0, 1]], ![[0, 1], [279, 127], [407, 275], [98, 319], [105, 364], [347, 299], [374, 249], [83, 233], [407, 442]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [225, 234]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI443N0 : CertifiedPrimeIdeal' SI443N0 443 where
  n := 2
  hpos := by decide
  P := [200, 36, 1]
  hirr := P443P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![273236, 171920, 33156, 644992, -107520]
  a := ![98, 126, -136, -32, 304]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-358828, -228860, 33156, 644992, -107520]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI443N0 : Ideal.IsPrime I443N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI443N0 B_one_repr
lemma NI443N0 : Nat.card (O ⧸ I443N0) = 196249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI443N0

def I443N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7175, 15802, 8924, -5108, -12852]] i)))

def SI443N1: IdealEqSpanCertificate' Table ![![7175, 15802, 8924, -5108, -12852]] 
 ![![443, 0, 0, 0, 0], ![0, 443, 0, 0, 0], ![241, 398, 1, 0, 0], ![129, 184, 0, 1, 0], ![194, 374, 0, 0, 1]] where
  M :=![![![7175, 15802, 8924, -5108, -12852], ![7408, 18511, 10530, -5944, -15160], ![9084, 21122, 11967, -6808, -17232], ![-5832, -13576, -7692, 4375, 11076], ![-2104, -5166, -2936, 1660, 4227]]]
  hmulB := by decide  
  f := ![![![77, 42, -48, 92, -52]], ![![-24, 153, -430, -808, 840]], ![![11, 150, -401, -676, 708]], ![![15, 78, -196, -309, 336]], ![![6, 140, -376, -644, 675]]]
  g := ![![![2277, 4990, 8924, -5108, -12852], ![2658, 5849, 10530, -5944, -15160], ![3039, 6672, 11967, -6808, -17232], ![-1953, -4288, -7692, 4375, 11076], ![-742, -1632, -2936, 1660, 4227]]]
  hle1 := by decide   
  hle2 := by decide  


def P443P1 : CertificateIrreducibleZModOfList' 443 2 2 8 [27, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [436, 442], [0, 1]]
 g := ![![[312, 361], [169, 25], [3], [71, 400], [193, 341], [44, 367], [41], [436, 1]], ![[0, 82], [437, 418], [3], [372, 43], [21, 102], [133, 76], [41], [429, 442]]]
 h' := ![![[436, 442], [310, 424], [123, 5], [298, 171], [105, 20], [141, 28], [60, 55], [189, 22], [0, 1]], ![[0, 1], [0, 19], [88, 438], [430, 272], [408, 423], [388, 415], [118, 388], [35, 421], [436, 442]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [383]]
 b := ![[], [338, 413]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI443N1 : CertifiedPrimeIdeal' SI443N1 443 where
  n := 2
  hpos := by decide
  P := [27, 7, 1]
  hirr := P443P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3199032, 3017077, -321356, 5994131, 3528254]
  a := ![374, 413, -313, 219, 701]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3108529, -5172845, -321356, 5994131, 3528254]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI443N1 : Ideal.IsPrime I443N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI443N1 B_one_repr
lemma NI443N1 : Nat.card (O ⧸ I443N1) = 196249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI443N1

def I443N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-847, -2020, -1146, 650, 1650]] i)))

def SI443N2: IdealEqSpanCertificate' Table ![![-847, -2020, -1146, 650, 1650]] 
 ![![443, 0, 0, 0, 0], ![223, 1, 0, 0, 0], ![330, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![214, 0, 0, 0, 1]] where
  M :=![![![-847, -2020, -1146, 650, 1650], ![-976, -2327, -1320, 748, 1900], ![-1128, -2684, -1519, 856, 2184], ![720, 1720, 978, -557, -1410], ![270, 648, 370, -214, -535]]]
  hmulB := by decide  
  f := ![![![7783, -2844, -2250, 586, 3174]], ![![3907, -1427, -1130, 294, 1594]], ![![5802, -2124, -1675, 436, 2364]], ![![242, -88, -70, 19, 98]], ![![3760, -1376, -1086, 282, 1533]]]
  g := ![![![1051, -2020, -1146, 650, 1650], ![1211, -2327, -1320, 748, 1900], ![1398, -2684, -1519, 856, 2184], ![-894, 1720, 978, -557, -1410], ![-336, 648, 370, -214, -535]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI443N2 : Nat.card (O ⧸ I443N2) = 443 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI443N2)

lemma isPrimeI443N2 : Ideal.IsPrime I443N2 := prime_ideal_of_norm_prime hp443.out _ NI443N2
def MulI443N0 : IdealMulLeCertificate' Table 
  ![![-23384, 8558, 6917, -1685, -9828]] ![![7175, 15802, 8924, -5108, -12852]]
  ![![-11043476, 8651052, 6028691, -2200571, -8607872]] where
 M := ![![![-11043476, 8651052, 6028691, -2200571, -8607872]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI443N1 : IdealMulLeCertificate' Table 
  ![![-11043476, 8651052, 6028691, -2200571, -8607872]] ![![-847, -2020, -1146, 650, 1650]]
  ![![443, 0, 0, 0, 0]] where
 M := ![![![-9798502588, -23367066304, -13258217851, 7521089647, 19089941174]]]
 hmul := by decide  
 g := ![![![![-22118516, -52747328, -29928257, 16977629, 43092418]]]]
 hle2 := by decide  


def PBC443 : ContainsPrimesAboveP 443 ![I443N0, I443N1, I443N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI443N0
    exact isPrimeI443N1
    exact isPrimeI443N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 443 (by decide) (𝕀 ⊙ MulI443N0 ⊙ MulI443N1)
instance hp449 : Fact (Nat.Prime 449) := {out := by norm_num}

def I449N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5238, -7560, 10839, 7727, -19100]] i)))

def SI449N0: IdealEqSpanCertificate' Table ![![-5238, -7560, 10839, 7727, -19100]] 
 ![![449, 0, 0, 0, 0], ![0, 449, 0, 0, 0], ![0, 0, 449, 0, 0], ![229, 100, 74, 1, 0], ![285, 7, 86, 0, 1]] where
  M :=![![![-5238, -7560, 10839, 7727, -19100], ![57742, 60765, -76668, -7278, 100016], ![-289088, -254694, 289909, -134444, -258256], ![35657, 8830, 7073, 94500, -78710], ![-146833, -109868, 110277, -135547, -35731]]]
  hmulB := by decide  
  f := ![![![-1478, -1164, -403, 23, 394]], ![![-1538, -3007, -468, -1638, -604]], ![![-10568, -11034, 2337, -13724, -11896]], ![![-2847, -3090, 80, -2631, -1910]], ![![-3001, -2913, 190, -2662, -2059]]]
  g := ![![![8171, -1440, 2409, 7727, -19100], ![-59644, 197, -18128, -7278, 100016], ![231852, 33402, 72269, -134444, -258256], ![1843, -19800, -483, 94500, -78710], ![91485, 30501, 29429, -135547, -35731]]]
  hle1 := by decide   
  hle2 := by decide  


def P449P0 : CertificateIrreducibleZModOfList' 449 3 2 8 [243, 358, 157, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [412, 35, 116], [329, 413, 333], [0, 1]]
 g := ![![[2, 66, 193], [293, 403], [321, 321], [46, 72], [309, 23], [89, 403], [56, 200, 403], [1]], ![[160, 18, 20, 155], [165, 321], [14, 293], [342, 392], [74, 118], [387, 349], [353, 60, 420, 76], [149, 68, 262, 172]], ![[106, 38, 167, 317], [72, 390], [61, 442], [86, 351], [12, 164], [181, 102], [101, 425, 92, 47], [193, 368, 229, 277]]]
 h' := ![![[412, 35, 116], [25, 135, 174], [103, 48, 157], [352, 350, 84], [94, 44, 180], [111, 194, 186], [311, 279, 157], [206, 91, 292], [0, 1]], ![[329, 413, 333], [440, 364, 416], [308, 132, 365], [93, 437, 309], [68, 280, 420], [156, 100, 93], [51, 135, 221], [246, 243, 44], [412, 35, 116]], ![[0, 1], [283, 399, 308], [244, 269, 376], [189, 111, 56], [181, 125, 298], [292, 155, 170], [121, 35, 71], [447, 115, 113], [329, 413, 333]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 169], []]
 b := ![[], [431, 87, 374], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI449N0 : CertifiedPrimeIdeal' SI449N0 449 where
  n := 3
  hpos := by decide
  P := [243, 358, 157, 1]
  hirr := P449P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1189962463, -1184469488, 421416376, -1722662004, -1634140508]
  a := ![-100, -107, 72, -79, -161]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1913206417, 406504932, 597849640, -1722662004, -1634140508]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI449N0 : Ideal.IsPrime I449N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI449N0 B_one_repr
lemma NI449N0 : Nat.card (O ⧸ I449N0) = 90518849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI449N0

def I449N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2239, -797, -657, 172, 942]] i)))

def SI449N1: IdealEqSpanCertificate' Table ![![2239, -797, -657, 172, 942]] 
 ![![449, 0, 0, 0, 0], ![83, 1, 0, 0, 0], ![295, 0, 1, 0, 0], ![395, 0, 0, 1, 0], ![119, 0, 0, 0, 1]] where
  M :=![![![2239, -797, -657, 172, 942], ![-1370, 584, 399, -4, -508], ![1362, 101, -416, 716, 984], ![-354, 416, 96, 275, 54], ![558, 213, -175, 472, 523]]]
  hmulB := by decide  
  f := ![![![1079, 1119, -1839, -412, 2646]], ![![183, 191, -322, -80, 470]], ![![763, 774, -1247, -216, 1746]], ![![955, 997, -1637, -385, 2368]], ![![303, 302, -486, -68, 669]]]
  g := ![![![183, -797, -657, 172, 942], ![-235, 584, 399, -4, -508], ![-633, 101, -416, 716, 984], ![-397, 416, 96, 275, 54], ![-477, 213, -175, 472, 523]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI449N1 : Nat.card (O ⧸ I449N1) = 449 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI449N1)

lemma isPrimeI449N1 : Ideal.IsPrime I449N1 := prime_ideal_of_norm_prime hp449.out _ NI449N1

def I449N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![654, 1561, 886, -503, -1276]] i)))

def SI449N2: IdealEqSpanCertificate' Table ![![654, 1561, 886, -503, -1276]] 
 ![![449, 0, 0, 0, 0], ![376, 1, 0, 0, 0], ![59, 0, 1, 0, 0], ![315, 0, 0, 1, 0], ![112, 0, 0, 0, 1]] where
  M :=![![![654, 1561, 886, -503, -1276], ![752, 1796, 1021, -582, -1472], ![854, 2057, 1180, -688, -1712], ![-565, -1338, -753, 418, 1078], ![-221, -513, -282, 147, 397]]]
  hmulB := by decide  
  f := ![![![-1122, 517, 194, -247, -182]], ![![-940, 430, 165, -206, -156]], ![![-136, 80, 12, -29, -10]], ![![-789, 361, 137, -177, -126]], ![![-273, 135, 42, -57, -41]]]
  g := ![![![-751, 1561, 886, -503, -1276], ![-861, 1796, 1021, -582, -1472], ![-966, 2057, 1180, -688, -1712], ![656, -1338, -753, 418, 1078], ![264, -513, -282, 147, 397]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI449N2 : Nat.card (O ⧸ I449N2) = 449 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI449N2)

lemma isPrimeI449N2 : Ideal.IsPrime I449N2 := prime_ideal_of_norm_prime hp449.out _ NI449N2
def MulI449N0 : IdealMulLeCertificate' Table 
  ![![-5238, -7560, 10839, 7727, -19100]] ![![2239, -797, -657, 172, 942]]
  ![![-1122, 517, 194, -247, -182]] where
 M := ![![![-1122, 517, 194, -247, -182]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI449N1 : IdealMulLeCertificate' Table 
  ![![-1122, 517, 194, -247, -182]] ![![654, 1561, 886, -503, -1276]]
  ![![449, 0, 0, 0, 0]] where
 M := ![![![449, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC449 : ContainsPrimesAboveP 449 ![I449N0, I449N1, I449N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI449N0
    exact isPrimeI449N1
    exact isPrimeI449N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 449 (by decide) (𝕀 ⊙ MulI449N0 ⊙ MulI449N1)
instance hp457 : Fact (Nat.Prime 457) := {out := by norm_num}

def I457N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4153, -9952, -5648, 3202, 8132]] i)))

def SI457N0: IdealEqSpanCertificate' Table ![![-4153, -9952, -5648, 3202, 8132]] 
 ![![457, 0, 0, 0, 0], ![0, 457, 0, 0, 0], ![91, 293, 1, 0, 0], ![254, 204, 0, 1, 0], ![404, 311, 0, 0, 1]] where
  M :=![![![-4153, -9952, -5648, 3202, 8132], ![-4816, -11453, -6496, 3684, 9352], ![-5536, -13208, -7485, 4232, 10768], ![3546, 8476, 4814, -2737, -6936], ![1338, 3196, 1820, -1042, -2627]]]
  hmulB := by decide  
  f := ![![![-157, -168, 180, -66, -172]], ![![472, 307, -248, 652, -184]], ![![273, 167, -129, 398, -140]], ![![120, 40, -6, 255, -184]], ![![186, 65, -16, 382, -267]]]
  g := ![![![-7853, -3364, -5648, 3202, 8132], ![-9032, -3869, -6496, 3684, 9352], ![-10393, -4447, -7485, 4232, 10768], ![6702, 2874, 4814, -2737, -6936], ![2542, 1093, 1820, -1042, -2627]]]
  hle1 := by decide   
  hle2 := by decide  


def P457P0 : CertificateIrreducibleZModOfList' 457 2 2 8 [82, 282, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [175, 456], [0, 1]]
 g := ![![[427, 242], [232], [94], [209, 408], [19], [262], [312, 292], [175, 1]], ![[276, 215], [232], [94], [317, 49], [19], [262], [228, 165], [350, 456]]]
 h' := ![![[175, 456], [237, 34], [404, 193], [228, 262], [95, 306], [59, 48], [8, 165], [274, 381], [0, 1]], ![[0, 1], [246, 423], [361, 264], [378, 195], [176, 151], [233, 409], [92, 292], [227, 76], [175, 456]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [176]]
 b := ![[], [69, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI457N0 : CertifiedPrimeIdeal' SI457N0 457 where
  n := 2
  hpos := by decide
  P := [82, 282, 1]
  hirr := P457P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2471747, 2291744, -218280, 4692926, 2534699]
  a := ![325, 365, -289, 164, 647]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4800189, -3674837, -218280, 4692926, 2534699]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI457N0 : Ideal.IsPrime I457N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI457N0 B_one_repr
lemma NI457N0 : Nat.card (O ⧸ I457N0) = 208849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI457N0

def I457N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-70, -164, -93, 53, 134]] i)))

def SI457N1: IdealEqSpanCertificate' Table ![![-70, -164, -93, 53, 134]] 
 ![![457, 0, 0, 0, 0], ![324, 1, 0, 0, 0], ![134, 0, 1, 0, 0], ![132, 0, 0, 1, 0], ![239, 0, 0, 0, 1]] where
  M :=![![![-70, -164, -93, 53, 134], ![-78, -189, -108, 62, 156], ![-88, -214, -125, 76, 184], ![61, 142, 79, -42, -112], ![25, 56, 29, -13, -39]]]
  hmulB := by decide  
  f := ![![![-326, 88, 137, 37, -228]], ![![-230, 63, 96, 26, -160]], ![![-100, 22, 45, 10, -72]], ![![-93, 26, 39, 12, -66]], ![![-173, 44, 74, 18, -121]]]
  g := ![![![58, -164, -93, 53, 134], ![66, -189, -108, 62, 156], ![70, -214, -125, 76, 184], ![-53, 142, 79, -42, -112], ![-24, 56, 29, -13, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI457N1 : Nat.card (O ⧸ I457N1) = 457 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI457N1)

lemma isPrimeI457N1 : Ideal.IsPrime I457N1 := prime_ideal_of_norm_prime hp457.out _ NI457N1

def I457N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1064, -1171, 1510, 311, -2094]] i)))

def SI457N2: IdealEqSpanCertificate' Table ![![-1064, -1171, 1510, 311, -2094]] 
 ![![457, 0, 0, 0, 0], ![347, 1, 0, 0, 0], ![239, 0, 1, 0, 0], ![333, 0, 0, 1, 0], ![329, 0, 0, 0, 1]] where
  M :=![![![-1064, -1171, 1510, 311, -2094], ![6116, 5636, -6603, 1990, 6676], ![-18306, -12263, 11028, -21848, 2568], ![-3357, -5762, 8685, 8114, -16728], ![-4451, 51, -3070, -15775, 15471]]]
  hmulB := by decide  
  f := ![![![39632, 16017, 6102, -5449, -8452]], ![![30088, 12249, 4679, -4149, -6476]], ![![20838, 8496, 3208, -2791, -4396]], ![![28869, 11655, 4415, -3917, -6090]], ![![28569, 11548, 4368, -3860, -6015]]]
  g := ![![![1378, -1171, 1510, 311, -2094], ![-7069, 5636, -6603, 1990, 6676], ![17575, -12263, 11028, -21848, 2568], ![5956, -5762, 8685, 8114, -16728], ![1914, 51, -3070, -15775, 15471]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI457N2 : Nat.card (O ⧸ I457N2) = 457 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI457N2)

lemma isPrimeI457N2 : Ideal.IsPrime I457N2 := prime_ideal_of_norm_prime hp457.out _ NI457N2

def I457N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1135, 403, 333, -88, -478]] i)))

def SI457N3: IdealEqSpanCertificate' Table ![![-1135, 403, 333, -88, -478]] 
 ![![457, 0, 0, 0, 0], ![407, 1, 0, 0, 0], ![242, 0, 1, 0, 0], ![268, 0, 0, 1, 0], ![155, 0, 0, 0, 1]] where
  M :=![![![-1135, 403, 333, -88, -478], ![690, -300, -201, -4, 252], ![-718, -79, 220, -404, -536], ![166, -224, -44, -159, -46], ![-302, -127, 95, -268, -291]]]
  hmulB := by decide  
  f := ![![![12169, 29047, 16559, -9320, -23862]], ![![10869, 25943, 14788, -8324, -21310]], ![![6476, 15463, 8820, -4964, -12708]], ![![7114, 16980, 9680, -5447, -13950]], ![![4117, 9830, 5606, -3156, -8077]]]
  g := ![![![-324, 403, 333, -88, -478], ![292, -300, -201, -4, 252], ![371, -79, 220, -404, -536], ![332, -224, -44, -159, -46], ![318, -127, 95, -268, -291]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI457N3 : Nat.card (O ⧸ I457N3) = 457 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI457N3)

lemma isPrimeI457N3 : Ideal.IsPrime I457N3 := prime_ideal_of_norm_prime hp457.out _ NI457N3
def MulI457N0 : IdealMulLeCertificate' Table 
  ![![-4153, -9952, -5648, 3202, 8132]] ![![-70, -164, -93, 53, 134]]
  ![![1962612, 4680768, 2655831, -1506581, -3824018]] where
 M := ![![![1962612, 4680768, 2655831, -1506581, -3824018]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI457N1 : IdealMulLeCertificate' Table 
  ![![1962612, 4680768, 2655831, -1506581, -3824018]] ![![-1064, -1171, 1510, 311, -2094]]
  ![![12169, 29047, 16559, -9320, -23862]] where
 M := ![![![12169, 29047, 16559, -9320, -23862]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI457N2 : IdealMulLeCertificate' Table 
  ![![12169, 29047, 16559, -9320, -23862]] ![![-1135, 403, 333, -88, -478]]
  ![![457, 0, 0, 0, 0]] where
 M := ![![![457, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC457 : ContainsPrimesAboveP 457 ![I457N0, I457N1, I457N2, I457N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI457N0
    exact isPrimeI457N1
    exact isPrimeI457N2
    exact isPrimeI457N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 457 (by decide) (𝕀 ⊙ MulI457N0 ⊙ MulI457N1 ⊙ MulI457N2)
instance hp461 : Fact (Nat.Prime 461) := {out := by norm_num}

def I461N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7585, 3384, 2206, 132, -2710]] i)))

def SI461N0: IdealEqSpanCertificate' Table ![![-7585, 3384, 2206, 132, -2710]] 
 ![![461, 0, 0, 0, 0], ![0, 461, 0, 0, 0], ![0, 0, 461, 0, 0], ![53, 264, 39, 1, 0], ![143, 426, 392, 0, 1]] where
  M :=![![![-7585, 3384, 2206, 132, -2710], ![8344, 1263, -2564, 5056, 6476], ![17792, 22224, -6009, 31152, 27496], ![12278, 9436, -3984, 15341, 14842], ![13840, 15000, -4610, 21848, 19785]]]
  hmulB := by decide  
  f := ![![![1387, 3304, 1862, -1068, -2678]], ![![1544, 3747, 2220, -1216, -3188]], ![![2080, 4592, 2235, -1296, -3352]], ![![1217, 2908, 1671, -927, -2412]], ![![3625, 8390, 4528, -2556, -6625]]]
  g := ![![![809, 2436, 2298, 132, -2710], ![-2572, -8877, -5940, 5056, 6476], ![-12072, -43200, -26029, 31152, 27496], ![-6341, -22480, -13927, 15341, 14842], ![-8619, -30762, -18682, 21848, 19785]]]
  hle1 := by decide   
  hle2 := by decide  


def P461P0 : CertificateIrreducibleZModOfList' 461 3 2 8 [33, 123, 254, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [394, 258, 268], [274, 202, 193], [0, 1]]
 g := ![![[16, 351, 64], [286, 452], [98, 109, 431], [432, 99, 23], [31, 88], [129, 237], [296, 352, 437], [1]], ![[144, 315, 108, 452], [60, 442], [449, 375, 82, 41], [102, 359, 355, 381], [452, 387], [85, 85], [357, 288, 453, 54], [452, 26, 186, 238]], ![[136, 362, 323, 348], [280, 167], [446, 107, 173, 143], [9, 85, 95, 262], [435, 181], [371, 87], [86, 176, 300, 114], [112, 128, 90, 223]]]
 h' := ![![[394, 258, 268], [292, 201, 453], [454, 326, 144], [35, 186, 390], [209, 376, 22], [85, 359, 114], [374, 87, 148], [428, 338, 207], [0, 1]], ![[274, 202, 193], [349, 418, 159], [255, 438, 284], [416, 365, 9], [61, 131, 104], [446, 452, 302], [206, 454, 197], [106, 178, 91], [394, 258, 268]], ![[0, 1], [207, 303, 310], [212, 158, 33], [162, 371, 62], [333, 415, 335], [384, 111, 45], [258, 381, 116], [74, 406, 163], [274, 202, 193]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 212], []]
 b := ![[], [207, 399, 357], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI461N0 : CertifiedPrimeIdeal' SI461N0 461 where
  n := 3
  hpos := by decide
  P := [33, 123, 254, 1]
  hirr := P461P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8167573306, 8287241673, -3136205984, 11367968403, 11981571234]
  a := ![194, 219, -176, 93, 393]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5005855615, -17564003823, -11156752489, 11367968403, 11981571234]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI461N0 : Ideal.IsPrime I461N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI461N0 B_one_repr
lemma NI461N0 : Nat.card (O ⧸ I461N0) = 97972181 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI461N0

def I461N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![430, -3739, -2534, 1683, 3912]] i)))

def SI461N1: IdealEqSpanCertificate' Table ![![430, -3739, -2534, 1683, 3912]] 
 ![![461, 0, 0, 0, 0], ![145, 1, 0, 0, 0], ![181, 0, 1, 0, 0], ![58, 0, 0, 1, 0], ![451, 0, 0, 0, 1]] where
  M :=![![![430, -3739, -2534, 1683, 3912], ![-648, -1596, -2647, 4254, 5640], ![12414, 8773, -7332, 21864, 22752], ![7469, 9698, -395, 8866, 6478], ![10205, 10559, -2578, 13849, 12227]]]
  hmulB := by decide  
  f := ![![![498782, 343493, -318238, 562983, -24126]], ![![157522, 110503, -104341, 170817, 2286]], ![![165076, 99114, -77696, 236583, -79302]], ![![79115, 58304, -57723, 76118, 14876]], ![![461491, 308666, -277100, 552446, -67097]]]
  g := ![![![-1867, -3739, -2534, 1683, 3912], ![-4513, -1596, -2647, 4254, 5640], ![-24863, 8773, -7332, 21864, 22752], ![-10332, 9698, -395, 8866, 6478], ![-15991, 10559, -2578, 13849, 12227]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI461N1 : Nat.card (O ⧸ I461N1) = 461 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI461N1)

lemma isPrimeI461N1 : Ideal.IsPrime I461N1 := prime_ideal_of_norm_prime hp461.out _ NI461N1

def I461N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 6, -5, 9, 2]] i)))

def SI461N2: IdealEqSpanCertificate' Table ![![8, 6, -5, 9, 2]] 
 ![![461, 0, 0, 0, 0], ![309, 1, 0, 0, 0], ![407, 0, 1, 0, 0], ![225, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![8, 6, -5, 9, 2], ![10, 21, -26, -26, 68], ![-124, -156, 261, 180, -344], ![125, 118, -117, 68, 148], ![-119, -126, 193, 71, -213]]]
  hmulB := by decide  
  f := ![![![81976, -34274, -26803, 7197, 38116]], ![![54826, -22941, -17937, 4819, 25508]], ![![72444, -30298, -23692, 6363, 33692]], ![![39967, -16704, -13064, 3507, 18578]], ![![733, -302, -237, 63, 337]]]
  g := ![![![-4, 6, -5, 9, 2], ![21, 21, -26, -26, 68], ![-211, -156, 261, 180, -344], ![-10, 118, -117, 68, 148], ![-119, -126, 193, 71, -213]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI461N2 : Nat.card (O ⧸ I461N2) = 461 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI461N2)

lemma isPrimeI461N2 : Ideal.IsPrime I461N2 := prime_ideal_of_norm_prime hp461.out _ NI461N2
def MulI461N0 : IdealMulLeCertificate' Table 
  ![![-7585, 3384, 2206, 132, -2710]] ![![430, -3739, -2534, 1683, 3912]]
  ![![-4738740, 14977935, 1022790, 13501487, 7324078]] where
 M := ![![![-4738740, 14977935, 1022790, 13501487, 7324078]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI461N1 : IdealMulLeCertificate' Table 
  ![![-4738740, 14977935, 1022790, 13501487, 7324078]] ![![8, 6, -5, 9, 2]]
  ![![461, 0, 0, 0, 0]] where
 M := ![![![801164063, 796890593, -264911345, 1190137884, 1095373802]]]
 hmul := by decide  
 g := ![![![![1737883, 1728613, -574645, 2581644, 2376082]]]]
 hle2 := by decide  


def PBC461 : ContainsPrimesAboveP 461 ![I461N0, I461N1, I461N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI461N0
    exact isPrimeI461N1
    exact isPrimeI461N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 461 (by decide) (𝕀 ⊙ MulI461N0 ⊙ MulI461N1)
instance hp463 : Fact (Nat.Prime 463) := {out := by norm_num}

def I463N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![463, 0, 0, 0, 0]] i)))

def SI463N0: IdealEqSpanCertificate' Table ![![463, 0, 0, 0, 0]] 
 ![![463, 0, 0, 0, 0], ![0, 463, 0, 0, 0], ![0, 0, 463, 0, 0], ![0, 0, 0, 463, 0], ![0, 0, 0, 0, 463]] where
  M :=![![![463, 0, 0, 0, 0], ![0, 463, 0, 0, 0], ![0, 0, 463, 0, 0], ![0, 0, 0, 463, 0], ![0, 0, 0, 0, 463]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P463P0 : CertificateIrreducibleZModOfList' 463 5 2 8 [418, 287, 50, 448, 76, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [375, 92, 115, 290, 328], [234, 287, 89, 445, 233], [323, 207, 22, 443, 177], [381, 339, 237, 211, 188], [0, 1]]
 g := ![![[317, 30, 332, 98, 143], [388, 413, 336, 118, 370], [68, 145, 314, 82, 94], [419, 178, 147, 29, 265], [32, 349, 396, 15], [288, 267, 106, 322], [235, 387, 1], []], ![[109, 193, 322, 416, 118, 194, 190, 126], [214, 439, 229, 302, 269, 1, 132, 96], [114, 68, 458, 441, 33, 25, 227, 171], [248, 355, 87, 377, 280, 436, 325, 295], [150, 236, 272, 228], [294, 190, 169, 222], [225, 349, 239, 133, 345, 181, 212, 254], [36, 389, 442, 36, 1, 109, 246, 7]], ![[462, 291, 78, 243, 92, 207, 387, 401], [83, 422, 201, 378, 387, 217, 146, 442], [199, 150, 359, 419, 16, 103, 362, 254], [283, 436, 8, 142, 277, 88, 306, 391], [453, 304, 49, 225], [2, 115, 336, 21], [116, 166, 10, 440, 247, 134, 30, 333], [146, 370, 97, 112, 453, 453, 85, 177]], ![[195, 273, 132, 262, 353, 156, 244, 296], [254, 430, 443, 328, 444, 172, 144, 282], [267, 75, 105, 323, 437, 76, 105, 105], [113, 259, 234, 397, 69, 384, 254, 119], [421, 295, 62, 220], [26, 192, 290, 322], [389, 83, 190, 409, 28, 303, 139, 26], [355, 196, 400, 170, 180, 90, 211, 345]], ![[128, 97, 199, 171, 59, 459, 164, 133], [288, 176, 107, 404, 346, 3, 312, 16], [126, 349, 404, 436, 199, 228, 410, 407], [33, 62, 408, 438, 62, 146, 147, 59], [82, 309, 385, 303], [165, 136, 314, 367], [111, 29, 333, 409, 235, 148, 275, 220], [387, 264, 342, 308, 433, 5, 83, 159]]]
 h' := ![![[375, 92, 115, 290, 328], [329, 180, 420, 109, 148], [282, 152, 230, 225, 36], [335, 119, 94, 60, 284], [162, 458, 343, 336, 400], [379, 342, 189, 107, 362], [389, 437, 384, 93, 396], [0, 0, 0, 1], [0, 1]], ![[234, 287, 89, 445, 233], [39, 24, 103, 358, 264], [34, 269, 260, 108, 48], [10, 180, 435, 365, 443], [349, 177, 334, 448, 160], [9, 191, 231, 346, 368], [222, 166, 461, 235, 384], [295, 364, 85, 256, 143], [375, 92, 115, 290, 328]], ![[323, 207, 22, 443, 177], [305, 48, 64, 154, 439], [61, 0, 141, 414, 273], [297, 167, 347, 32, 362], [257, 33, 214, 437, 291], [187, 222, 2, 371, 15], [339, 83, 71, 86, 22], [393, 154, 201, 433, 384], [234, 287, 89, 445, 233]], ![[381, 339, 237, 211, 188], [400, 6, 224, 86, 234], [163, 435, 188, 326, 160], [88, 202, 454, 23, 337], [369, 53, 357, 221, 452], [380, 169, 289, 115, 387], [236, 248, 279, 140, 396], [434, 254, 229, 439, 299], [323, 207, 22, 443, 177]], ![[0, 1], [54, 205, 115, 219, 304], [86, 70, 107, 316, 409], [77, 258, 59, 446, 426], [322, 205, 141, 410, 86], [375, 2, 215, 450, 257], [56, 455, 194, 372, 191], [349, 154, 411, 260, 100], [381, 339, 237, 211, 188]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [408, 375, 151, 354], [], [], []]
 b := ![[], [207, 227, 94, 384, 301], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI463N0 : CertifiedPrimeIdeal' SI463N0 463 where
  n := 5
  hpos := by decide
  P := [418, 287, 50, 448, 76, 1]
  hirr := P463P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![156492372737807216, 155764474634254144, -52143980744292540, 231762596005925920, 214576621906453472]
  a := ![151, 167, -127, 88, 284]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![337996485394832, 336424351261888, -112621988648580, 500567161999840, 463448427443744]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI463N0 : Ideal.IsPrime I463N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI463N0 B_one_repr
lemma NI463N0 : Nat.card (O ⧸ I463N0) = 21276733558543 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI463N0

def PBC463 : ContainsPrimesAboveP 463 ![I463N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI463N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![463, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 463 (by decide) 𝕀



lemma PB1640I9_primes (p : ℕ) :
  p ∈ Set.range ![421, 431, 433, 439, 443, 449, 457, 461, 463] ↔ Nat.Prime p ∧ 419 < p ∧ p ≤ 463 := by
  rw [← List.mem_ofFn']
  convert primes_range 419 463 (by omega)

def PB1640I9 : PrimesBelowBoundCertificateInterval O 419 463 1640 where
  m := 9
  g := ![3, 2, 2, 2, 3, 3, 4, 3, 1]
  P := ![421, 431, 433, 439, 443, 449, 457, 461, 463]
  hP := PB1640I9_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I421N0, I421N1, I421N2]
    · exact ![I431N0, I431N1]
    · exact ![I433N0, I433N1]
    · exact ![I439N0, I439N1]
    · exact ![I443N0, I443N1, I443N2]
    · exact ![I449N0, I449N1, I449N2]
    · exact ![I457N0, I457N1, I457N2, I457N3]
    · exact ![I461N0, I461N1, I461N2]
    · exact ![I463N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC421
    · exact PBC431
    · exact PBC433
    · exact PBC439
    · exact PBC443
    · exact PBC449
    · exact PBC457
    · exact PBC461
    · exact PBC463
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![74618461, 421, 421]
    · exact ![34507149121, 431]
    · exact ![35152125121, 433]
    · exact ![84604519, 192721]
    · exact ![196249, 196249, 443]
    · exact ![90518849, 449, 449]
    · exact ![208849, 457, 457, 457]
    · exact ![97972181, 461, 461]
    · exact ![21276733558543]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI421N0
      exact NI421N1
      exact NI421N2
    · dsimp ; intro j
      fin_cases j
      exact NI431N0
      exact NI431N1
    · dsimp ; intro j
      fin_cases j
      exact NI433N0
      exact NI433N1
    · dsimp ; intro j
      fin_cases j
      exact NI439N0
      exact NI439N1
    · dsimp ; intro j
      fin_cases j
      exact NI443N0
      exact NI443N1
      exact NI443N2
    · dsimp ; intro j
      fin_cases j
      exact NI449N0
      exact NI449N1
      exact NI449N2
    · dsimp ; intro j
      fin_cases j
      exact NI457N0
      exact NI457N1
      exact NI457N2
      exact NI457N3
    · dsimp ; intro j
      fin_cases j
      exact NI461N0
      exact NI461N1
      exact NI461N2
    · dsimp ; intro j
      fin_cases j
      exact NI463N0
  β := ![I421N1, I421N2, I431N1, I433N1, I443N2, I449N1, I449N2, I457N1, I457N2, I457N3, I461N1, I461N2]
  Il := ![[I421N1, I421N2], [I431N1], [I433N1], [], [I443N2], [I449N1, I449N2], [I457N1, I457N2, I457N3], [I461N1, I461N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
