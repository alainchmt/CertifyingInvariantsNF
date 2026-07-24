
import IdealArithmetic.Examples.NF5_3_303750000_1.RI5_3_303750000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -165, -7, 29, -4]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![5, -165, -7, 29, -4]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![0, 0, 311, 0, 0], ![0, 0, 0, 311, 0], ![232, 119, 235, 226, 1]] where
  M :=![![![5, -165, -7, 29, -4], ![-280, -90, -541, -69, 224], ![100, 432, 171, -42, -80], ![440, 97, 939, 64, -352], ![116, -407, 273, 113, -155]]]
  hmulB := by decide  
  f := ![![![23, 1, 5, 1, -4]], ![![-4, -2, -1, -1, 0]], ![![-12, -2, -5, 0, 0]], ![![-20, -13, -9, -6, 0]], ![![-8, -11, -7, -4, -3]]]
  g := ![![![3, 1, 3, 3, -4], ![-168, -86, -171, -163, 224], ![60, 32, 61, 58, -80], ![264, 135, 269, 256, -352], ![116, 58, 118, 113, -155]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 4 2 8 [100, 258, 12, 298, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [155, 109, 200, 60], [88, 43, 168, 209], [81, 158, 254, 42], [0, 1]]
 g := ![![[14, 88, 156, 240], [59, 4, 253, 32], [297, 191, 15, 109], [149, 130, 234], [123, 6, 183, 265], [246, 52, 19, 169], [1], []], ![[148, 274, 260, 219, 151, 40], [74, 26, 91, 90, 225, 84], [95, 149, 75, 189, 213, 268], [9, 67, 219], [161, 145, 95, 21, 46, 268], [285, 62, 117, 207, 88, 120], [167, 273, 64], [79, 203, 179]], ![[57, 14, 58, 1, 288, 169], [49, 106, 162, 95, 8, 254], [15, 2, 269, 268, 49, 234], [116, 221, 2], [122, 120, 279, 185, 57, 249], [204, 164, 114, 87, 1, 188], [32, 46, 139], [42, 216, 141]], ![[67, 47, 87, 137, 50, 156], [181, 102, 110, 60, 266, 105], [266, 229, 29, 199, 93, 135], [176, 59, 56], [20, 290, 7, 65, 182, 60], [76, 283, 64, 182, 118, 126], [269, 298, 224], [152, 106, 209]]]
 h' := ![![[155, 109, 200, 60], [9, 6, 60, 193], [156, 43, 167, 47], [35, 250, 105, 174], [140, 38, 95, 168], [280, 111, 55, 287], [211, 53, 299, 13], [0, 0, 1], [0, 1]], ![[88, 43, 168, 209], [157, 4, 201, 72], [274, 8, 181, 166], [40, 249, 213, 98], [171, 279, 188, 29], [260, 70, 197, 213], [126, 246, 266, 245], [264, 261, 171, 303], [155, 109, 200, 60]], ![[81, 158, 254, 42], [107, 185, 19, 170], [34, 255, 264, 280], [80, 33, 297, 4], [22, 229, 48, 245], [228, 243, 194, 306], [111, 48, 228, 78], [123, 12, 271, 57], [88, 43, 168, 209]], ![[0, 1], [36, 116, 31, 187], [155, 5, 10, 129], [207, 90, 7, 35], [154, 76, 291, 180], [223, 198, 176, 127], [253, 275, 140, 286], [69, 38, 179, 262], [81, 158, 254, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [265, 139, 247], []]
 b := ![[], [], [282, 224, 249, 225], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 4
  hpos := by decide
  P := [100, 258, 12, 298, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![292302440986, 356544488802, 442611581934, 22051475745, 302558613342]
  a := ![-20, -41, -39, 24, -100]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-224763009178, -114623570736, -227198271876, -219794839677, 302558613342]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 9354951841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 1, 5, 1, -4]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![23, 1, 5, 1, -4]] 
 ![![311, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![291, 0, 1, 0, 0], ![223, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![23, 1, 5, 1, -4], ![-4, -2, -1, -1, 0], ![-12, -2, -5, 0, 0], ![-20, -13, -9, -6, 0], ![-8, -7, -9, -1, -5]]]
  hmulB := by decide  
  f := ![![![5, -165, -7, 29, -4]], ![![0, -30, -3, 5, 0]], ![![5, -153, -6, 27, -4]], ![![5, -118, -2, 21, -4]], ![![1, -22, 0, 4, -1]]]
  g := ![![![-5, 1, 5, 1, -4], ![2, -2, -1, -1, 0], ![5, -2, -5, 0, 0], ![15, -13, -9, -6, 0], ![11, -7, -9, -1, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N1 : Nat.card (O ⧸ I311N1) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N1)

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := prime_ideal_of_norm_prime hp311.out _ NI311N1
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![5, -165, -7, 29, -4]] ![![23, 1, 5, 1, -4]]
  ![![311, 0, 0, 0, 0]] where
 M := ![![![311, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC311 : ContainsPrimesAboveP 311 ![I311N0, I311N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI311N0
    exact isPrimeI311N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 311 (by decide) (𝕀 ⊙ MulI311N0)
instance hp313 : Fact (Nat.Prime 313) := {out := by norm_num}

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-393, -63, -185, -1, 170]] i)))

def SI313N0: IdealEqSpanCertificate' Table ![![-393, -63, -185, -1, 170]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![0, 0, 313, 0, 0], ![0, 0, 0, 313, 0], ![110, 204, 137, 197, 1]] where
  M :=![![![-393, -63, -185, -1, 170], ![212, 746, 99, -13, 332], ![676, 548, 859, 118, -28], ![2164, 1845, 2735, 700, 1192], ![1156, 1239, 1343, 437, 1143]]]
  hmulB := by decide  
  f := ![![![-29, 105, -267, 193, -234]], ![![128, -482, 1225, -887, 1076]], ![![-164, 622, -1579, 1144, -1388]], ![![720, -2719, 6901, -4998, 6064]], ![![454, -1714, 4351, -3151, 3823]]]
  g := ![![![-61, -111, -75, -107, 170], ![-116, -214, -145, -209, 332], ![12, 20, 15, 18, -28], ![-412, -771, -513, -748, 1192], ![-398, -741, -496, -718, 1143]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P0 : CertificateIrreducibleZModOfList' 313 4 2 8 [8, 179, 263, 128, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [290, 270, 122, 75], [78, 288, 97, 63], [130, 67, 94, 175], [0, 1]]
 g := ![![[42, 237, 24, 238], [284, 45, 305], [297, 70, 217], [189, 175, 258, 128], [115, 232, 200, 192], [251, 129, 294, 108], [1], []], ![[276, 145, 104, 54, 94, 300], [6, 66, 171], [184, 217, 24], [45, 170, 243, 174, 197, 75], [139, 141, 52, 127, 94, 113], [50, 79, 72, 35, 14, 281], [132, 26, 88], [218, 46, 304]], ![[100, 39, 166, 165, 158, 231], [247, 302, 281], [256, 214, 147], [104, 97, 49, 264, 11, 46], [191, 254, 175, 122, 81, 172], [178, 143, 109, 283, 85, 279], [208, 118, 147], [120, 295, 213]], ![[186, 108, 134, 102, 165, 266], [206, 108, 209], [267, 237, 173], [300, 5, 279, 191, 86, 131], [97, 174, 22, 75, 59, 283], [128, 311, 197, 89, 267, 74], [288, 242, 289], [32, 47, 264]]]
 h' := ![![[290, 270, 122, 75], [234, 244, 281, 267], [120, 110, 24, 260], [53, 186, 253, 34], [19, 93, 277, 21], [183, 114, 300, 275], [305, 134, 50, 185], [0, 0, 1], [0, 1]], ![[78, 288, 97, 63], [261, 84, 251, 311], [263, 52, 312, 291], [229, 233, 58, 112], [81, 54, 221, 1], [226, 121, 263, 110], [0, 262, 193, 269], [37, 148, 227, 251], [290, 270, 122, 75]], ![[130, 67, 94, 175], [6, 180, 92, 185], [143, 40, 74, 207], [0, 82, 281, 45], [179, 114, 21, 179], [44, 4, 136, 276], [211, 236, 150, 174], [116, 117, 113, 45], [78, 288, 97, 63]], ![[0, 1], [197, 118, 2, 176], [210, 111, 216, 181], [74, 125, 34, 122], [219, 52, 107, 112], [41, 74, 240, 278], [95, 307, 233, 311], [55, 48, 285, 17], [130, 67, 94, 175]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [223, 59, 276], []]
 b := ![[], [], [246, 130, 138, 249], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N0 : CertifiedPrimeIdeal' SI313N0 313 where
  n := 4
  hpos := by decide
  P := [8, 179, 263, 128, 1]
  hirr := P313P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1110528074979, 1340945388623, 1704431486578, 63645332423, 1171285006931]
  a := ![-37, -75, -76, 33, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-408085695487, -759109252477, -507225605313, -736995210968, 1171285006931]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N0 : Ideal.IsPrime I313N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N0 B_one_repr
lemma NI313N0 : Nat.card (O ⧸ I313N0) = 9597924961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N0

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, -105, 267, -193, 234]] i)))

def SI313N1: IdealEqSpanCertificate' Table ![![29, -105, 267, -193, 234]] 
 ![![313, 0, 0, 0, 0], ![300, 1, 0, 0, 0], ![118, 0, 1, 0, 0], ![74, 0, 0, 1, 0], ![124, 0, 0, 0, 1]] where
  M :=![![![29, -105, 267, -193, 234], ![-128, 482, -1225, 887, -1076], ![164, -622, 1579, -1144, 1388], ![-720, 2719, -6901, 4998, -6064], ![192, -725, 1841, -1333, 1617]]]
  hmulB := by decide  
  f := ![![![393, 63, 185, 1, -170]], ![![376, 58, 177, 1, -164]], ![![146, 22, 67, 0, -64]], ![![86, 9, 35, -2, -44]], ![![152, 21, 69, -1, -71]]]
  g := ![![![-47, -105, 267, -193, 234], ![216, 482, -1225, 887, -1076], ![-278, -622, 1579, -1144, 1388], ![1214, 2719, -6901, 4998, -6064], ![-324, -725, 1841, -1333, 1617]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N1 : Nat.card (O ⧸ I313N1) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N1)

lemma isPrimeI313N1 : Ideal.IsPrime I313N1 := prime_ideal_of_norm_prime hp313.out _ NI313N1
def MulI313N0 : IdealMulLeCertificate' Table 
  ![![-393, -63, -185, -1, 170]] ![![29, -105, 267, -193, 234]]
  ![![313, 0, 0, 0, 0]] where
 M := ![![![-313, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC313 : ContainsPrimesAboveP 313 ![I313N0, I313N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI313N0
    exact isPrimeI313N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 313 (by decide) (𝕀 ⊙ MulI313N0)
instance hp317 : Fact (Nat.Prime 317) := {out := by norm_num}

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1137, 41, 359, 62, -213]] i)))

def SI317N0: IdealEqSpanCertificate' Table ![![1137, 41, 359, 62, -213]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![61, 34, 1, 0, 0], ![75, 259, 0, 1, 0], ![158, 6, 0, 0, 1]] where
  M :=![![![1137, 41, 359, 62, -213], ![-220, -273, -160, 22, 70], ![-604, 86, -333, -70, 168], ![-456, 426, 72, -73, 14], ![78, 126, 324, 22, -123]]]
  hmulB := by decide  
  f := ![![![583, -2125, 5465, -3940, 4797]], ![![-2536, 9955, -24928, 18142, -21926]], ![![-149, 619, -1520, 1114, -1339]], ![![-1979, 7808, -19517, 14213, -17169]], ![![256, -916, 2372, -1706, 2081]]]
  g := ![![![26, -85, 359, 62, -213], ![-10, -3, -160, 22, 70], ![-5, 90, -333, -70, 168], ![-5, 53, 72, -73, 14], ![-6, -50, 324, 22, -123]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P0 : CertificateIrreducibleZModOfList' 317 2 2 8 [10, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [224, 316], [0, 1]]
 g := ![![[41, 222], [95], [213, 141], [192, 15], [42, 40], [157, 53], [90], [1]], ![[0, 95], [95], [97, 176], [65, 302], [126, 277], [300, 264], [90], [1]]]
 h' := ![![[224, 316], [314, 92], [89, 27], [299, 211], [214, 40], [15, 62], [151, 147], [307, 224], [0, 1]], ![[0, 1], [0, 225], [114, 290], [13, 106], [298, 277], [272, 255], [111, 170], [80, 93], [224, 316]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [182, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N0 : CertifiedPrimeIdeal' SI317N0 317 where
  n := 2
  hpos := by decide
  P := [10, 93, 1]
  hirr := P317P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5348, 5578, 9224, -425, 5733]
  a := ![-5, -11, -10, 6, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4515, -733, 9224, -425, 5733]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N0 : Ideal.IsPrime I317N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N0 B_one_repr
lemma NI317N0 : Nat.card (O ⧸ I317N0) = 100489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N0

def I317N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![88553, 4297, 20869, 3737, -13968]] i)))

def SI317N1: IdealEqSpanCertificate' Table ![![88553, 4297, 20869, 3737, -13968]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![224, 18, 1, 0, 0], ![299, 231, 0, 1, 0], ![222, 295, 0, 0, 1]] where
  M :=![![![88553, 4297, 20869, 3737, -13968], ![-11868, -616, -2701, -573, 1960], ![-40924, -1930, -9783, -1624, 6328], ![-47244, -2521, -10589, -2404, 7952], ![-8280, -343, -2105, -237, 1165]]]
  hmulB := by decide  
  f := ![![![-2567, -1103, -5049, -517, 2032]], ![![824, 12020, 601, -1983, -72]], ![![-1748, -100, -3495, -472, 1416]], ![![-1825, 7654, -4327, -1922, 1864]], ![![-1054, 10381, -3020, -2208, 1373]]]
  g := ![![![-8210, 9104, 20869, 3737, -13968], ![1039, -1255, -2701, -573, 1960], ![3884, -4156, -9783, -1624, 6328], ![4032, -5055, -10589, -2404, 7952], ![869, -793, -2105, -237, 1165]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P1 : CertificateIrreducibleZModOfList' 317 2 2 8 [229, 201, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 316], [0, 1]]
 g := ![![[131, 181], [252], [302, 179], [8, 168], [104, 90], [264, 142], [142], [1]], ![[205, 136], [252], [144, 138], [159, 149], [83, 227], [252, 175], [142], [1]]]
 h' := ![![[116, 316], [154, 205], [265, 209], [70, 275], [276, 52], [91, 93], [269, 116], [88, 116], [0, 1]], ![[0, 1], [159, 112], [100, 108], [270, 42], [285, 265], [101, 224], [94, 201], [230, 201], [116, 316]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [154]]
 b := ![[], [289, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N1 : CertifiedPrimeIdeal' SI317N1 317 where
  n := 2
  hpos := by decide
  P := [229, 201, 1]
  hirr := P317P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![433537, 489950, 779918, -99117, 646619]
  a := ![46, 95, 92, -54, 215]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-909090, -572256, 779918, -99117, 646619]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N1 : Ideal.IsPrime I317N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N1 B_one_repr
lemma NI317N1 : Nat.card (O ⧸ I317N1) = 100489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N1

def I317N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, -3, 1, 0, -5]] i)))

def SI317N2: IdealEqSpanCertificate' Table ![![15, -3, 1, 0, -5]] 
 ![![317, 0, 0, 0, 0], ![111, 1, 0, 0, 0], ![221, 0, 1, 0, 0], ![210, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![15, -3, 1, 0, -5], ![-16, -19, -18, -4, -10], ![-20, -16, -17, -4, -8], ![-92, -114, -106, -25, -66], ![-62, -84, -76, -18, -49]]]
  hmulB := by decide  
  f := ![![![65, 63, 123, -42, 17]], ![![23, 22, 43, -14, 5]], ![![45, 43, 86, -30, 13]], ![![42, 44, 76, -25, 8]], ![![8, 8, 16, -6, 3]]]
  g := ![![![1, -3, 1, 0, -5], ![23, -19, -18, -4, -10], ![21, -16, -17, -4, -8], ![138, -114, -106, -25, -66], ![100, -84, -76, -18, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI317N2 : Nat.card (O ⧸ I317N2) = 317 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI317N2)

lemma isPrimeI317N2 : Ideal.IsPrime I317N2 := prime_ideal_of_norm_prime hp317.out _ NI317N2
def MulI317N0 : IdealMulLeCertificate' Table 
  ![![1137, 41, 359, 62, -213]] ![![88553, 4297, 20869, 3737, -13968]]
  ![![84340969, 4084320, 19897062, 3543893, -13284625]] where
 M := ![![![84340969, 4084320, 19897062, 3543893, -13284625]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI317N1 : IdealMulLeCertificate' Table 
  ![![84340969, 4084320, 19897062, 3543893, -13284625]] ![![15, -3, 1, 0, -5]]
  ![![317, 0, 0, 0, 0]] where
 M := ![![![1299432769, 62926719, 306551997, 54600397, -204674854]]]
 hmul := by decide  
 g := ![![![![4099157, 198507, 967041, 172241, -645662]]]]
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

def I331N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43121, 2088, 10172, 1812, -6792]] i)))

def SI331N0: IdealEqSpanCertificate' Table ![![43121, 2088, 10172, 1812, -6792]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![46, 80, 1, 0, 0], ![50, 92, 0, 1, 0], ![131, 169, 0, 0, 1]] where
  M :=![![![43121, 2088, 10172, 1812, -6792], ![-5784, -279, -1364, -244, 912], ![-19920, -964, -4699, -836, 3136], ![-23032, -1120, -5428, -971, 3632], ![-4024, -196, -952, -168, 633]]]
  hmulB := by decide  
  f := ![![![-101, -104, -148, -28, -40]], ![![-344, -381, -420, -132, -304]], ![![-98, -108, -123, -36, -80]], ![![-118, -132, -148, -43, -96]], ![![-221, -243, -280, -80, -175]]]
  g := ![![![1131, 512, 10172, 1812, -6792], ![-152, -69, -1364, -244, 912], ![-522, -236, -4699, -836, 3136], ![-606, -276, -5428, -971, 3632], ![-105, -47, -952, -168, 633]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P0 : CertificateIrreducibleZModOfList' 331 2 2 8 [317, 248, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [83, 330], [0, 1]]
 g := ![![[266, 149], [29, 274], [46], [264, 214], [30], [297], [157, 269], [1]], ![[55, 182], [263, 57], [46], [152, 117], [30], [297], [307, 62], [1]]]
 h' := ![![[83, 330], [75, 76], [28, 85], [55, 276], [176, 144], [114, 312], [212, 112], [14, 83], [0, 1]], ![[0, 1], [94, 255], [132, 246], [124, 55], [212, 187], [192, 19], [240, 219], [283, 248], [83, 330]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111]]
 b := ![[], [262, 221]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N0 : CertifiedPrimeIdeal' SI331N0 331 where
  n := 2
  hpos := by decide
  P := [317, 248, 1]
  hirr := P331P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![177202, 186539, 322768, -36014, 236060]
  a := ![-27, -60, -55, 38, -147]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-132306, -187963, 322768, -36014, 236060]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N0 : Ideal.IsPrime I331N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N0 B_one_repr
lemma NI331N0 : Nat.card (O ⧸ I331N0) = 109561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N0

def I331N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, -1, 3, -2]] i)))

def SI331N1: IdealEqSpanCertificate' Table ![![1, -1, -1, 3, -2]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![294, 153, 1, 0, 0], ![74, 305, 0, 1, 0], ![129, 216, 0, 0, 1]] where
  M :=![![![1, -1, -1, 3, -2], ![0, -2, 7, -9, 20], ![4, 22, -9, 12, -12], ![48, 19, 131, -42, 80], ![24, 31, 17, 23, -3]]]
  hmulB := by decide  
  f := ![![![2095, 109, 495, 87, -330]], ![![-268, -10, -41, -9, 36]], ![![1734, 92, 420, 73, -276]], ![![218, 15, 72, 11, -40]], ![![641, 36, 166, 28, -105]]]
  g := ![![![1, -1, -1, 3, -2], ![-12, -8, 7, -9, 20], ![10, 1, -9, 12, -12], ![-138, -74, 131, -42, 80], ![-19, -27, 17, 23, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P1 : CertificateIrreducibleZModOfList' 331 2 2 8 [31, 140, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [191, 330], [0, 1]]
 g := ![![[154, 299], [140, 1], [245], [304, 96], [96], [80], [64, 71], [1]], ![[0, 32], [0, 330], [245], [104, 235], [96], [80], [54, 260], [1]]]
 h' := ![![[191, 330], [294, 300], [191, 330], [175, 307], [128, 33], [172, 298], [2, 61], [300, 191], [0, 1]], ![[0, 1], [0, 31], [0, 1], [225, 24], [142, 298], [158, 33], [68, 270], [40, 140], [191, 330]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [190, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N1 : CertifiedPrimeIdeal' SI331N1 331 where
  n := 2
  hpos := by decide
  P := [31, 140, 1]
  hirr := P331P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4563, 1532, 20368, -12896, 19328]
  a := ![2, 16, 14, -18, 32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-22727, -10140, 20368, -12896, 19328]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N1 : Ideal.IsPrime I331N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N1 B_one_repr
lemma NI331N1 : Nat.card (O ⧸ I331N1) = 109561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N1

def I331N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, 1, 1, 2]] i)))

def SI331N2: IdealEqSpanCertificate' Table ![![1, -1, 1, 1, 2]] 
 ![![331, 0, 0, 0, 0], ![63, 1, 0, 0, 0], ![151, 0, 1, 0, 0], ![300, 0, 0, 1, 0], ![303, 0, 0, 0, 1]] where
  M :=![![![1, -1, 1, 1, 2], ![4, 14, 1, 1, 12], ![12, 20, 17, 2, 4], ![68, 79, 93, 20, 40], ![44, 49, 57, 15, 33]]]
  hmulB := by decide  
  f := ![![![-7777, -363, -1855, -315, 1210]], ![![-1477, -69, -352, -60, 230]], ![![-3537, -165, -844, -143, 550]], ![![-7036, -329, -1677, -286, 1096]], ![![-7117, -332, -1698, -288, 1107]]]
  g := ![![![-3, -1, 1, 1, 2], ![-15, 14, 1, 1, 12], ![-17, 20, 17, 2, 4], ![-112, 79, 93, 20, 40], ![-79, 49, 57, 15, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI331N2 : Nat.card (O ⧸ I331N2) = 331 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI331N2)

lemma isPrimeI331N2 : Ideal.IsPrime I331N2 := prime_ideal_of_norm_prime hp331.out _ NI331N2
def MulI331N0 : IdealMulLeCertificate' Table 
  ![![43121, 2088, 10172, 1812, -6792]] ![![1, -1, -1, 3, -2]]
  ![![7777, 363, 1855, 315, -1210]] where
 M := ![![![7777, 363, 1855, 315, -1210]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI331N1 : IdealMulLeCertificate' Table 
  ![![7777, 363, 1855, 315, -1210]] ![![1, -1, 1, 1, 2]]
  ![![331, 0, 0, 0, 0]] where
 M := ![![![-331, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC331 : ContainsPrimesAboveP 331 ![I331N0, I331N1, I331N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI331N0
    exact isPrimeI331N1
    exact isPrimeI331N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 331 (by decide) (𝕀 ⊙ MulI331N0 ⊙ MulI331N1)
instance hp337 : Fact (Nat.Prime 337) := {out := by norm_num}

def I337N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3373, 3858, -7104, -1655, 2945]] i)))

def SI337N0: IdealEqSpanCertificate' Table ![![-3373, 3858, -7104, -1655, 2945]] 
 ![![337, 0, 0, 0, 0], ![0, 337, 0, 0, 0], ![0, 0, 337, 0, 0], ![0, 0, 0, 337, 0], ![203, 117, 142, 329, 1]] where
  M :=![![![-3373, 3858, -7104, -1655, 2945], ![10296, 20294, 18861, -849, -7350], ![5160, -15732, 11729, 4342, -5008], ![-17340, -34761, -31707, 1530, 12362], ![-15150, -2103, -30195, -3857, 12235]]]
  hmulB := by decide  
  f := ![![![653, 36, 156, 29, -101]], ![![-72, 14, 3, -3, 30]], ![![-288, 6, -61, -4, 52]], ![![-252, 99, 63, -8, 154]], ![![1, 126, 131, 7, 122]]]
  g := ![![![-1784, -1011, -1262, -2880, 2945], ![4458, 2612, 3153, 7173, -7350], ![3032, 1692, 2145, 4902, -5008], ![-7498, -4395, -5303, -12064, 12362], ![-7415, -4254, -5245, -11956, 12235]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P0 : CertificateIrreducibleZModOfList' 337 4 2 8 [218, 312, 186, 17, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [249, 279, 126, 298], [203, 42, 215, 180], [205, 15, 333, 196], [0, 1]]
 g := ![![[189, 263, 65, 141], [106, 242, 316], [250, 261, 115], [305, 91, 126], [303, 52, 210, 54], [174, 325, 162], [320, 1], []], ![[84, 120, 0, 211, 99, 9], [317, 147, 148], [325, 70, 230], [44, 73, 74], [56, 69, 329, 191, 235, 182], [237, 41, 150], [144, 36, 8, 115, 309, 190], [62, 37, 173]], ![[140, 20, 290, 295, 129, 315], [190, 255, 287], [192, 86, 193], [147, 128, 98], [331, 295, 335, 82, 301, 80], [197, 94, 230], [125, 269, 134, 71, 222, 218], [85, 85, 48]], ![[230, 223, 124, 92, 143, 253], [269, 4, 234], [254, 142, 3], [74, 111, 263], [334, 321, 120, 40, 225, 149], [68, 285, 18], [1, 190, 288, 251, 201, 43], [331, 151, 335]]]
 h' := ![![[249, 279, 126, 298], [253, 152, 274, 50], [67, 28, 230, 84], [240, 114, 104, 231], [335, 204, 260, 154], [150, 164, 73, 197], [336, 31, 154, 103], [0, 0, 1], [0, 1]], ![[203, 42, 215, 180], [277, 221, 285, 166], [201, 136, 315, 85], [195, 258, 314, 60], [276, 335, 70, 243], [296, 31, 254, 283], [8, 106, 194, 216], [294, 322, 267, 95], [249, 279, 126, 298]], ![[205, 15, 333, 196], [105, 296, 281, 109], [243, 65, 235, 31], [206, 79, 187, 91], [205, 56, 29, 182], [186, 238, 252, 224], [296, 247, 225, 277], [100, 310, 201, 271], [203, 42, 215, 180]], ![[0, 1], [196, 5, 171, 12], [260, 108, 231, 137], [202, 223, 69, 292], [81, 79, 315, 95], [247, 241, 95, 307], [68, 290, 101, 78], [197, 42, 205, 308], [205, 15, 333, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [290, 24, 94], []]
 b := ![[], [], [87, 170, 222, 153], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N0 : CertifiedPrimeIdeal' SI337N0 337 where
  n := 4
  hpos := by decide
  P := [218, 312, 186, 17, 1]
  hirr := P337P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17326046934450, 21920535319987, 24982802806513, 2387120520575, 16822764553630]
  a := ![60, 102, 106, -52, 251]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10082181476120, -5775498271379, -7014390990531, -16416327648735, 16822764553630]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI337N0 : Ideal.IsPrime I337N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N0 B_one_repr
lemma NI337N0 : Nat.card (O ⧸ I337N0) = 12897917761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N0

def I337N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![653, 36, 156, 29, -101]] i)))

def SI337N1: IdealEqSpanCertificate' Table ![![653, 36, 156, 29, -101]] 
 ![![337, 0, 0, 0, 0], ![62, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![286, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![653, 36, 156, 29, -101], ![-72, 14, 3, -3, 30], ![-288, 6, -61, -4, 52], ![-252, 99, 63, -8, 154], ![6, 93, 63, 23, 57]]]
  hmulB := by decide  
  f := ![![![-3373, 3858, -7104, -1655, 2945]], ![![-590, 770, -1251, -307, 520]], ![![-335, 354, -703, -159, 291]], ![![-2914, 3171, -6123, -1400, 2536]], ![![-95, 51, -195, -36, 80]]]
  g := ![![![-44, 36, 156, 29, -101], ![-1, 14, 3, -3, 30], ![7, 6, -61, -4, 52], ![-21, 99, 63, -8, 154], ![-44, 93, 63, 23, 57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI337N1 : Nat.card (O ⧸ I337N1) = 337 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI337N1)

lemma isPrimeI337N1 : Ideal.IsPrime I337N1 := prime_ideal_of_norm_prime hp337.out _ NI337N1
def MulI337N0 : IdealMulLeCertificate' Table 
  ![![-3373, 3858, -7104, -1655, 2945]] ![![653, 36, 156, 29, -101]]
  ![![337, 0, 0, 0, 0]] where
 M := ![![![337, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC337 : ContainsPrimesAboveP 337 ![I337N0, I337N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI337N0
    exact isPrimeI337N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 337 (by decide) (𝕀 ⊙ MulI337N0)
instance hp347 : Fact (Nat.Prime 347) := {out := by norm_num}

def I347N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91, 27, -135, -24, 57]] i)))

def SI347N0: IdealEqSpanCertificate' Table ![![-91, 27, -135, -24, 57]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![66, 173, 1, 0, 0], ![197, 63, 0, 1, 0], ![122, 108, 0, 0, 1]] where
  M :=![![![-91, 27, -135, -24, 57], ![120, 341, 204, -30, -78], ![132, -174, 257, 66, -108], ![-180, -582, -336, 53, 126], ![-234, -132, -462, -42, 185]]]
  hmulB := by decide  
  f := ![![![-59, 99, -315, 210, -267]], ![![84, -617, 1284, -1002, 1146]], ![![30, -287, 575, -456, 516]], ![![-17, -66, 75, -79, 75]], ![![4, -156, 282, -234, 257]]]
  g := ![![![19, 54, -135, -24, 57], ![6, -71, 204, -30, -78], ![-48, -107, 257, 66, -108], ![-11, 117, -336, 53, 126], ![46, 180, -462, -42, 185]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P0 : CertificateIrreducibleZModOfList' 347 2 2 8 [180, 256, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [91, 346], [0, 1]]
 g := ![![[333, 263], [152, 53], [94], [144, 46], [285, 167], [29], [92, 300], [1]], ![[323, 84], [117, 294], [94], [166, 301], [214, 180], [29], [326, 47], [1]]]
 h' := ![![[91, 346], [53, 144], [4, 327], [105, 326], [56, 156], [179, 127], [96, 305], [167, 91], [0, 1]], ![[0, 1], [318, 203], [266, 20], [276, 21], [25, 191], [285, 220], [91, 42], [120, 256], [91, 346]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [271]]
 b := ![[], [341, 309]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N0 : CertifiedPrimeIdeal' SI347N0 347 where
  n := 2
  hpos := by decide
  P := [180, 256, 1]
  hirr := P347P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![494, 899, 1586, -1567, 3272]
  a := ![0, 3, 2, -4, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-561, -1522, 1586, -1567, 3272]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N0 : Ideal.IsPrime I347N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N0 B_one_repr
lemma NI347N0 : Nat.card (O ⧸ I347N0) = 120409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N0

def I347N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![513, 25, 121, 22, -81]] i)))

def SI347N1: IdealEqSpanCertificate' Table ![![513, 25, 121, 22, -81]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![103, 112, 1, 0, 0], ![334, 118, 0, 1, 0], ![144, 319, 0, 0, 1]] where
  M :=![![![513, 25, 121, 22, -81], ![-68, -3, -14, -4, 14], ![-236, -8, -57, -8, 36], ![-264, -6, -42, -17, 58], ![-42, 6, -6, 2, 9]]]
  hmulB := by decide  
  f := ![![![17, 73, 25, -8, -9]], ![![112, -13, 226, 32, -82]], ![![41, 17, 80, 8, -29]], ![![54, 66, 100, 3, -36]], ![![110, 19, 218, 26, -79]]]
  g := ![![![-22, 28, 121, 22, -81], ![2, -7, -14, -4, 14], ![9, -12, -57, -8, 36], ![4, -34, -42, -17, 58], ![-4, -7, -6, 2, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P1 : CertificateIrreducibleZModOfList' 347 2 2 8 [111, 154, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [193, 346], [0, 1]]
 g := ![![[314, 292], [217, 339], [1], [258, 339], [65, 30], [33], [93, 120], [1]], ![[109, 55], [61, 8], [1], [102, 8], [303, 317], [33], [4, 227], [1]]]
 h' := ![![[193, 346], [203, 197], [86, 214], [163, 346], [72, 133], [89, 270], [87, 294], [236, 193], [0, 1]], ![[0, 1], [54, 150], [95, 133], [317, 1], [63, 214], [149, 77], [268, 53], [9, 154], [193, 346]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [114, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N1 : CertifiedPrimeIdeal' SI347N1 347 where
  n := 2
  hpos := by decide
  P := [111, 154, 1]
  hirr := P347P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![423116, 466438, 777294, -109998, 643594]
  a := ![45, 91, 91, -56, 217]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-390710, -803796, 777294, -109998, 643594]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N1 : Ideal.IsPrime I347N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N1 B_one_repr
lemma NI347N1 : Nat.card (O ⧸ I347N1) = 120409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N1

def I347N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 10, -20, 16, -18]] i)))

def SI347N2: IdealEqSpanCertificate' Table ![![-1, 10, -20, 16, -18]] 
 ![![347, 0, 0, 0, 0], ![250, 1, 0, 0, 0], ![275, 0, 1, 0, 0], ![134, 0, 0, 1, 0], ![126, 0, 0, 0, 1]] where
  M :=![![![-1, 10, -20, 16, -18], ![16, -31, 106, -70, 92], ![-8, 58, -121, 94, -108], ![96, -168, 606, -393, 520], ![12, 96, -114, 116, -109]]]
  hmulB := by decide  
  f := ![![![12717, 790, 3028, 508, -2010]], ![![9158, 569, 2182, 366, -1448]], ![![10061, 624, 2395, 402, -1590]], ![![4890, 304, 1162, 195, -772]], ![![4614, 288, 1098, 184, -729]]]
  g := ![![![9, 10, -20, 16, -18], ![-68, -31, 106, -70, 92], ![57, 58, -121, 94, -108], ![-396, -168, 606, -393, 520], ![16, 96, -114, 116, -109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI347N2 : Nat.card (O ⧸ I347N2) = 347 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI347N2)

lemma isPrimeI347N2 : Ideal.IsPrime I347N2 := prime_ideal_of_norm_prime hp347.out _ NI347N2
def MulI347N0 : IdealMulLeCertificate' Table 
  ![![-91, 27, -135, -24, 57]] ![![513, 25, 121, 22, -81]]
  ![![-12717, -790, -3028, -508, 2010]] where
 M := ![![![-12717, -790, -3028, -508, 2010]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI347N1 : IdealMulLeCertificate' Table 
  ![![-12717, -790, -3028, -508, 2010]] ![![-1, 10, -20, 16, -18]]
  ![![347, 0, 0, 0, 0]] where
 M := ![![![-347, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC347 : ContainsPrimesAboveP 347 ![I347N0, I347N1, I347N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI347N0
    exact isPrimeI347N1
    exact isPrimeI347N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 347 (by decide) (𝕀 ⊙ MulI347N0 ⊙ MulI347N1)
instance hp349 : Fact (Nat.Prime 349) := {out := by norm_num}

def I349N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![349, 0, 0, 0, 0]] i)))

def SI349N0: IdealEqSpanCertificate' Table ![![349, 0, 0, 0, 0]] 
 ![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![0, 0, 349, 0, 0], ![0, 0, 0, 349, 0], ![0, 0, 0, 0, 349]] where
  M :=![![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![0, 0, 349, 0, 0], ![0, 0, 0, 349, 0], ![0, 0, 0, 0, 349]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P0 : CertificateIrreducibleZModOfList' 349 5 2 8 [110, 193, 256, 103, 15, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [222, 308, 253, 214, 176], [85, 86, 113, 4, 71], [65, 246, 60, 151, 254], [311, 57, 272, 329, 197], [0, 1]]
 g := ![![[182, 237, 236, 137, 289], [36, 178, 113, 201], [240, 76, 102, 18, 12], [195, 230, 221, 101, 88], [7, 91, 268, 5, 335], [9, 87, 64, 225], [1], []], ![[163, 29, 333, 9, 189, 154, 287, 63], [257, 3, 322, 104], [64, 130, 163, 283, 286, 193, 113, 166], [45, 232, 208, 173, 143, 162, 108, 71], [163, 10, 246, 86, 241, 50, 55, 117], [26, 179, 218, 31], [225, 327, 213, 337, 223, 18, 334, 237], [60, 31, 172, 264]], ![[308, 195, 258, 208, 245, 236, 76, 251], [94, 156, 173, 241], [48, 262, 142, 248, 325, 168, 53, 58], [348, 301, 278, 37, 284, 181, 21, 131], [273, 16, 301, 338, 105, 144, 6, 314], [336, 128, 51, 210], [108, 223, 334, 256, 341, 198, 56, 179], [182, 277, 337, 155]], ![[202, 268, 308, 159, 187, 223, 338, 268], [60, 127, 297, 76], [119, 135, 21, 165, 20, 336, 69, 5], [66, 199, 15, 32, 97, 13, 9, 289], [8, 59, 7, 299, 19, 218, 306, 196], [214, 313, 318, 308], [282, 69, 348, 301, 64, 113, 273, 20], [268, 221, 314, 300]], ![[217, 8, 237, 5, 50, 295, 193, 107], [253, 243, 197, 268], [238, 225, 285, 96, 233, 7, 80, 74], [280, 152, 66, 40, 168, 195, 119, 50], [227, 305, 197, 30, 109, 83, 290, 114], [163, 6, 128, 245], [266, 230, 36, 126, 115, 243, 1, 120], [274, 129, 144, 70]]]
 h' := ![![[222, 308, 253, 214, 176], [248, 277, 57, 111, 17], [124, 208, 326, 63, 119], [188, 183, 257, 105, 330], [277, 30, 172, 21, 92], [291, 92, 77, 100, 252], [239, 156, 93, 246, 334], [0, 0, 1], [0, 1]], ![[85, 86, 113, 4, 71], [86, 123, 337, 179, 33], [281, 99, 150, 30, 43], [92, 23, 268, 74, 24], [250, 242, 73, 25, 45], [245, 208, 142, 237, 117], [118, 76, 310, 136, 322], [106, 310, 111, 12, 51], [222, 308, 253, 214, 176]], ![[65, 246, 60, 151, 254], [159, 64, 249, 90, 78], [99, 302, 247, 31, 275], [41, 148, 71, 44, 242], [241, 172, 213, 181, 329], [335, 328, 348, 124, 250], [67, 206, 179, 306, 48], [118, 327, 116, 182, 229], [85, 86, 113, 4, 71]], ![[311, 57, 272, 329, 197], [184, 329, 325, 279, 117], [190, 58, 148, 289, 84], [266, 345, 200, 15, 30], [219, 229, 341, 80, 307], [45, 272, 332, 219, 27], [30, 243, 105, 18, 79], [222, 269, 342, 149, 289], [65, 246, 60, 151, 254]], ![[0, 1], [323, 254, 79, 39, 104], [294, 31, 176, 285, 177], [158, 348, 251, 111, 72], [86, 25, 248, 42, 274], [50, 147, 148, 18, 52], [251, 17, 11, 341, 264], [271, 141, 128, 6, 129], [311, 57, 272, 329, 197]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [314, 209, 220, 131], [], [], []]
 b := ![[], [217, 155, 324, 339, 29], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N0 : CertifiedPrimeIdeal' SI349N0 349 where
  n := 5
  hpos := by decide
  P := [110, 193, 256, 103, 15, 1]
  hirr := P349P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![460419554475448, 565282394838450, 691579271118658, 39460536325821, 471962962890487]
  a := ![18, 39, 36, -24, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1319253737752, 1619720329050, 1981602496042, 113067439329, 1352329406563]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI349N0 : Ideal.IsPrime I349N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N0 B_one_repr
lemma NI349N0 : Nat.card (O ⧸ I349N0) = 5177583776749 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N0

def PBC349 : ContainsPrimesAboveP 349 ![I349N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI349N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![349, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 349 (by decide) 𝕀

instance hp353 : Fact (Nat.Prime 353) := {out := by norm_num}

def I353N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![701, -215, -13, -25, -278]] i)))

def SI353N0: IdealEqSpanCertificate' Table ![![701, -215, -13, -25, -278]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![52, 204, 1, 0, 0], ![35, 258, 0, 1, 0], ![223, 335, 0, 0, 1]] where
  M :=![![![701, -215, -13, -25, -278], ![-1036, -1244, -1225, -241, -756], ![-1212, -1160, -1055, -302, -532], ![-6236, -7819, -7605, -1526, -4768], ![-4268, -5809, -5229, -1299, -3291]]]
  hmulB := by decide  
  f := ![![![-4783, -11967, -8539, 861, 3286]], ![![-15640, 14088, -32599, -6975, 13460]], ![![-9696, 6450, -20009, -3904, 8228]], ![![-11829, 9044, -24514, -4979, 10098]], ![![-17873, 5696, -36339, -6057, 14851]]]
  g := ![![![182, 289, -13, -25, -278], ![679, 1598, -1225, -241, -756], ![518, 1332, -1055, -302, -532], ![4266, 10013, -7605, -1526, -4768], ![2966, 7078, -5229, -1299, -3291]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P0 : CertificateIrreducibleZModOfList' 353 2 2 8 [307, 347, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 352], [0, 1]]
 g := ![![[215, 23], [256], [186], [201], [34], [95, 345], [62, 36], [1]], ![[0, 330], [256], [186], [201], [34], [47, 8], [278, 317], [1]]]
 h' := ![![[6, 352], [191, 27], [345, 337], [150, 48], [105, 55], [134, 280], [28, 261], [46, 6], [0, 1]], ![[0, 1], [0, 326], [249, 16], [85, 305], [82, 298], [49, 73], [182, 92], [82, 347], [6, 352]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [61, 215]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N0 : CertifiedPrimeIdeal' SI353N0 353 where
  n := 2
  hpos := by decide
  P := [307, 347, 1]
  hirr := P353P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![92655, 111669, 154503, -14121, 143196]
  a := ![21, 37, 37, -19, 92]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-111558, -214545, 154503, -14121, 143196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N0 : Ideal.IsPrime I353N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N0 B_one_repr
lemma NI353N0 : Nat.card (O ⧸ I353N0) = 124609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N0

def I353N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![143, -43, -3, -3, -58]] i)))

def SI353N1: IdealEqSpanCertificate' Table ![![143, -43, -3, -3, -58]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![199, 38, 1, 0, 0], ![32, 146, 0, 1, 0], ![156, 46, 0, 0, 1]] where
  M :=![![![143, -43, -3, -3, -58], ![-208, -254, -239, -55, -140], ![-244, -222, -223, -52, -116], ![-1232, -1571, -1451, -342, -904], ![-848, -1151, -1049, -247, -669]]]
  hmulB := by decide  
  f := ![![![-61, 277, -649, 475, -582]], ![![340, -1202, 3075, -2181, 2636]], ![![1, 31, -46, 41, -54]], ![![140, -491, 1261, -894, 1080]], ![![16, -29, 101, -65, 75]]]
  g := ![![![28, 9, -3, -3, -58], ![201, 66, -239, -55, -140], ![181, 60, -223, -52, -116], ![1245, 411, -1451, -342, -904], ![907, 299, -1049, -247, -669]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P1 : CertificateIrreducibleZModOfList' 353 2 2 8 [74, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [235, 352], [0, 1]]
 g := ![![[97, 4], [32], [271], [185], [253], [24, 185], [350, 157], [1]], ![[331, 349], [32], [271], [185], [253], [80, 168], [180, 196], [1]]]
 h' := ![![[235, 352], [54, 2], [59, 38], [92, 174], [108, 213], [342, 286], [222, 213], [279, 235], [0, 1]], ![[0, 1], [171, 351], [164, 315], [34, 179], [37, 140], [129, 67], [151, 140], [83, 118], [235, 352]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [287]]
 b := ![[], [171, 320]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N1 : CertifiedPrimeIdeal' SI353N1 353 where
  n := 2
  hpos := by decide
  P := [74, 118, 1]
  hirr := P353P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1189685, 1270243, 2209202, -306450, 1739098]
  a := ![-75, -156, -157, 98, -371]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1982817, -334097, 2209202, -306450, 1739098]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N1 : Ideal.IsPrime I353N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N1 B_one_repr
lemma NI353N1 : Nat.card (O ⧸ I353N1) = 124609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N1

def I353N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 7, 23, 4, -15]] i)))

def SI353N2: IdealEqSpanCertificate' Table ![![103, 7, 23, 4, -15]] 
 ![![353, 0, 0, 0, 0], ![93, 1, 0, 0, 0], ![286, 0, 1, 0, 0], ![256, 0, 0, 1, 0], ![308, 0, 0, 0, 1]] where
  M :=![![![103, 7, 23, 4, -15], ![-8, 9, 6, 0, 2], ![-44, -4, -5, 0, 8], ![-44, 10, -2, 3, 26], ![-2, 16, 4, 2, 15]]]
  hmulB := by decide  
  f := ![![![-491, 1845, -4715, 3410, -4133]], ![![-123, 462, -1181, 854, -1035]], ![![-406, 1526, -3899, 2820, -3418]], ![![-320, 1202, -3074, 2223, -2694]], ![![-438, 1646, -4206, 3042, -3687]]]
  g := ![![![-10, 7, 23, 4, -15], ![-9, 9, 6, 0, 2], ![-2, -4, -5, 0, 8], ![-26, 10, -2, 3, 26], ![-22, 16, 4, 2, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI353N2 : Nat.card (O ⧸ I353N2) = 353 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI353N2)

lemma isPrimeI353N2 : Ideal.IsPrime I353N2 := prime_ideal_of_norm_prime hp353.out _ NI353N2
def MulI353N0 : IdealMulLeCertificate' Table 
  ![![701, -215, -13, -25, -278]] ![![143, -43, -3, -3, -58]]
  ![![414679, 386606, 380078, 87614, 199532]] where
 M := ![![![414679, 386606, 380078, 87614, 199532]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI353N1 : IdealMulLeCertificate' Table 
  ![![414679, 386606, 380078, 87614, 199532]] ![![103, 7, 23, 4, -15]]
  ![![353, 0, 0, 0, 0]] where
 M := ![![![18641577, 8930547, 10579763, 2320622, 2864595]]]
 hmul := by decide  
 g := ![![![![52809, 25299, 29971, 6574, 8115]]]]
 hle2 := by decide  


def PBC353 : ContainsPrimesAboveP 353 ![I353N0, I353N1, I353N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI353N0
    exact isPrimeI353N1
    exact isPrimeI353N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 353 (by decide) (𝕀 ⊙ MulI353N0 ⊙ MulI353N1)
instance hp359 : Fact (Nat.Prime 359) := {out := by norm_num}

def I359N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8907, -424, -2128, -379, 1413]] i)))

def SI359N0: IdealEqSpanCertificate' Table ![![-8907, -424, -2128, -379, 1413]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![86, 178, 1, 0, 0], ![240, 73, 0, 1, 0], ![307, 203, 0, 0, 1]] where
  M :=![![![-8907, -424, -2128, -379, 1413], ![1220, 138, 329, 43, -206], ![4136, 158, 1029, 188, -672], ![4704, 93, 1041, 212, -718], ![774, 9, 87, 25, -87]]]
  hmulB := by decide  
  f := ![![![-179, -406, 32, -277, 93]], ![![-1180, -890, -2671, 679, -2030]], ![![-630, -544, -1315, 266, -982]], ![![-380, -469, -566, -37, -384]], ![![-833, -871, -1494, 139, -1074]]]
  g := ![![![-470, 332, -2128, -379, 1413], ![72, -55, 329, 43, -206], ![214, -168, 1029, 188, -672], ![236, -153, 1041, 212, -718], ![39, 1, 87, 25, -87]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P0 : CertificateIrreducibleZModOfList' 359 2 2 8 [284, 237, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 358], [0, 1]]
 g := ![![[83, 128], [130, 4], [286, 147], [85], [165], [272, 182], [17, 165], [1]], ![[262, 231], [259, 355], [270, 212], [85], [165], [218, 177], [43, 194], [1]]]
 h' := ![![[122, 358], [57, 207], [269, 357], [93, 295], [189, 320], [296, 237], [198, 329], [75, 122], [0, 1]], ![[0, 1], [181, 152], [25, 2], [183, 64], [98, 39], [131, 122], [128, 30], [240, 237], [122, 358]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [298]]
 b := ![[], [245, 149]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N0 : CertifiedPrimeIdeal' SI359N0 359 where
  n := 2
  hpos := by decide
  P := [284, 237, 1]
  hirr := P359P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![180774, 192802, 323588, -31571, 235845]
  a := ![-29, -59, -58, 36, -145]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-257591, -286846, 323588, -31571, 235845]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N0 : Ideal.IsPrime I359N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N0 B_one_repr
lemma NI359N0 : Nat.card (O ⧸ I359N0) = 128881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N0

def I359N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -23, -13, 2, 5]] i)))

def SI359N1: IdealEqSpanCertificate' Table ![![-5, -23, -13, 2, 5]] 
 ![![359, 0, 0, 0, 0], ![171, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![58, 0, 0, 1, 0], ![278, 0, 0, 0, 1]] where
  M :=![![![-5, -23, -13, 2, 5], ![-32, 21, -66, -12, 26], ![28, 50, 55, -2, -20], ![52, -32, 106, 25, -50], ![-2, -74, 4, 12, -1]]]
  hmulB := by decide  
  f := ![![![-2609, -3807, -3449, -816, -2247]], ![![-1281, -1866, -1691, -400, -1101]], ![![-85, -121, -110, -26, -71]], ![![-662, -946, -860, -203, -556]], ![![-2196, -3190, -2892, -684, -1881]]]
  g := ![![![7, -23, -13, 2, 5], ![-27, 21, -66, -12, 26], ![-9, 50, 55, -2, -20], ![48, -32, 106, 25, -50], ![34, -74, 4, 12, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI359N1 : Nat.card (O ⧸ I359N1) = 359 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI359N1)

lemma isPrimeI359N1 : Ideal.IsPrime I359N1 := prime_ideal_of_norm_prime hp359.out _ NI359N1

def I359N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 67, 39, -6, -15]] i)))

def SI359N2: IdealEqSpanCertificate' Table ![![25, 67, 39, -6, -15]] 
 ![![359, 0, 0, 0, 0], ![264, 1, 0, 0, 0], ![281, 0, 1, 0, 0], ![315, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![25, 67, 39, -6, -15], ![92, -55, 190, 36, -78], ![-84, -148, -153, 4, 60], ![-160, 90, -326, -61, 134], ![2, 210, -14, -38, 9]]]
  hmulB := by decide  
  f := ![![![293, -53, 607, -300, 449]], ![![216, -35, 442, -216, 326]], ![![231, -43, 484, -240, 359]], ![![261, -23, 509, -237, 371]], ![![35, -1, 75, -34, 56]]]
  g := ![![![-73, 67, 39, -6, -15], ![-132, -55, 190, 36, -78], ![219, -148, -153, 4, 60], ![229, 90, -326, -61, 134], ![-111, 210, -14, -38, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI359N2 : Nat.card (O ⧸ I359N2) = 359 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI359N2)

lemma isPrimeI359N2 : Ideal.IsPrime I359N2 := prime_ideal_of_norm_prime hp359.out _ NI359N2

def I359N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 21, 29, 0, -13]] i)))

def SI359N3: IdealEqSpanCertificate' Table ![![15, 21, 29, 0, -13]] 
 ![![359, 0, 0, 0, 0], ![290, 1, 0, 0, 0], ![84, 0, 1, 0, 0], ![67, 0, 0, 1, 0], ![130, 0, 0, 0, 1]] where
  M :=![![![15, 21, 29, 0, -13], ![16, -71, 42, 16, -26], ![-52, -44, -97, -8, 32], ![-76, 54, -134, -41, 6], ![2, 60, 16, -18, -41]]]
  hmulB := by decide  
  f := ![![![-389933, -18891, -91971, -16398, 61435]], ![![-314842, -15253, -74260, -13240, 49604]], ![![-90736, -4396, -21401, -3816, 14296]], ![![-72193, -3497, -17029, -3035, 11373]], ![![-141100, -6836, -33280, -5934, 22231]]]
  g := ![![![-19, 21, 29, 0, -13], ![54, -71, 42, 16, -26], ![48, -44, -97, -8, 32], ![-7, 54, -134, -41, 6], ![-34, 60, 16, -18, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI359N3 : Nat.card (O ⧸ I359N3) = 359 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI359N3)

lemma isPrimeI359N3 : Ideal.IsPrime I359N3 := prime_ideal_of_norm_prime hp359.out _ NI359N3
def MulI359N0 : IdealMulLeCertificate' Table 
  ![![-8907, -424, -2128, -379, 1413]] ![![-5, -23, -13, 2, 5]]
  ![![-24015, -2877, -7787, -989, 4538]] where
 M := ![![![-24015, -2877, -7787, -989, 4538]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI359N1 : IdealMulLeCertificate' Table 
  ![![-24015, -2877, -7787, -989, 4538]] ![![25, 67, 39, -6, -15]]
  ![![-43635, 565676, -32922, -102745, 25727]] where
 M := ![![![-43635, 565676, -32922, -102745, 25727]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI359N2 : IdealMulLeCertificate' Table 
  ![![-43635, 565676, -32922, -102745, 25727]] ![![15, 21, 29, 0, -13]]
  ![![359, 0, 0, 0, 0]] where
 M := ![![![17968309, -43635373, 39865873, 13063651, -16865102]]]
 hmul := by decide  
 g := ![![![![50051, -121547, 111047, 36389, -46978]]]]
 hle2 := by decide  


def PBC359 : ContainsPrimesAboveP 359 ![I359N0, I359N1, I359N2, I359N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI359N0
    exact isPrimeI359N1
    exact isPrimeI359N2
    exact isPrimeI359N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 359 (by decide) (𝕀 ⊙ MulI359N0 ⊙ MulI359N1 ⊙ MulI359N2)


lemma PB853I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313, 317, 331, 337, 347, 349, 353, 359] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 359 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 359 (by omega)

def PB853I7 : PrimesBelowBoundCertificateInterval O 307 359 853 where
  m := 9
  g := ![2, 2, 3, 3, 2, 3, 1, 3, 4]
  P := ![311, 313, 317, 331, 337, 347, 349, 353, 359]
  hP := PB853I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1]
    · exact ![I313N0, I313N1]
    · exact ![I317N0, I317N1, I317N2]
    · exact ![I331N0, I331N1, I331N2]
    · exact ![I337N0, I337N1]
    · exact ![I347N0, I347N1, I347N2]
    · exact ![I349N0]
    · exact ![I353N0, I353N1, I353N2]
    · exact ![I359N0, I359N1, I359N2, I359N3]
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
    · exact ![9354951841, 311]
    · exact ![9597924961, 313]
    · exact ![100489, 100489, 317]
    · exact ![109561, 109561, 331]
    · exact ![12897917761, 337]
    · exact ![120409, 120409, 347]
    · exact ![5177583776749]
    · exact ![124609, 124609, 353]
    · exact ![128881, 359, 359, 359]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI311N0
      exact NI311N1
    · dsimp ; intro j
      fin_cases j
      exact NI313N0
      exact NI313N1
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
      exact NI317N1
      exact NI317N2
    · dsimp ; intro j
      fin_cases j
      exact NI331N0
      exact NI331N1
      exact NI331N2
    · dsimp ; intro j
      fin_cases j
      exact NI337N0
      exact NI337N1
    · dsimp ; intro j
      fin_cases j
      exact NI347N0
      exact NI347N1
      exact NI347N2
    · dsimp ; intro j
      fin_cases j
      exact NI349N0
    · dsimp ; intro j
      fin_cases j
      exact NI353N0
      exact NI353N1
      exact NI353N2
    · dsimp ; intro j
      fin_cases j
      exact NI359N0
      exact NI359N1
      exact NI359N2
      exact NI359N3
  β := ![I311N1, I313N1, I317N2, I331N2, I337N1, I347N2, I353N2, I359N1, I359N2, I359N3]
  Il := ![[I311N1], [I313N1], [I317N2], [I331N2], [I337N1], [I347N2], [], [I353N2], [I359N1, I359N2, I359N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
