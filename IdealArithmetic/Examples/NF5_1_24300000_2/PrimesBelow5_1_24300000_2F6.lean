
import IdealArithmetic.Examples.NF5_1_24300000_2.RI5_1_24300000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0, 0, 0]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0, 0, 0]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![0, 0, 0, 257, 0], ![0, 0, 0, 0, 257]] where
  M :=![![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![0, 0, 0, 257, 0], ![0, 0, 0, 0, 257]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 5 2 8 [96, 44, 22, 102, 192, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 193, 60, 80, 245], [169, 29, 80, 148, 74], [208, 164, 40, 125, 148], [147, 127, 77, 161, 47], [0, 1]]
 g := ![![[61, 118, 120, 184, 228], [46, 16, 70, 52], [46, 72, 228, 223], [178, 216, 185, 232], [75, 174, 176, 207], [231, 11, 65, 1], [], []], ![[16, 109, 117, 109, 209, 81, 173, 38], [251, 28, 129, 223], [185, 202, 240, 197], [197, 51, 43, 114], [140, 233, 111, 143], [43, 159, 112, 32], [33, 68, 124, 242], [15, 221, 244, 144]], ![[136, 211, 50, 210, 19, 148, 218, 39], [121, 185, 254, 139], [37, 205, 76, 146], [9, 230, 215, 9], [100, 67, 64, 70], [244, 132, 104, 157], [173, 167, 220, 111], [218, 155, 54, 79]], ![[154, 151, 225, 66, 149, 228, 18, 126], [232, 46, 165, 32], [167, 209, 134, 196], [56, 249, 246, 207], [166, 76, 76, 255], [65, 65, 38, 79], [245, 108, 66, 99], [228, 95, 229, 59]], ![[134, 73, 17, 84, 126, 218, 51, 14], [193, 154, 66, 89], [178, 157, 217, 70], [90, 180, 237, 128], [100, 112, 173, 62], [214, 246, 16, 17], [21, 88, 217, 114], [186, 61, 150, 153]]]
 h' := ![![[55, 193, 60, 80, 245], [228, 246, 69, 101, 182], [77, 245, 86, 181, 201], [102, 205, 57, 12, 123], [75, 125, 248, 69, 177], [183, 88, 16, 225, 83], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[169, 29, 80, 148, 74], [51, 10, 202, 149, 168], [62, 173, 240, 236, 134], [54, 178, 85, 206, 35], [132, 54, 97, 240, 194], [112, 84, 107, 24, 237], [223, 200, 119, 73, 240], [43, 125, 91, 237, 146], [55, 193, 60, 80, 245]], ![[208, 164, 40, 125, 148], [210, 206, 164, 189, 2], [2, 40, 85, 35, 216], [133, 59, 241, 236, 114], [45, 179, 122, 24, 3], [81, 41, 233, 29, 29], [115, 150, 41, 11, 160], [180, 236, 30, 40, 25], [169, 29, 80, 148, 74]], ![[147, 127, 77, 161, 47], [62, 255, 221, 216, 118], [177, 111, 67, 178, 17], [180, 120, 208, 229, 14], [219, 179, 12, 13, 174], [96, 255, 37, 161, 189], [93, 118, 196, 123, 183], [45, 242, 20, 133, 149], [208, 164, 40, 125, 148]], ![[0, 1], [94, 54, 115, 116, 44], [115, 202, 36, 141, 203], [193, 209, 180, 88, 228], [98, 234, 35, 168, 223], [184, 46, 121, 75, 233], [164, 46, 158, 50, 187], [155, 168, 115, 104, 194], [147, 127, 77, 161, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136, 51, 235, 203], [], [], []]
 b := ![[], [43, 110, 59, 175, 124], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 5
  hpos := by decide
  P := [96, 44, 22, 102, 192, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1968446011, -499812829, 1374125287, -541082660, 1427779434]
  a := ![-13, -7, -11, 0, -26]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7659323, -1944797, 5346791, -2105380, 5555562]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 1121154893057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def PBC257 : ContainsPrimesAboveP 257 ![I257N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![257, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 257 (by decide) 𝕀

instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4099, 395, -451, -580, -324]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![4099, 395, -451, -580, -324]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![14, 31, 1, 0, 0], ![46, 53, 0, 1, 0], ![99, 127, 0, 0, 1]] where
  M :=![![![4099, 395, -451, -580, -324], ![-3036, 3716, -1089, 2, -3804], ![-15210, 3485, -84, 1624, -3792], ![-3630, -4901, 2015, 999, 4878], ![6673, -4524, 1100, -393, 4685]]]
  hmulB := by decide  
  f := ![![![-985, 141, -331, -86, -132]], ![![-786, -1138, -163, -444, -648]], ![![-160, -127, -47, -54, -96]], ![![-350, -201, -94, -109, -150]], ![![-746, -501, -200, -249, -361]]]
  g := ![![![263, 328, -451, -580, -324], ![1478, 1979, -1089, 2, -3804], ![1090, 1527, -84, 1624, -3792], ![-2132, -2813, 2015, 999, 4878], ![-1728, -2330, 1100, -393, 4685]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [79, 152, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [111, 262], [0, 1]]
 g := ![![[205, 75], [253, 258], [257, 102], [89], [178], [109], [223], [1]], ![[114, 188], [224, 5], [7, 161], [89], [178], [109], [223], [1]]]
 h' := ![![[111, 262], [1, 148], [211, 235], [198, 75], [172, 103], [86, 242], [196, 114], [184, 111], [0, 1]], ![[0, 1], [123, 115], [259, 28], [107, 188], [33, 160], [122, 21], [226, 149], [144, 152], [111, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [198]]
 b := ![[], [160, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [79, 152, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2132, 44932, -19485, 14385, 5425]
  a := ![19, -56, 15, -67, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3529, -3051, -19485, 14385, 5425]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, -2, 2, 2, 2]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![-15, -2, 2, 2, 2]] 
 ![![263, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![97, 0, 0, 1, 0], ![257, 0, 0, 0, 1]] where
  M :=![![![-15, -2, 2, 2, 2], ![14, -15, 4, 0, 14], ![56, -10, -1, -6, 14], ![12, 18, -6, -5, -18], ![-26, 16, -4, 2, -19]]]
  hmulB := by decide  
  f := ![![![-857, -186, -342, -90, -394]], ![![-95, -21, -38, -10, -44]], ![![-212, -46, -85, -22, -98]], ![![-331, -72, -132, -35, -152]], ![![-837, -182, -334, -88, -385]]]
  g := ![![![-3, -2, 2, 2, 2], ![-13, -15, 4, 0, 14], ![-10, -10, -1, -6, 14], ![19, 18, -6, -5, -18], ![17, 16, -4, 2, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1

def I263N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 10, 6, 4, 10]] i)))

def SI263N2: IdealEqSpanCertificate' Table ![![17, 10, 6, 4, 10]] 
 ![![263, 0, 0, 0, 0], ![221, 1, 0, 0, 0], ![77, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![105, 0, 0, 0, 1]] where
  M :=![![![17, 10, 6, 4, 10], ![52, 7, 28, -2, 34], ![130, 10, 37, 24, 22], ![54, 70, 26, 15, 66], ![0, -4, 12, -12, 19]]]
  hmulB := by decide  
  f := ![![![1443, 1074, -490, -304, -1058]], ![![1193, 913, -414, -254, -900]], ![![383, 316, -141, -84, -312]], ![![342, 226, -106, -69, -222]], ![![605, 418, -194, -124, -411]]]
  g := ![![![-15, 10, 6, 4, 10], ![-27, 7, 28, -2, 34], ![-33, 10, 37, 24, 22], ![-96, 70, 26, 15, 66], ![-5, -4, 12, -12, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N2 : Nat.card (O ⧸ I263N2) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N2)

lemma isPrimeI263N2 : Ideal.IsPrime I263N2 := prime_ideal_of_norm_prime hp263.out _ NI263N2

def I263N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-99, -23, -43, -8, -52]] i)))

def SI263N3: IdealEqSpanCertificate' Table ![![-99, -23, -43, -8, -52]] 
 ![![263, 0, 0, 0, 0], ![247, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![226, 0, 0, 0, 1]] where
  M :=![![![-99, -23, -43, -8, -52], ![-232, -46, -91, -26, -100], ![-478, -149, -198, -56, -256], ![-480, -87, -213, -29, -246], ![-11, 16, 2, -3, 17]]]
  hmulB := by decide  
  f := ![![![6949, -801, -243, -826, 932]], ![![6531, -737, -234, -778, 860]], ![![117, 6, -11, -16, -4]], ![![1640, -207, -51, -193, 238]], ![![5983, -710, -202, -709, 823]]]
  g := ![![![69, -23, -43, -8, -52], ![137, -46, -91, -26, -100], ![377, -149, -198, -56, -256], ![304, -87, -213, -29, -246], ![-29, 16, 2, -3, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N3 : Nat.card (O ⧸ I263N3) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N3)

lemma isPrimeI263N3 : Ideal.IsPrime I263N3 := prime_ideal_of_norm_prime hp263.out _ NI263N3
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![4099, 395, -451, -580, -324]] ![![-15, -2, 2, 2, 2]]
  ![![-79747, -25237, 15005, 13156, 24010]] where
 M := ![![![-79747, -25237, 15005, 13156, 24010]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI263N1 : IdealMulLeCertificate' Table 
  ![![-79747, -25237, 15005, 13156, 24010]] ![![17, 10, 6, 4, 10]]
  ![![-6949, 801, 243, 826, -932]] where
 M := ![![![-6949, 801, 243, 826, -932]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI263N2 : IdealMulLeCertificate' Table 
  ![![-6949, 801, 243, 826, -932]] ![![-99, -23, -43, -8, -52]]
  ![![263, 0, 0, 0, 0]] where
 M := ![![![-263, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1, I263N2, I263N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
    exact isPrimeI263N2
    exact isPrimeI263N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0 ⊙ MulI263N1 ⊙ MulI263N2)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1492, -439, 43, -149, 470]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![1492, -439, 43, -149, 470]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![39, 6, 115, 1, 0], ![126, 21, 230, 0, 1]] where
  M :=![![![1492, -439, 43, -149, 470], ![1433, 446, -267, -235, -424], ![-2401, 1779, -448, 125, -1834], ![-4197, 249, 231, 524, -330], ![-842, -870, 372, 204, 861]]]
  hmulB := by decide  
  f := ![![![36, 33, 15, 9, 32]], ![![155, -4, 83, -11, 86]], ![![311, 55, 60, 91, 20]], ![![142, 29, 30, 40, 16]], ![![295, 62, 65, 81, 39]]]
  g := ![![![-193, -35, -338, -149, 470], ![238, 40, 462, -235, -424], ![832, 147, 1513, 125, -1834], ![63, 15, 59, 524, -330], ![-436, -75, -822, 204, 861]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [40, 258, 191, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 59, 187], [34, 209, 82], [0, 1]]
 g := ![![[241, 28, 207], [179, 264], [260, 104, 182], [55, 133, 21], [140, 256], [194, 125], [78, 1], []], ![[259, 252, 191, 19], [52, 216], [87, 95, 27, 137], [33, 25, 66, 129], [101, 20], [260, 142], [103, 103], [199, 268]], ![[122, 173, 99, 18], [69, 152], [168, 147, 125, 10], [145, 4, 257, 40], [109, 13], [105, 57], [14, 253], [35, 268]]]
 h' := ![![[44, 59, 187], [45, 94, 106], [91, 197, 110], [221, 163, 102], [263, 244, 57], [138, 48, 253], [108, 11, 177], [0, 0, 1], [0, 1]], ![[34, 209, 82], [208, 236, 189], [58, 220, 111], [78, 178, 151], [115, 268, 244], [180, 35, 252], [122, 101, 45], [163, 158, 209], [44, 59, 187]], ![[0, 1], [242, 208, 243], [124, 121, 48], [243, 197, 16], [31, 26, 237], [25, 186, 33], [65, 157, 47], [25, 111, 59], [34, 209, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93, 108], []]
 b := ![[], [105, 74, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [40, 258, 191, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27142, 30302, 17782, -626, 32544]
  a := ![-2, -4, -2, -3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15052, -2414, -27492, -626, 32544]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13298, 2582, 5176, 1515, 5628]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![13298, 2582, 5176, 1515, 5628]] 
 ![![269, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![171, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![13298, 2582, 5176, 1515, 5628], ![27057, 8733, 11240, 3209, 14718], ![68499, 12070, 29869, 4553, 33972], ![61245, 13122, 21954, 9002, 23286], ![-3759, 3022, -1690, 627, 173]]]
  hmulB := by decide  
  f := ![![![3031492, -5494486, 1720630, 188307, 5597970]], ![![750241, -1228365, 379172, 32584, 1252818]], ![![254201, -298422, 86663, -1523, 305670]], ![![1810737, -3431112, 1080714, 128393, 3494238]], ![![303285, -719098, 232276, 36909, 730943]]]
  g := ![![![-2541, 2582, 5176, 1515, 5628], ![-6493, 8733, 11240, 3209, 14718], ![-11610, 12070, 29869, 4553, 33972], ![-12795, 13122, 21954, 9002, 23286], ![-998, 3022, -1690, 627, 173]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1

def I269N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5865, -2771, 539, -474, 2902]] i)))

def SI269N2: IdealEqSpanCertificate' Table ![![5865, -2771, 539, -474, 2902]] 
 ![![269, 0, 0, 0, 0], ![249, 1, 0, 0, 0], ![138, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![205, 0, 0, 0, 1]] where
  M :=![![![5865, -2771, 539, -474, 2902], ![10186, 126, -817, -1350, 58], ![-3818, 7903, -2516, -342, -8042], ![-21690, 4641, -3, 2351, -5076], ![-9181, -2028, 1416, 1421, 1879]]]
  hmulB := by decide  
  f := ![![![15815, 2729, 7153, 800, 8266]], ![![14771, 2553, 6668, 760, 7700]], ![![8366, 1501, 3784, 436, 4406]], ![![2949, 474, 1332, 143, 1518]], ![![12062, 2069, 5443, 619, 6275]]]
  g := ![![![178, -2771, 539, -474, 2902], ![522, 126, -817, -1350, 58], ![147, 7903, -2516, -342, -8042], ![-900, 4641, -3, 2351, -5076], ![-553, -2028, 1416, 1421, 1879]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N2 : Nat.card (O ⧸ I269N2) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N2)

lemma isPrimeI269N2 : Ideal.IsPrime I269N2 := prime_ideal_of_norm_prime hp269.out _ NI269N2
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![1492, -439, 43, -149, 470]] ![![13298, 2582, 5176, 1515, 5628]]
  ![![15815, 2729, 7153, 800, 8266]] where
 M := ![![![15815, 2729, 7153, 800, 8266]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI269N1 : IdealMulLeCertificate' Table 
  ![![15815, 2729, 7153, 800, 8266]] ![![5865, -2771, 539, -474, 2902]]
  ![![269, 0, 0, 0, 0]] where
 M := ![![![269, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC269 : ContainsPrimesAboveP 269 ![I269N0, I269N1, I269N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
    exact isPrimeI269N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 269 (by decide) (𝕀 ⊙ MulI269N0 ⊙ MulI269N1)
instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14, -93, -35, 79, -146]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![14, -93, -35, 79, -146]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![0, 0, 0, 271, 0], ![89, 125, 184, 57, 1]] where
  M :=![![![14, -93, -35, 79, -146], ![-347, 350, -81, -3, 328], ![1303, -1087, 672, -487, 310], ![63, 259, -835, 762, -1470], ![-972, 882, -280, 90, 187]]]
  hmulB := by decide  
  f := ![![![-402, -95, -165, -41, -196]], ![![-907, -216, -373, -93, -442]], ![![-2047, -489, -844, -211, -1000]], ![![-1863, -443, -769, -192, -912]], ![![-2332, -556, -961, -240, -1139]]]
  g := ![![![48, 67, 99, 31, -146], ![-109, -150, -223, -69, 328], ![-97, -147, -208, -67, 310], ![483, 679, 995, 312, -1470], ![-65, -83, -128, -39, 187]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 4 2 8 [7, 23, 205, 266, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 130, 98, 256], [246, 255, 129, 143], [183, 156, 44, 143], [0, 1]]
 g := ![![[138, 16, 41, 195], [64, 192, 17, 103], [103, 143, 159, 80], [233, 33, 70, 228], [118, 30, 32], [216, 243, 25], [1], []], ![[133, 37, 24, 83, 40, 41], [128, 189, 144, 20, 195, 129], [96, 60, 220, 13, 259, 31], [4, 113, 268, 165, 78, 151], [131, 75, 79], [84, 214, 50], [270, 78, 106], [97, 82, 225]], ![[123, 232, 9, 251, 256, 226], [3, 69, 120, 234, 242, 254], [235, 245, 74, 98, 38, 267], [220, 162, 155, 63, 77, 188], [181, 168, 166], [195, 13, 81], [40, 27, 126], [233, 116, 124]], ![[183, 220, 185, 240, 130, 26], [179, 249, 49, 41, 13, 86], [79, 48, 128, 214, 260, 54], [237, 16, 123, 161, 163, 199], [225, 131, 144], [197, 158, 112], [263, 199, 81], [161, 196, 124]]]
 h' := ![![[118, 130, 98, 256], [94, 228, 192, 174], [92, 178, 262, 118], [266, 105, 228, 132], [269, 20, 169, 162], [163, 157, 238, 158], [264, 248, 66, 5], [0, 0, 1], [0, 1]], ![[246, 255, 129, 143], [14, 251, 70, 14], [225, 142, 142, 202], [235, 47, 229, 4], [256, 8, 139, 192], [233, 260, 162, 86], [79, 164, 227, 62], [237, 233, 151, 169], [118, 130, 98, 256]], ![[183, 156, 44, 143], [129, 133, 118, 52], [52, 131, 170, 134], [79, 149, 135, 12], [30, 227, 200, 121], [22, 262, 61, 39], [113, 31, 82, 262], [78, 49, 228, 111], [246, 255, 129, 143]], ![[0, 1], [150, 201, 162, 31], [141, 91, 239, 88], [82, 241, 221, 123], [131, 16, 34, 67], [132, 134, 81, 259], [88, 99, 167, 213], [113, 260, 162, 262], [183, 156, 44, 143]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [11, 6, 117], []]
 b := ![[], [], [209, 119, 42, 147], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 4
  hpos := by decide
  P := [7, 23, 205, 266, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1665912080, 324053061, 606240653, 222479130, 646046985]
  a := ![23, 27, 19, 12, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-206023135, -296796384, -436407397, -135063465, 646046985]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 5393580481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![402, 95, 165, 41, 196]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![402, 95, 165, 41, 196]] 
 ![![271, 0, 0, 0, 0], ![199, 1, 0, 0, 0], ![236, 0, 1, 0, 0], ![131, 0, 0, 1, 0], ![263, 0, 0, 0, 1]] where
  M :=![![![402, 95, 165, 41, 196], ![907, 216, 373, 93, 442], ![2047, 489, 844, 211, 1000], ![1863, 443, 769, 192, 912], ![-20, -6, -8, -2, -9]]]
  hmulB := by decide  
  f := ![![![-14, 93, 35, -79, 146]], ![![-9, 67, 26, -58, 106]], ![![-17, 85, 28, -67, 126]], ![![-7, 44, 20, -41, 76]], ![![-10, 87, 35, -77, 141]]]
  g := ![![![-422, 95, 165, 41, 196], ![-954, 216, 373, 93, 442], ![-2159, 489, 844, 211, 1000], ![-1966, 443, 769, 192, 912], ![21, -6, -8, -2, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![14, -93, -35, 79, -146]] ![![402, 95, 165, 41, 196]]
  ![![271, 0, 0, 0, 0]] where
 M := ![![![-271, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2004, 457, 839, 189, 992]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![2004, 457, 839, 189, 992]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![205, 272, 9, 1, 0], ![66, 50, 251, 0, 1]] where
  M :=![![![2004, 457, 839, 189, 992], ![4535, 1048, 1827, 497, 2126], ![9995, 2607, 4168, 1031, 5108], ![9495, 1965, 3975, 850, 4584], ![-26, -86, -76, 40, -175]]]
  hmulB := by decide  
  f := ![![![-868, 177, 3, 95, -194]], ![![-491, -382, 173, 105, 376]], ![![1819, -965, 204, -135, 1006]], ![![-1058, -275, 178, 168, 258]], ![![1353, -899, 216, -81, 931]]]
  g := ![![![-369, -363, -902, 189, 992], ![-858, -868, -1936, 497, 2126], ![-1944, -1925, -4647, 1031, 5108], ![-1687, -1655, -4167, 850, 4584], ![12, -8, 157, 40, -175]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 3 2 8 [38, 190, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [158, 73, 188], [117, 203, 89], [0, 1]]
 g := ![![[25, 74, 190], [52, 108], [164, 147, 256], [207, 255], [163, 16, 192], [254, 248], [275, 1], []], ![[141, 197, 209, 49], [205, 273], [92, 18, 213, 202], [88, 36], [19, 132, 221, 190], [21, 146], [250, 213], [249, 165]], ![[5, 247, 250, 136], [163, 156], [75, 154, 179, 160], [28, 120], [192, 142, 164, 190], [16, 261], [183, 66], [71, 165]]]
 h' := ![![[158, 73, 188], [171, 37, 81], [139, 171, 51], [195, 40, 261], [177, 4, 55], [2, 117, 68], [76, 65, 91], [0, 0, 1], [0, 1]], ![[117, 203, 89], [221, 130, 131], [55, 92, 120], [27, 268, 117], [259, 198, 6], [80, 145, 67], [18, 92, 223], [267, 235, 203], [158, 73, 188]], ![[0, 1], [61, 110, 65], [95, 14, 106], [205, 246, 176], [182, 75, 216], [160, 15, 142], [136, 120, 240], [188, 42, 73], [117, 203, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 196], []]
 b := ![[], [124, 199, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 3
  hpos := by decide
  P := [38, 190, 2, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1288484, -1481920, -836972, 977416, -2796243]
  a := ![-33, -9, -27, 15, -65]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-52454, -460386, 2499001, 977416, -2796243]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 21253933 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3329, 791, 1371, 342, 1626]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![3329, 791, 1371, 342, 1626]] 
 ![![277, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![66, 0, 0, 1, 0], ![211, 0, 0, 0, 1]] where
  M :=![![![3329, 791, 1371, 342, 1626], ![7530, 1790, 3101, 774, 3678], ![17034, 4049, 7016, 1750, 8322], ![15504, 3683, 6385, 1593, 7572], ![-169, -40, -70, -17, -83]]]
  hmulB := by decide  
  f := ![![![1595, -229, -51, -172, 294]], ![![440, -60, -15, -48, 78]], ![![223, -28, -9, -24, 36]], ![![366, -55, -11, -39, 72]], ![![1216, -179, -37, -131, 229]]]
  g := ![![![-1728, 791, 1371, 342, 1626], ![-3909, 1790, 3101, 774, 3678], ![-8844, 4049, 7016, 1750, 8322], ![-8047, 3683, 6385, 1593, 7572], ![88, -40, -70, -17, -83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1

def I277N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6150, -2080, 272, -585, 2210]] i)))

def SI277N2: IdealEqSpanCertificate' Table ![![6150, -2080, 272, -585, 2210]] 
 ![![277, 0, 0, 0, 0], ![183, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![255, 0, 0, 1, 0], ![74, 0, 0, 0, 1]] where
  M :=![![![6150, -2080, 272, -585, 2210], ![7085, 1417, -1040, -1081, -1300], ![-8443, 7564, -2045, 301, -7786], ![-18663, 1984, 710, 2238, -2340], ![-4993, -3226, 1524, 999, 3165]]]
  hmulB := by decide  
  f := ![![![-27166660, -6456712, -11188390, -2791549, -13270280]], ![![-18169511, -4318355, -7482980, -1867034, -8875382]], ![![-3247977, -771948, -1337655, -333751, -1586560]], ![![-25465767, -6052460, -10487890, -2616771, -12439434]], ![![-7252541, -1723714, -2986906, -745245, -3542697]]]
  g := ![![![1317, -2080, 272, -585, 2210], ![537, 1417, -1040, -1081, -1300], ![-3018, 7564, -2045, 301, -7786], ![-2885, 1984, 710, 2238, -2340], ![194, -3226, 1524, 999, 3165]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N2 : Nat.card (O ⧸ I277N2) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N2)

lemma isPrimeI277N2 : Ideal.IsPrime I277N2 := prime_ideal_of_norm_prime hp277.out _ NI277N2
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![2004, 457, 839, 189, 992]] ![![3329, 791, 1371, 342, 1626]]
  ![![27166660, 6456712, 11188390, 2791549, 13270280]] where
 M := ![![![27166660, 6456712, 11188390, 2791549, 13270280]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI277N1 : IdealMulLeCertificate' Table 
  ![![27166660, 6456712, 11188390, 2791549, 13270280]] ![![6150, -2080, 272, -585, 2210]]
  ![![277, 0, 0, 0, 0]] where
 M := ![![![-277, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-418, -59, -145, -29, -198]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![-418, -59, -145, -29, -198]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![0, 0, 0, 281, 0], ![127, 67, 198, 152, 1]] where
  M :=![![![-418, -59, -145, -29, -198], ![-879, -196, -315, -63, -372], ![-1677, -513, -694, -195, -750], ![-1353, -435, -669, -190, -774], ![78, 50, -20, -4, -37]]]
  hmulB := by decide  
  f := ![![![-2, 1, -1, 1, 0]], ![![3, -2, 3, -3, 6]], ![![15, -9, -2, 3, -12]], ![![-21, 21, -9, 4, 0]], ![![-1, 5, -6, 4, -7]]]
  g := ![![![88, 47, 139, 107, -198], ![165, 88, 261, 201, -372], ![333, 177, 526, 405, -750], ![345, 183, 543, 418, -774], ![17, 9, 26, 20, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 4 2 8 [41, 218, 13, 181, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 80, 52, 112], [38, 3, 166, 91], [8, 197, 63, 78], [0, 1]]
 g := ![![[218, 277, 120, 223], [102, 180, 43], [172, 24, 72], [35, 177, 247, 124], [202, 75, 136, 66], [120, 131, 165], [1], []], ![[279, 216, 218, 204, 203, 4], [181, 69, 277], [78, 270, 265], [84, 89, 139, 78, 94, 78], [159, 252, 53, 217, 202, 90], [153, 254, 183], [248, 257, 101], [269, 143, 180]], ![[129, 78, 163, 106, 271, 188], [14, 27, 33], [138, 56, 31], [171, 111, 128, 37, 197, 120], [105, 93, 23, 114, 83, 77], [110, 147, 85], [44, 117, 272], [3, 138, 132]], ![[234, 270, 74, 192, 229, 50], [259, 277, 279], [160, 4, 28], [171, 84, 153, 206, 119, 195], [264, 178, 110, 116, 242, 128], [99, 166, 4], [204, 74, 202], [278, 28, 183]]]
 h' := ![![[54, 80, 52, 112], [90, 204, 83, 144], [30, 216, 229, 18], [251, 273, 128, 51], [148, 83, 152, 168], [133, 114, 186, 176], [240, 63, 268, 100], [0, 0, 1], [0, 1]], ![[38, 3, 166, 91], [131, 256, 249, 208], [33, 172, 38, 106], [155, 131, 95, 69], [228, 57, 131, 128], [259, 203, 219, 233], [120, 264, 277, 78], [36, 54, 32, 35], [54, 80, 52, 112]], ![[8, 197, 63, 78], [190, 252, 14, 114], [157, 40, 279, 186], [241, 227, 109, 84], [44, 271, 208, 158], [249, 258, 78, 138], [194, 57, 216, 101], [197, 98, 132, 122], [38, 3, 166, 91]], ![[0, 1], [75, 131, 216, 96], [4, 134, 16, 252], [246, 212, 230, 77], [121, 151, 71, 108], [107, 268, 79, 15], [191, 178, 82, 2], [187, 129, 116, 124], [8, 197, 63, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [103, 236, 21], []]
 b := ![[], [], [22, 159, 81, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 4
  hpos := by decide
  P := [41, 218, 13, 181, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-158057379, 159642344, -42750016, 2624580, 80797424]
  a := ![14, -4, 12, -22, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-37079467, -18696744, -57084128, -43696028, 80797424]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 6234839521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -1, 1, -1, 0]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![2, -1, 1, -1, 0]] 
 ![![281, 0, 0, 0, 0], ![211, 1, 0, 0, 0], ![158, 0, 1, 0, 0], ![226, 0, 0, 1, 0], ![58, 0, 0, 0, 1]] where
  M :=![![![2, -1, 1, -1, 0], ![-3, 2, -3, 3, -6], ![-15, 9, 2, -3, 12], ![21, -21, 9, -4, 0], ![6, -2, -4, 4, -7]]]
  hmulB := by decide  
  f := ![![![418, 59, 145, 29, 198]], ![![317, 45, 110, 22, 150]], ![![241, 35, 84, 17, 114]], ![![341, 49, 119, 24, 162]], ![![86, 12, 30, 6, 41]]]
  g := ![![![1, -1, 1, -1, 0], ![-1, 2, -3, 3, -6], ![-8, 9, 2, -3, 12], ![14, -21, 9, -4, 0], ![2, -2, -4, 4, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N1 : Nat.card (O ⧸ I281N1) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N1)

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := prime_ideal_of_norm_prime hp281.out _ NI281N1
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![-418, -59, -145, -29, -198]] ![![2, -1, 1, -1, 0]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![-281, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3973128, -944235, -1636323, -408233, -1940780]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![-3973128, -944235, -1636323, -408233, -1940780]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![193, 139, 1, 0, 0], ![29, 200, 0, 1, 0], ![111, 264, 0, 0, 1]] where
  M :=![![![-3973128, -944235, -1636323, -408233, -1940780], ![-8987819, -2136124, -3701481, -923633, -4390178], ![-20331611, -4832577, -8373568, -2089151, -9931976], ![-18503769, -4397127, -7620687, -1901188, -9038352], ![201614, 47986, 83174, 20602, 98773]]]
  hmulB := by decide  
  f := ![![![534436, 298787, -146585, -101997, -291706]], ![![-1472815, 869266, -196913, 100533, -903688]], ![![-370630, 631562, -196096, -18735, -643860]], ![![-983445, 639630, -152498, 60815, -663136]], ![![-1156334, 924849, -240639, 53077, -954009]]]
  g := ![![![1904956, 2899354, -1636323, -408233, -1940780], ![4309163, 6558669, -3701481, -923633, -4390178], ![9748416, 14837333, -8373568, -2089151, -9931976], ![8871662, 13502618, -7620687, -1901188, -9038352], ![-96863, -147384, 83174, 20602, 98773]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 2 2 8 [205, 263, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 282], [0, 1]]
 g := ![![[276, 94], [50, 9], [116], [102, 137], [219, 129], [97], [117], [1]], ![[175, 189], [230, 274], [116], [12, 146], [252, 154], [97], [117], [1]]]
 h' := ![![[20, 282], [221, 159], [167, 3], [32, 207], [102, 234], [15, 176], [211, 83], [78, 20], [0, 1]], ![[0, 1], [5, 124], [227, 280], [210, 76], [254, 49], [139, 107], [173, 200], [195, 263], [20, 282]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [256, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 2
  hpos := by decide
  P := [205, 263, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18828, 7569, 11301, 2715, 18360]
  a := ![29, 19, 20, 10, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15120, -24570, 11301, 2715, 18360]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 80089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15965, 7700, -3944, -2916, -7478]] i)))

def SI283N1: IdealEqSpanCertificate' Table ![![15965, 7700, -3944, -2916, -7478]] 
 ![![283, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![259, 0, 1, 0, 0], ![108, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![15965, 7700, -3944, -2916, -7478], ![-38660, 24061, -5610, 2506, -24974], ![-92378, 8184, 4099, 11248, -9938], ![16326, -40608, 13176, 2191, 41262], ![60578, -25828, 4576, -5194, 27159]]]
  hmulB := by decide  
  f := ![![![2812374699, 668414828, 1158254800, 288989840, 1373775446]], ![![360363290, 85647253, 148412838, 37029678, 176028550]], ![![2624724869, 623816244, 1080972667, 269707596, 1282113148]], ![![1119555174, 266083776, 461080152, 115041595, 546874998]], ![![218125348, 51841676, 89833240, 22413802, 106548835]]]
  g := ![![![4435, 7700, -3944, -2916, -7478], ![3092, 24061, -5610, 2506, -24974], ![-8581, 8184, 4099, 11248, -9938], ![-11166, -40608, 13176, 2191, 41262], ![-1000, -25828, 4576, -5194, 27159]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N1 : Nat.card (O ⧸ I283N1) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N1)

lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := prime_ideal_of_norm_prime hp283.out _ NI283N1

def I283N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3342, 795, 1377, 343, 1634]] i)))

def SI283N2: IdealEqSpanCertificate' Table ![![3342, 795, 1377, 343, 1634]] 
 ![![283, 0, 0, 0, 0], ![125, 1, 0, 0, 0], ![223, 0, 1, 0, 0], ![150, 0, 0, 1, 0], ![107, 0, 0, 0, 1]] where
  M :=![![![3342, 795, 1377, 343, 1634], ![7565, 1794, 3115, 777, 3692], ![17099, 4073, 7040, 1761, 8354], ![15567, 3699, 6417, 1594, 7614], ![-164, -46, -68, -18, -85]]]
  hmulB := by decide  
  f := ![![![-12946, 3349, -205, 1339, -3608]], ![![-5755, 1463, -82, 598, -1578]], ![![-10119, 2586, -149, 1050, -2788]], ![![-6741, 1773, -117, 694, -1908]], ![![-4878, 1295, -89, 501, -1393]]]
  g := ![![![-2224, 795, 1377, 343, 1634], ![-5028, 1794, 3115, 777, 3692], ![-11378, 4073, 7040, 1761, 8354], ![-10359, 3699, 6417, 1594, 7614], ![115, -46, -68, -18, -85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N2 : Nat.card (O ⧸ I283N2) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N2)

lemma isPrimeI283N2 : Ideal.IsPrime I283N2 := prime_ideal_of_norm_prime hp283.out _ NI283N2

def I283N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1673, 408, -18, 176, -442]] i)))

def SI283N3: IdealEqSpanCertificate' Table ![![-1673, 408, -18, 176, -442]] 
 ![![283, 0, 0, 0, 0], ![268, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![126, 0, 0, 0, 1]] where
  M :=![![![-1673, 408, -18, 176, -442], ![-1240, -631, 318, 230, 614], ![3146, -1920, 443, -208, 1994], ![4296, 12, -330, -565, 66], ![472, 1088, -422, -178, -1089]]]
  hmulB := by decide  
  f := ![![![-351, -1384, 178, -628, -350]], ![![-344, -1311, 158, -590, -346]], ![![-116, -272, 31, -140, -58]], ![![-6, -132, 18, -49, -42]], ![![-154, -616, 70, -270, -173]]]
  g := ![![![-203, 408, -18, 176, -442], ![240, -631, 318, 230, 614], ![864, -1920, 443, -208, 1994], ![78, 12, -330, -565, 66], ![-446, 1088, -422, -178, -1089]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N3 : Nat.card (O ⧸ I283N3) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N3)

lemma isPrimeI283N3 : Ideal.IsPrime I283N3 := prime_ideal_of_norm_prime hp283.out _ NI283N3
def MulI283N0 : IdealMulLeCertificate' Table 
  ![![-3973128, -944235, -1636323, -408233, -1940780]] ![![15965, 7700, -3944, -2916, -7478]]
  ![![-124, 137, -83, 51, -18]] where
 M := ![![![-124, 137, -83, 51, -18]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI283N1 : IdealMulLeCertificate' Table 
  ![![-124, 137, -83, 51, -18]] ![![3342, 795, 1377, 343, 1634]]
  ![![-351, -1384, 178, -628, -350]] where
 M := ![![![-351, -1384, 178, -628, -350]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI283N2 : IdealMulLeCertificate' Table 
  ![![-351, -1384, 178, -628, -350]] ![![-1673, 408, -18, 176, -442]]
  ![![283, 0, 0, 0, 0]] where
 M := ![![![283, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC283 : ContainsPrimesAboveP 283 ![I283N0, I283N1, I283N2, I283N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI283N0
    exact isPrimeI283N1
    exact isPrimeI283N2
    exact isPrimeI283N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 283 (by decide) (𝕀 ⊙ MulI283N0 ⊙ MulI283N1 ⊙ MulI283N2)
instance hp293 : Fact (Nat.Prime 293) := {out := by norm_num}

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-479645, -117251, -199429, -48266, -239530]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![-479645, -117251, -199429, -48266, -239530]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![0, 0, 0, 293, 0], ![236, 79, 17, 27, 1]] where
  M :=![![![-479645, -117251, -199429, -48266, -239530], ![-1102918, -248280, -453313, -111062, -529126], ![-2449690, -609041, -999530, -266438, -1195498], ![-2239194, -538191, -942051, -213031, -1132500], ![5491, 25108, 1976, 6189, 15921]]]
  hmulB := by decide  
  f := ![![![-7395, 39809, -13571, -3276, -40294]], ![![-171004, 56346, -7037, 16428, -59950]], ![![-190516, -41713, 29252, 29448, 38618]], ![![206910, -132699, 31419, -12995, 137628]], ![![-43315, 32452, -8236, 2222, -33525]]]
  g := ![![![191295, 64183, 13217, 21908, -239530], ![422426, 141818, 29153, 48380, -529126], ![954566, 320257, 65952, 109256, -1195498], ![904542, 303513, 62493, 103633, -1132500], ![-12805, -4207, -917, -1446, 15921]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 4 2 8 [94, 256, 151, 222, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [209, 34, 134, 285], [148, 221, 249, 84], [7, 37, 203, 217], [0, 1]]
 g := ![![[57, 223, 71, 292], [70, 273, 209], [35, 133, 173, 64], [201, 93, 197], [113, 127, 232], [46, 80, 105, 60], [1], []], ![[27, 277, 173, 257, 4, 8], [1, 203, 143], [224, 132, 209, 6, 92, 106], [12, 107, 226], [203, 27, 95], [65, 31, 156, 223, 195, 30], [27, 157, 124], [4, 56, 64]], ![[154, 121, 181, 136, 212, 156], [196, 226, 152], [188, 218, 125, 280, 206, 53], [51, 259, 240], [193, 77, 71], [11, 215, 100, 27, 259, 77], [242, 11, 256], [186, 172, 24]], ![[201, 223, 270, 2, 58, 110], [78, 18, 100], [178, 58, 274, 187, 270, 131], [155, 12, 56], [278, 240, 81], [216, 217, 264, 74, 196, 207], [88, 69, 67], [143, 98, 209]]]
 h' := ![![[209, 34, 134, 285], [253, 13, 164, 138], [226, 206, 255, 76], [54, 197, 148, 8], [279, 51, 129, 37], [71, 88, 284, 143], [199, 37, 142, 71], [0, 0, 1], [0, 1]], ![[148, 221, 249, 84], [104, 41, 266, 155], [265, 151, 163, 27], [112, 165, 88, 222], [19, 80, 82, 144], [254, 74, 168, 55], [64, 236, 10, 41], [234, 13, 173, 257], [209, 34, 134, 285]], ![[7, 37, 203, 217], [233, 60, 199, 48], [265, 63, 19, 200], [181, 246, 44, 25], [64, 111, 219, 151], [178, 287, 196, 86], [145, 155, 10, 65], [25, 167, 119, 277], [148, 221, 249, 84]], ![[0, 1], [114, 179, 250, 245], [282, 166, 149, 283], [66, 271, 13, 38], [239, 51, 156, 254], [292, 137, 231, 9], [125, 158, 131, 116], [85, 113, 0, 52], [7, 37, 203, 217]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [262, 143, 206], []]
 b := ![[], [], [283, 140, 161, 158], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 4
  hpos := by decide
  P := [94, 256, 151, 222, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3771474, -4417988, 3453284, -2632024, 2263924]
  a := ![3, -3, 3, -6, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1810630, -625488, -119568, -217604, 2263924]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 7370050801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7395, -39809, 13571, 3276, 40294]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![7395, -39809, 13571, 3276, 40294]] 
 ![![293, 0, 0, 0, 0], ![130, 1, 0, 0, 0], ![94, 0, 1, 0, 0], ![271, 0, 0, 1, 0], ![274, 0, 0, 0, 1]] where
  M :=![![![7395, -39809, 13571, 3276, 40294], ![171004, -56346, 7037, -16428, 59950], ![190516, 41713, -29252, -29448, -38618], ![-206910, 132699, -31419, 12995, -137628], ![-215443, 45828, 66, 23381, -50147]]]
  hmulB := by decide  
  f := ![![![479645, 117251, 199429, 48266, 239530]], ![![216576, 52870, 90031, 21794, 108082]], ![![162240, 39695, 67392, 16394, 80926]], ![![451273, 110284, 187670, 45369, 225410]], ![![448523, 109562, 186490, 45115, 223943]]]
  g := ![![![-27377, -39809, 13571, 3276, 40294], ![-17542, -56346, 7037, -16428, 59950], ![54878, 41713, -29252, -29448, -38618], ![67181, 132699, -31419, 12995, -137628], ![4180, 45828, 66, 23381, -50147]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N1 : Nat.card (O ⧸ I293N1) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N1)

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := prime_ideal_of_norm_prime hp293.out _ NI293N1
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![-479645, -117251, -199429, -48266, -239530]] ![![7395, -39809, 13571, 3276, 40294]]
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


lemma PB307I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 306 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 306 (by omega)

def PB307I6 : PrimesBelowBoundCertificateInterval O 251 306 307 where
  m := 8
  g := ![1, 4, 3, 2, 3, 2, 4, 2]
  P := ![257, 263, 269, 271, 277, 281, 283, 293]
  hP := PB307I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0]
    · exact ![I263N0, I263N1, I263N2, I263N3]
    · exact ![I269N0, I269N1, I269N2]
    · exact ![I271N0, I271N1]
    · exact ![I277N0, I277N1, I277N2]
    · exact ![I281N0, I281N1]
    · exact ![I283N0, I283N1, I283N2, I283N3]
    · exact ![I293N0, I293N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1121154893057]
    · exact ![69169, 263, 263, 263]
    · exact ![19465109, 269, 269]
    · exact ![5393580481, 271]
    · exact ![21253933, 277, 277]
    · exact ![6234839521, 281]
    · exact ![80089, 283, 283, 283]
    · exact ![7370050801, 293]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
      exact NI263N2
      exact NI263N3
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
      exact NI269N2
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
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
      exact NI283N1
      exact NI283N2
      exact NI283N3
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
  β := ![I263N1, I263N2, I263N3, I269N1, I269N2, I271N1, I277N1, I277N2, I281N1, I283N1, I283N2, I283N3, I293N1]
  Il := ![[], [I263N1, I263N2, I263N3], [I269N1, I269N2], [I271N1], [I277N1, I277N2], [I281N1], [I283N1, I283N2, I283N3], [I293N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
