
import IdealArithmetic.Examples.NF5_3_1215000000_2.RI5_3_1215000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![883, 466, 227, -51, -114]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![883, 466, 227, -51, -114]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![45, 45, 199, 1, 0], ![166, 217, 175, 0, 1]] where
  M :=![![![883, 466, 227, -51, -114], ![684, 365, 188, -54, -102], ![612, 244, 123, -102, -108], ![648, 292, 110, -179, -138], ![126, 66, -21, -225, -107]]]
  hmulB := by decide  
  f := ![![![95, -86, 71, -117, 60]], ![![-360, 321, -274, 456, -234]], ![![1404, -1244, 1051, -1770, 912]], ![![1035, -917, 774, -1304, 672]], ![![724, -641, 538, -909, 469]]]
  g := ![![![86, 107, 118, -51, -114], ![78, 97, 112, -54, -102], ![90, 110, 153, -102, -108], ![123, 149, 233, -179, -138], ![109, 130, 247, -225, -107]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [223, 78, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 134, 92], [175, 122, 165], [0, 1]]
 g := ![![[213, 47, 176], [71, 226], [168, 221], [129, 123], [0, 34], [95, 120], [221, 1], []], ![[210, 123, 94, 197], [90, 133], [11, 64], [64, 122], [132, 88], [229, 208], [66, 235], [82, 240]], ![[0, 189, 10, 129], [231, 226], [33, 34], [241, 8], [89, 236], [187, 173], [155, 223], [9, 240]]]
 h' := ![![[46, 134, 92], [66, 123, 144], [42, 83, 212], [193, 38, 161], [144, 108, 196], [12, 42, 88], [61, 15, 190], [0, 0, 1], [0, 1]], ![[175, 122, 165], [10, 10, 100], [88, 207, 90], [182, 225, 8], [233, 133, 181], [194, 45, 208], [115, 8, 145], [21, 214, 122], [46, 134, 92]], ![[0, 1], [0, 124, 13], [192, 224, 212], [163, 251, 88], [129, 16, 137], [207, 170, 218], [187, 234, 179], [91, 43, 134], [175, 122, 165]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150, 27], []]
 b := ![[], [150, 237, 131], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [223, 78, 36, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11593559, 4672938, -5852055, -18677976, -12117623]
  a := ![0, 7, -7, -5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11142521, 13520257, 22691242, -18677976, -12117623]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 16974593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, 50, -42, 70, -36]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![-55, 50, -42, 70, -36]] 
 ![![257, 0, 0, 0, 0], ![199, 1, 0, 0, 0], ![234, 0, 1, 0, 0], ![128, 0, 0, 1, 0], ![161, 0, 0, 0, 1]] where
  M :=![![![-55, 50, -42, 70, -36], ![216, -191, 162, -272, 140], ![-840, 746, -625, 1054, -544], ![880, -782, 654, -1101, 568], ![-1616, 1438, -1202, 2022, -1043]]]
  hmulB := by decide  
  f := ![![![377, 70, 6, -230, -132]], ![![295, 55, 4, -182, -104]], ![![354, 66, 3, -226, -128]], ![![208, 38, -2, -145, -80]], ![![265, 48, -4, -188, -103]]]
  g := ![![![-13, 50, -42, 70, -36], ![49, -191, 162, -272, 140], ![-196, 746, -625, 1054, -544], ![206, -782, 654, -1101, 568], ![-379, 1438, -1202, 2022, -1043]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1

def I257N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 0, -1, -1, 0]] i)))

def SI257N2: IdealEqSpanCertificate' Table ![![1, 0, -1, -1, 0]] 
 ![![257, 0, 0, 0, 0], ![231, 1, 0, 0, 0], ![95, 0, 1, 0, 0], ![161, 0, 0, 1, 0], ![153, 0, 0, 0, 1]] where
  M :=![![![1, 0, -1, -1, 0], ![0, 3, 0, -4, -2], ![12, -2, -1, -16, -8], ![20, 2, -6, -29, -14], ![26, 8, -7, -45, -19]]]
  hmulB := by decide  
  f := ![![![-755, -436, -205, 41, 102]], ![![-681, -393, -185, 37, 92]], ![![-281, -162, -76, 15, 38]], ![![-475, -274, -129, 26, 64]], ![![-449, -260, -122, 24, 61]]]
  g := ![![![1, 0, -1, -1, 0], ![1, 3, 0, -4, -2], ![17, -2, -1, -16, -8], ![27, 2, -6, -29, -14], ![35, 8, -7, -45, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N2 : Nat.card (O ⧸ I257N2) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N2)

lemma isPrimeI257N2 : Ideal.IsPrime I257N2 := prime_ideal_of_norm_prime hp257.out _ NI257N2
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![883, 466, 227, -51, -114]] ![![-55, 50, -42, 70, -36]]
  ![![755, 436, 205, -41, -102]] where
 M := ![![![755, 436, 205, -41, -102]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI257N1 : IdealMulLeCertificate' Table 
  ![![755, 436, 205, -41, -102]] ![![1, 0, -1, -1, 0]]
  ![![257, 0, 0, 0, 0]] where
 M := ![![![-257, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1, I257N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
    exact isPrimeI257N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0 ⊙ MulI257N1)
instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0, 0, 0]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0, 0, 0]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![0, 0, 0, 263, 0], ![0, 0, 0, 0, 263]] where
  M :=![![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![0, 0, 0, 263, 0], ![0, 0, 0, 0, 263]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 5 2 8 [101, 77, 213, 162, 238, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 71, 179, 43, 146], [171, 249, 83, 232, 220], [38, 186, 12, 84, 250], [9, 19, 252, 167, 173], [0, 1]]
 g := ![![[192, 11, 172, 33, 122], [10, 214, 43, 19, 122], [225, 189, 221, 57, 147], [154, 230, 218, 70], [61, 16, 67, 124], [211, 200, 25, 1], [], []], ![[44, 17, 57, 179, 221, 237, 159, 130], [83, 191, 79, 52, 53, 20, 116, 237], [96, 34, 28, 208, 33, 69, 114, 84], [119, 162, 157, 208], [156, 153, 231, 223], [211, 111, 255, 12], [209, 141, 240, 196], [74, 50, 257, 13]], ![[163, 122, 24, 109, 103, 143, 77, 152], [55, 113, 70, 112, 82, 59, 56, 255], [40, 10, 15, 200, 91, 97, 121, 84], [134, 45, 7, 35], [250, 122, 182, 78], [27, 102, 93, 249], [120, 219, 203, 4], [168, 5, 236, 8]], ![[30, 158, 36, 25, 122, 120, 188, 226], [218, 176, 181, 228, 7, 61, 26, 91], [175, 106, 69, 86, 153, 69, 99, 241], [29, 79, 117, 200], [107, 168, 121, 172], [204, 21, 254, 242], [117, 178, 134, 66], [24, 146, 200, 169]], ![[164, 230, 37, 188, 201, 183, 34, 151], [247, 126, 17, 16, 101, 29, 233, 69], [63, 233, 206, 189, 157, 170, 55, 173], [81, 49, 126, 172], [232, 166, 164, 35], [156, 77, 131, 178], [159, 144, 15, 198], [118, 224, 175, 210]]]
 h' := ![![[70, 71, 179, 43, 146], [42, 111, 130, 132, 139], [156, 149, 201, 96, 139], [163, 101, 16, 10, 161], [215, 80, 226, 114, 164], [255, 110, 252, 92, 85], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[171, 249, 83, 232, 220], [231, 207, 127, 1, 150], [57, 150, 119, 108, 212], [19, 169, 208, 79, 159], [27, 18, 86, 14, 205], [23, 20, 221, 107, 152], [174, 150, 138, 152, 217], [56, 244, 49, 59, 14], [70, 71, 179, 43, 146]], ![[38, 186, 12, 84, 250], [84, 34, 214, 195, 32], [189, 223, 228, 249, 116], [169, 18, 95, 173, 39], [194, 199, 175, 190, 78], [249, 77, 92, 48, 135], [95, 168, 164, 145, 182], [175, 181, 137, 40, 261], [171, 249, 83, 232, 220]], ![[9, 19, 252, 167, 173], [187, 200, 209, 119, 34], [121, 184, 78, 169, 16], [170, 230, 29, 121, 166], [224, 1, 45, 182, 48], [118, 245, 56, 148, 232], [205, 148, 116, 25, 105], [72, 172, 6, 201, 131], [38, 186, 12, 84, 250]], ![[0, 1], [166, 237, 109, 79, 171], [145, 83, 163, 167, 43], [180, 8, 178, 143, 1], [58, 228, 257, 26, 31], [168, 74, 168, 131, 185], [251, 60, 108, 204, 21], [261, 192, 70, 226, 120], [9, 19, 252, 167, 173]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [220, 199, 189, 88], [], [], []]
 b := ![[], [32, 164, 96, 157, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 5
  hpos := by decide
  P := [101, 77, 213, 162, 238, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5239477789297794214, 2083465691284571100, -2618625152556200328, -8432042056015649333, -5441750511733235471]
  a := ![3, 62, -124, -1, -249]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![19921968780599978, 7921922780549700, -9956749629491256, -32060996410705891, -20691066584537017]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 1258284197543 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def PBC263 : ContainsPrimesAboveP 263 ![I263N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![263, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 263 (by decide) 𝕀

instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-313, 381, 38, -71, 8]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![-313, 381, 38, -71, 8]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![125, 161, 155, 1, 0], ![196, 266, 69, 0, 1]] where
  M :=![![![-313, 381, 38, -71, 8], ![-48, -256, 272, 91, -142], ![852, -837, -437, 55, 182], ![-96, 229, -170, -6, 50], ![-552, 291, 636, -87, -193]]]
  hmulB := by decide  
  f := ![![![571, 85, -152, -887, -412]], ![![2472, 374, -650, -3815, -1774]], ![![10644, 1615, -2791, -16409, -7630]], ![![7951, 1205, -2087, -12263, -5702]], ![![5696, 862, -1497, -8790, -4087]]]
  g := ![![![26, 36, 39, -71, 8], ![61, 85, -15, 91, -142], ![-155, -216, -80, 55, 182], ![-34, -45, -10, -6, 50], ![179, 244, 102, -87, -193]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [152, 211, 225, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [178, 167, 73], [135, 101, 196], [0, 1]]
 g := ![![[59, 105, 212], [215, 20], [121, 183, 169], [20, 74, 208], [23, 51], [0, 216], [44, 1], []], ![[127, 128, 131, 246], [163, 180], [48, 91, 36, 30], [192, 173, 61, 260], [45, 169], [94, 36], [90, 248], [80, 218]], ![[10, 3, 160, 154], [127, 80], [235, 57, 268, 190], [239, 176, 80, 99], [33, 105], [238, 265], [187, 182], [226, 218]]]
 h' := ![![[178, 167, 73], [185, 50, 88], [169, 20, 17], [188, 41, 256], [39, 94, 132], [24, 46, 201], [37, 248, 111], [0, 0, 1], [0, 1]], ![[135, 101, 196], [217, 245, 164], [194, 200, 218], [78, 118, 66], [241, 178, 19], [25, 67, 256], [165, 169, 263], [156, 21, 101], [178, 167, 73]], ![[0, 1], [9, 243, 17], [131, 49, 34], [174, 110, 216], [188, 266, 118], [239, 156, 81], [259, 121, 164], [13, 248, 167], [135, 101, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107, 166], []]
 b := ![[], [25, 166, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [152, 211, 225, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9171625, 4294760, -5154039, -14995332, -10331838]
  a := ![1, 6, -8, -3, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14530217, 19207480, 11271447, -14995332, -10331838]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![571, 85, -152, -887, -412]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![571, 85, -152, -887, -412]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![112, 72, 1, 0, 0], ![129, 216, 0, 1, 0], ![23, 214, 0, 0, 1]] where
  M :=![![![571, 85, -152, -887, -412], ![2472, 374, -650, -3815, -1774], ![10644, 1615, -2791, -16409, -7630], ![19632, 2981, -5148, -30262, -14074], ![28320, 4299, -7422, -43647, -20297]]]
  hmulB := by decide  
  f := ![![![-313, 381, 38, -71, 8]], ![![-48, -256, 272, 91, -142]], ![![-140, 87, 87, -5, -34]], ![![-189, -22, 236, 39, -110]], ![![-67, -170, 222, 66, -113]]]
  g := ![![![526, 1081, -152, -887, -412], ![2261, 4650, -650, -3815, -1774], ![9723, 19999, -2791, -16409, -7630], ![17932, 36885, -5148, -30262, -14074], ![25862, 53197, -7422, -43647, -20297]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P1 : CertificateIrreducibleZModOfList' 269 2 2 8 [249, 231, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 268], [0, 1]]
 g := ![![[244, 121], [97], [122, 13], [144, 121], [44], [189], [99], [1]], ![[0, 148], [97], [78, 256], [169, 148], [44], [189], [99], [1]]]
 h' := ![![[38, 268], [149, 258], [19, 108], [190, 33], [178, 258], [81, 154], [228, 171], [20, 38], [0, 1]], ![[0, 1], [0, 11], [88, 161], [99, 236], [29, 11], [15, 115], [1, 98], [119, 231], [38, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [155, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N1 : CertifiedPrimeIdeal' SI269N1 269 where
  n := 2
  hpos := by decide
  P := [249, 231, 1]
  hirr := P269P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-91285, -259273, 275209, 199430, 405524]
  a := ![1, -25, 48, -1, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-245235, -557373, 275209, 199430, 405524]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N1 B_one_repr
lemma NI269N1 : Nat.card (O ⧸ I269N1) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![-313, 381, 38, -71, 8]] ![![571, 85, -152, -887, -412]]
  ![![269, 0, 0, 0, 0]] where
 M := ![![![269, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55, -58, 66, -82, 36]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![55, -58, 66, -82, 36]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![175, 186, 1, 0, 0], ![229, 241, 0, 1, 0], ![255, 116, 0, 0, 1]] where
  M :=![![![55, -58, 66, -82, 36], ![-216, 179, -206, 332, -164], ![984, -834, 717, -1270, 664], ![-1072, 958, -770, 1309, -680], ![1976, -1798, 1442, -2394, 1235]]]
  hmulB := by decide  
  f := ![![![-7063, -3634, -1842, 382, 924]], ![![-5544, -2831, -1410, 400, 764]], ![![-8383, -4298, -2161, 524, 1124]], ![![-10917, -5597, -2814, 683, 1464]], ![![-9023, -4632, -2336, 536, 1199]]]
  g := ![![![-7, 12, 66, -82, 36], ![6, -83, -206, 332, -164], ![-11, 350, 717, -1270, 664], ![27, -341, -770, 1309, -680], ![-63, 604, 1442, -2394, 1235]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [141, 169, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 270], [0, 1]]
 g := ![![[80, 148], [230, 224], [198, 103], [81, 121], [31], [20], [106], [1]], ![[0, 123], [43, 47], [135, 168], [228, 150], [31], [20], [106], [1]]]
 h' := ![![[102, 270], [90, 31], [266, 148], [232, 153], [268, 11], [158, 207], [57, 205], [130, 102], [0, 1]], ![[0, 1], [0, 240], [186, 123], [120, 118], [35, 260], [134, 64], [100, 66], [236, 169], [102, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [98, 200]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 2
  hpos := by decide
  P := [141, 169, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5451, -27435, 24928, 323, 29848]
  a := ![-1, 7, -17, 8, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-44436, -30274, 24928, 323, 29848]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![81, 11, -21, -124, -58]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![81, 11, -21, -124, -58]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![245, 227, 1, 0, 0], ![152, 144, 0, 1, 0], ![183, 77, 0, 0, 1]] where
  M :=![![![81, 11, -21, -124, -58], ![348, 52, -92, -535, -248], ![1488, 231, -391, -2299, -1070], ![2752, 417, -720, -4242, -1972], ![3970, 601, -1043, -6114, -2845]]]
  hmulB := by decide  
  f := ![![![-509, -239, -149, 22, 72]], ![![-432, -166, -68, 7, 44]], ![![-823, -356, -192, 26, 102]], ![![-516, -223, -120, 16, 64]], ![![-467, -208, -120, 17, 61]]]
  g := ![![![128, 100, -21, -124, -58], ![552, 432, -92, -535, -248], ![2371, 1854, -391, -2299, -1070], ![4372, 3419, -720, -4242, -1972], ![6308, 4933, -1043, -6114, -2845]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P1 : CertificateIrreducibleZModOfList' 271 2 2 8 [9, 234, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 270], [0, 1]]
 g := ![![[26, 241], [172, 10], [255, 81], [234, 1], [35], [224], [14], [1]], ![[0, 30], [0, 261], [0, 190], [0, 270], [35], [224], [14], [1]]]
 h' := ![![[37, 270], [78, 181], [144, 84], [62, 262], [37, 270], [9, 199], [226, 123], [262, 37], [0, 1]], ![[0, 1], [0, 90], [0, 187], [0, 9], [0, 1], [55, 72], [170, 148], [5, 234], [37, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [148]]
 b := ![[], [257, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N1 : CertifiedPrimeIdeal' SI271N1 271 where
  n := 2
  hpos := by decide
  P := [9, 234, 1]
  hirr := P271P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20097, -17576, 18968, -30672, 16080]
  a := ![0, 4, 16, -26, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10729, -4224, 18968, -30672, 16080]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N1 B_one_repr
lemma NI271N1 : Nat.card (O ⧸ I271N1) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N1

def I271N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, -63, 10, 13, -8]] i)))

def SI271N2: IdealEqSpanCertificate' Table ![![35, -63, 10, 13, -8]] 
 ![![271, 0, 0, 0, 0], ![129, 1, 0, 0, 0], ![161, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![159, 0, 0, 0, 1]] where
  M :=![![![35, -63, 10, 13, -8], ![48, -12, -60, -5, 26], ![-156, 191, 43, -29, -10], ![-16, -7, 34, 2, -14], ![152, -145, -88, 21, 27]]]
  hmulB := by decide  
  f := ![![![-99627, -51389, -26132, 4991, 12876]], ![![-47709, -24609, -12514, 2390, 6166]], ![![-59409, -30644, -15583, 2976, 7678]], ![![-14563, -7512, -3820, 729, 1882]], ![![-58459, -30154, -15334, 2928, 7555]]]
  g := ![![![27, -63, 10, 13, -8], ![27, -12, -60, -5, 26], ![-107, 191, 43, -29, -10], ![-9, -7, 34, 2, -14], ![103, -145, -88, 21, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N2 : Nat.card (O ⧸ I271N2) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N2)

lemma isPrimeI271N2 : Ideal.IsPrime I271N2 := prime_ideal_of_norm_prime hp271.out _ NI271N2
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![55, -58, 66, -82, 36]] ![![81, 11, -21, -124, -58]]
  ![![-265, 277, -133, 216, -142]] where
 M := ![![![-265, 277, -133, 216, -142]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI271N1 : IdealMulLeCertificate' Table 
  ![![-265, 277, -133, 216, -142]] ![![35, -63, 10, 13, -8]]
  ![![271, 0, 0, 0, 0]] where
 M := ![![![-271, 7046, -5149, -3523, 3794]]]
 hmul := by decide  
 g := ![![![![-1, 26, -19, -13, 14]]]]
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

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 18, 40, 56, 34]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![37, 18, 40, 56, 34]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![0, 0, 0, 277, 0], ![107, 82, 213, 132, 1]] where
  M :=![![![37, 18, 40, 56, 34], ![-204, 43, 34, 380, 112], ![-672, -282, 389, 1154, 760], ![-1812, -58, 302, 2805, 1060], ![-2040, -678, 894, 3246, 1951]]]
  hmulB := by decide  
  f := ![![![25, -26, -8, 4, 2]], ![![-12, 35, -14, -8, 8]], ![![-48, 34, 41, -2, -16]], ![![12, -22, 6, 5, -4]], ![![-25, 16, 27, 0, -11]]]
  g := ![![![-13, -10, -26, -16, 34], ![-44, -33, -86, -52, 112], ![-296, -226, -583, -358, 760], ![-416, -314, -814, -495, 1060], ![-761, -580, -1497, -918, 1951]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 4 2 8 [5, 268, 63, 125, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 113, 40, 211], [121, 152, 88, 258], [4, 11, 149, 85], [0, 1]]
 g := ![![[50, 6, 228, 165], [59, 106, 243], [202, 95, 97, 9], [74, 217, 76], [168, 110, 252, 70], [56, 240, 113], [1], []], ![[33, 147, 268, 173, 189, 214], [193, 32, 48], [129, 65, 261, 190, 112, 133], [217, 57, 130], [230, 11, 258, 160, 158, 79], [245, 2, 274], [43, 196, 27], [244, 65, 201]], ![[141, 85, 223, 207, 233, 207], [159, 54, 130], [40, 115, 226, 147, 49, 112], [35, 73, 252], [169, 253, 195, 127, 66, 91], [46, 127, 57], [4, 198, 40], [81, 6, 84]], ![[118, 35, 155, 22, 11, 141], [96, 273, 63], [193, 79, 199, 260, 197, 194], [225, 38, 67], [71, 131, 249, 265, 181, 49], [243, 66, 21], [126, 161, 255], [151, 18, 23]]]
 h' := ![![[27, 113, 40, 211], [168, 49, 261, 188], [98, 102, 230, 215], [265, 145, 258, 274], [268, 61, 267, 82], [22, 45, 163, 65], [272, 9, 214, 152], [0, 0, 1], [0, 1]], ![[121, 152, 88, 258], [228, 102, 127, 40], [202, 56, 172, 243], [27, 151, 70, 163], [275, 33, 196, 31], [24, 100, 24, 147], [153, 157, 150, 44], [63, 217, 245, 113], [27, 113, 40, 211]], ![[4, 11, 149, 85], [167, 17, 130, 184], [193, 20, 157, 246], [61, 0, 68, 90], [201, 222, 247, 254], [54, 270, 230, 124], [227, 225, 165, 210], [109, 88, 151, 219], [121, 152, 88, 258]], ![[0, 1], [3, 109, 36, 142], [115, 99, 272, 127], [230, 258, 158, 27], [109, 238, 121, 187], [160, 139, 137, 218], [78, 163, 25, 148], [92, 249, 157, 222], [4, 11, 149, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [63, 168, 236], []]
 b := ![[], [], [105, 146, 112, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 4
  hpos := by decide
  P := [5, 268, 63, 125, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13735160368, -26870163833, 27570956618, 28031057542, 42302930487]
  a := ![13, 7, -15, 5, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16390428601, -12619893371, -32429434069, -20057602046, 42302930487]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 5887339441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -26, -8, 4, 2]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![25, -26, -8, 4, 2]] 
 ![![277, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![108, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![130, 0, 0, 0, 1]] where
  M :=![![![25, -26, -8, 4, 2], ![-12, 35, -14, -8, 8], ![-48, 34, 41, -2, -16], ![12, -22, 6, 5, -4], ![24, 6, -42, -6, 19]]]
  hmulB := by decide  
  f := ![![![37, 18, 40, 56, 34]], ![![1, 1, 2, 4, 2]], ![![12, 6, 17, 26, 16]], ![![-2, 2, 6, 17, 8]], ![![10, 6, 22, 38, 23]]]
  g := ![![![3, -26, -8, 4, 2], ![1, 35, -14, -8, 8], ![-10, 34, 41, -2, -16], ![0, -22, 6, 5, -4], ![8, 6, -42, -6, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![37, 18, 40, 56, 34]] ![![25, -26, -8, 4, 2]]
  ![![277, 0, 0, 0, 0]] where
 M := ![![![277, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC277 : ContainsPrimesAboveP 277 ![I277N0, I277N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
    exact isPrimeI277N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 277 (by decide) (𝕀 ⊙ MulI277N0)
instance hp281 : Fact (Nat.Prime 281) := {out := by norm_num}

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8179, 6064, 6297, -443, -2424]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![-8179, 6064, 6297, -443, -2424]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![0, 0, 0, 281, 0], ![80, 221, 68, 151, 1]] where
  M :=![![![-8179, 6064, 6297, -443, -2424], ![14544, -21305, -676, 3904, -886], ![5316, 8658, -16725, -3440, 7808], ![-8996, 12086, 1514, -2101, 14], ![9070, -25208, 11503, 5985, -6455]]]
  hmulB := by decide  
  f := ![![![-79, -28, -3, 55, 30]], ![![-180, -41, 30, 226, 110]], ![![-660, -106, 155, 976, 452]], ![![-1184, -194, 300, 1785, 838]], ![![-966, -171, 223, 1398, 659]]]
  g := ![![![661, 1928, 609, 1301, -2424], ![304, 621, 212, 490, -886], ![-2204, -6110, -1949, -4208, 7808], ![-36, 32, 2, -15, 14], ![1870, 4987, 1603, 3490, -6455]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 4 2 8 [159, 43, 83, 48, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [105, 56, 116, 91], [270, 213, 18, 103], [139, 11, 147, 87], [0, 1]]
 g := ![![[169, 174, 46, 128], [99, 21, 245], [79, 217, 162], [43, 162, 226, 263], [37, 214, 154, 32], [209, 222, 56], [1], []], ![[195, 119, 235, 262, 88, 110], [17, 215, 156], [217, 138, 165], [89, 190, 73, 22, 230, 148], [12, 34, 238, 195, 173, 262], [206, 245, 81], [26, 210, 126], [43, 164, 132]], ![[134, 220, 83, 87, 167, 65], [54, 253, 248], [169, 236, 144], [216, 215, 194, 264, 158, 65], [124, 49, 226, 77, 46, 93], [180, 134, 162], [161, 220, 20], [151, 276, 212]], ![[132, 151, 64, 182, 86, 258], [151, 280, 232], [173, 204, 56], [270, 42, 75, 129, 62, 99], [2, 267, 202, 167, 271, 240], [67, 142, 49], [226, 40, 183], [69, 28, 263]]]
 h' := ![![[105, 56, 116, 91], [198, 193, 248, 68], [22, 94, 163, 37], [188, 255, 10, 217], [18, 50, 191, 194], [199, 18, 33, 247], [122, 238, 198, 233], [0, 0, 1], [0, 1]], ![[270, 213, 18, 103], [251, 182, 78, 160], [269, 247, 230, 76], [107, 58, 15, 100], [246, 37, 245, 101], [88, 226, 33, 147], [248, 179, 67, 272], [254, 133, 102, 72], [105, 56, 116, 91]], ![[139, 11, 147, 87], [263, 155, 15, 110], [177, 227, 145, 258], [230, 38, 251, 12], [53, 190, 252, 171], [122, 219, 134, 131], [262, 169, 154, 64], [278, 13, 71, 131], [270, 213, 18, 103]], ![[0, 1], [236, 32, 221, 224], [172, 275, 24, 191], [215, 211, 5, 233], [153, 4, 155, 96], [23, 99, 81, 37], [252, 257, 143, 274], [201, 135, 107, 78], [139, 11, 147, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [189, 163, 29], []]
 b := ![[], [], [24, 211, 253, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 4
  hpos := by decide
  P := [159, 43, 83, 48, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-80880412, -22073397, 30661076, 127374575, 70794091]
  a := ![-1, 1, -2, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20442732, -55756468, -17022552, -37589086, 70794091]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 6234839521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 28, 3, -55, -30]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![79, 28, 3, -55, -30]] 
 ![![281, 0, 0, 0, 0], ![260, 1, 0, 0, 0], ![121, 0, 1, 0, 0], ![131, 0, 0, 1, 0], ![115, 0, 0, 0, 1]] where
  M :=![![![79, 28, 3, -55, -30], ![180, 41, -30, -226, -110], ![660, 106, -155, -976, -452], ![1184, 194, -300, -1785, -838], ![1682, 248, -433, -2589, -1195]]]
  hmulB := by decide  
  f := ![![![8179, -6064, -6297, 443, 2424]], ![![7516, -5535, -5824, 396, 2246]], ![![3503, -2642, -2652, 203, 1016]], ![![3845, -2870, -2941, 214, 1130]], ![![3315, -2392, -2618, 160, 1015]]]
  g := ![![![11, 28, 3, -55, -30], ![126, 41, -30, -226, -110], ![611, 106, -155, -976, -452], ![1129, 194, -300, -1785, -838], ![1659, 248, -433, -2589, -1195]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N1 : Nat.card (O ⧸ I281N1) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N1)

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := prime_ideal_of_norm_prime hp281.out _ NI281N1
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![-8179, 6064, 6297, -443, -2424]] ![![79, 28, 3, -55, -30]]
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

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46183, -31691, -38158, 1755, 14960]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![46183, -31691, -38158, 1755, 14960]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![0, 0, 0, 283, 0], ![151, 145, 231, 238, 1]] where
  M :=![![![46183, -31691, -38158, 1755, 14960], ![-89760, 127466, 8222, -22959, 3510], ![-21060, -64493, 96285, 22767, -45918], ![54896, -71631, -11168, 11974, 1042], ![-64924, 160403, -62692, -36489, 36167]]]
  hmulB := by decide  
  f := ![![![-3331, -1581, -676, 729, 652]], ![![-3912, -1428, -176, 2613, 1458]], ![![-8748, -1975, 1361, 10833, 5226]], ![![-14672, -2889, 2894, 19906, 9450]], ![![-23327, -5627, 3111, 27412, 13355]]]
  g := ![![![-7819, -7777, -12346, -12575, 14960], ![-2190, -1348, -2836, -3033, 3510], ![24426, 23299, 37821, 38697, -45918], ![-362, -787, -890, -834, 1042], ![-19527, -17964, -29743, -30545, 36167]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 4 2 8 [53, 221, 125, 148, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [164, 64, 180, 93], [207, 94, 119, 79], [47, 124, 267, 111], [0, 1]]
 g := ![![[77, 16, 235, 89], [123, 273, 158, 9], [262, 278, 85], [45, 90, 102, 130], [113, 58, 206, 15], [212, 183, 113], [1], []], ![[125, 30, 214, 133, 255, 78], [42, 33, 187, 0, 90, 29], [121, 97, 176], [126, 132, 156, 184, 126, 150], [13, 235, 271, 68, 78, 196], [228, 46, 62], [248, 259, 129], [236, 43, 159]], ![[95, 168, 61, 194, 244, 191], [183, 192, 45, 89, 252, 21], [268, 107, 52], [164, 183, 211, 233, 226, 222], [242, 106, 158, 26, 162, 114], [226, 169, 78], [171, 79, 127], [10, 168, 15]], ![[262, 49, 282, 3, 144, 227], [48, 99, 41, 263, 80, 121], [278, 103, 92], [240, 29, 64, 96, 1, 62], [141, 229, 276, 7, 132, 111], [85, 21, 59], [11, 211, 163], [89, 271, 152]]]
 h' := ![![[164, 64, 180, 93], [273, 12, 165, 213], [189, 11, 129, 280], [162, 136, 61, 59], [237, 260, 278, 160], [63, 269, 196, 204], [230, 62, 158, 135], [0, 0, 1], [0, 1]], ![[207, 94, 119, 79], [190, 267, 3, 145], [162, 271, 167, 7], [241, 99, 67, 193], [12, 197, 18, 245], [17, 32, 250, 226], [201, 116, 194, 104], [238, 234, 141, 176], [164, 64, 180, 93]], ![[47, 124, 267, 111], [247, 261, 31, 17], [273, 139, 44, 232], [238, 271, 282, 202], [249, 181, 191, 168], [186, 73, 6, 137], [174, 202, 271, 19], [152, 68, 251, 134], [207, 94, 119, 79]], ![[0, 1], [270, 26, 84, 191], [68, 145, 226, 47], [54, 60, 156, 112], [7, 211, 79, 276], [20, 192, 114, 282], [89, 186, 226, 25], [39, 264, 173, 256], [47, 124, 267, 111]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [97, 87, 214], []]
 b := ![[], [], [157, 196, 83, 137], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 4
  hpos := by decide
  P := [53, 221, 125, 148, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-635731438, -208726693, 275151270, 1010882698, 602597669]
  a := ![3, -3, 4, 2, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-323773779, -309489006, -490900743, -503206228, 602597669]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 6414247921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3331, -1581, -676, 729, 652]] i)))

def SI283N1: IdealEqSpanCertificate' Table ![![-3331, -1581, -676, 729, 652]] 
 ![![283, 0, 0, 0, 0], ![90, 1, 0, 0, 0], ![107, 0, 1, 0, 0], ![63, 0, 0, 1, 0], ![238, 0, 0, 0, 1]] where
  M :=![![![-3331, -1581, -676, 729, 652], ![-3912, -1428, -176, 2613, 1458], ![-8748, -1975, 1361, 10833, 5226], ![-14672, -2889, 2894, 19906, 9450], ![-18596, -2843, 4846, 28581, 13297]]]
  hmulB := by decide  
  f := ![![![46183, -31691, -38158, 1755, 14960]], ![![14370, -9628, -12106, 477, 4770]], ![![17387, -12210, -14087, 744, 5494]], ![![10475, -7308, -8534, 433, 3334]], ![![38610, -26085, -32312, 1347, 12709]]]
  g := ![![![36, -1581, -676, 729, 652], ![-1301, -1428, -176, 2613, 1458], ![-6724, -1975, 1361, 10833, 5226], ![-12606, -2889, 2894, 19906, 9450], ![-18539, -2843, 4846, 28581, 13297]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N1 : Nat.card (O ⧸ I283N1) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N1)

lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := prime_ideal_of_norm_prime hp283.out _ NI283N1
def MulI283N0 : IdealMulLeCertificate' Table 
  ![![46183, -31691, -38158, 1755, 14960]] ![![-3331, -1581, -676, 729, 652]]
  ![![283, 0, 0, 0, 0]] where
 M := ![![![283, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC283 : ContainsPrimesAboveP 283 ![I283N0, I283N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI283N0
    exact isPrimeI283N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 283 (by decide) (𝕀 ⊙ MulI283N0)
instance hp293 : Fact (Nat.Prime 293) := {out := by norm_num}

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![293, 0, 0, 0, 0]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![293, 0, 0, 0, 0]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![0, 0, 0, 293, 0], ![0, 0, 0, 0, 293]] where
  M :=![![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![0, 0, 0, 293, 0], ![0, 0, 0, 0, 293]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 5 2 8 [48, 98, 8, 83, 106, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [193, 205, 62, 197, 265], [202, 41, 67, 282, 266], [19, 32, 97, 226, 163], [66, 14, 67, 174, 185], [0, 1]]
 g := ![![[173, 69, 93, 104, 67], [154, 126, 291, 36], [2, 256, 241, 197, 71], [97, 143, 97, 228], [151, 114, 60, 184], [232, 37, 19, 187, 1], [], []], ![[144, 122, 140, 68, 239, 242, 217, 187], [257, 71, 137, 95], [205, 160, 73, 126, 276, 207, 185, 275], [99, 124, 5, 135], [157, 251, 56, 65], [123, 192, 286, 89, 257, 96, 284, 243], [216, 6, 180, 254], [227, 159, 210, 198]], ![[219, 140, 18, 80, 35, 23, 187, 105], [191, 260, 291, 167], [152, 151, 207, 135, 202, 241, 62, 34], [96, 249, 64, 39], [6, 286, 141, 191], [128, 271, 204, 248, 68, 39, 107, 51], [226, 42, 60, 193], [34, 130, 86, 143]], ![[118, 32, 172, 238, 41, 121, 111, 86], [173, 36, 50, 289], [15, 162, 196, 179, 216, 127, 110, 180], [199, 128, 216, 278], [152, 202, 60, 15], [23, 34, 210, 224, 60, 161, 106, 105], [162, 189, 123, 100], [278, 10, 135, 199]], ![[143, 50, 273, 88, 129, 131, 71, 242], [256, 110, 30, 199], [149, 101, 148, 203, 181, 270, 91, 241], [41, 107, 202, 253], [157, 164, 63, 35], [185, 95, 272, 286, 14, 101, 60, 23], [281, 265, 119, 137], [149, 73, 289, 237]]]
 h' := ![![[193, 205, 62, 197, 265], [66, 96, 5, 120, 52], [197, 42, 148, 24, 287], [147, 195, 217, 142, 86], [81, 133, 99, 81, 195], [291, 100, 52, 82, 105], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[202, 41, 67, 282, 266], [41, 12, 284, 255, 122], [86, 13, 185, 202, 55], [235, 24, 31, 114, 90], [42, 82, 11, 169, 253], [245, 43, 259, 222, 46], [176, 153, 42, 100, 143], [276, 28, 96, 283, 227], [193, 205, 62, 197, 265]], ![[19, 32, 97, 226, 163], [10, 112, 44, 213, 78], [238, 35, 131, 119, 131], [94, 97, 270, 192, 35], [166, 152, 41, 127, 268], [109, 104, 101, 177, 22], [182, 30, 177, 107, 144], [203, 253, 182, 62, 208], [202, 41, 67, 282, 266]], ![[66, 14, 67, 174, 185], [84, 235, 270, 271, 67], [188, 62, 158, 11, 276], [219, 39, 266, 101, 215], [106, 164, 142, 112, 211], [202, 128, 61, 48, 182], [212, 168, 252, 225, 196], [202, 155, 7, 211, 283], [19, 32, 97, 226, 163]], ![[0, 1], [179, 131, 276, 20, 267], [184, 141, 257, 230, 130], [286, 231, 95, 37, 160], [72, 55, 0, 97, 245], [24, 211, 113, 57, 231], [73, 235, 115, 154, 102], [134, 150, 7, 30, 161], [66, 14, 67, 174, 185]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [227, 272, 62, 152], [], [], []]
 b := ![[], [65, 93, 105, 275, 131], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 5
  hpos := by decide
  P := [48, 98, 8, 83, 106, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5181690828176, -12539810484000, 12722785792644, 11242535304380, 19103741842472]
  a := ![1, -5, 12, -5, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17684951632, -42797988000, 43422477108, 38370427660, 65200484104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 2159424884693 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def PBC293 : ContainsPrimesAboveP 293 ![I293N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI293N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![293, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 293 (by decide) 𝕀

instance hp307 : Fact (Nat.Prime 307) := {out := by norm_num}

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-775, 594, 535, 1, -238]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![-775, 594, 535, 1, -238]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![0, 0, 0, 307, 0], ![100, 62, 30, 89, 1]] where
  M :=![![![-775, 594, 535, 1, -238], ![1428, -2025, 60, 178, 2], ![-12, 1196, -1907, 370, 356], ![-240, 588, 542, -889, 366], ![-258, -1302, 291, 1815, -1249]]]
  hmulB := by decide  
  f := ![![![71, 30, 9, -31, -20]], ![![120, 33, -10, -124, -62]], ![![372, 68, -81, -526, -248]], ![![660, 112, -156, -969, -454]], ![![278, 56, -53, -372, -177]]]
  g := ![![![75, 50, 25, 69, -238], ![4, -7, 0, 0, 2], ![-116, -68, -41, -102, 356], ![-120, -72, -34, -109, 366], ![406, 248, 123, 368, -1249]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 4 2 8 [137, 20, 123, 70, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [279, 55, 191, 294], [269, 127, 206, 216], [303, 124, 217, 104], [0, 1]]
 g := ![![[296, 182, 281, 134], [10, 206, 181, 287], [2, 281, 68], [144, 27, 171], [202, 276, 163, 17], [306, 90, 254, 295], [1], []], ![[186, 239, 103, 306, 166, 40], [239, 85, 41, 3, 285, 63], [87, 80, 183], [58, 254, 233], [182, 261, 56, 197, 258, 114], [26, 279, 276, 175, 198, 287], [190, 287, 201], [52, 89, 169]], ![[164, 5, 59, 116, 4, 26], [98, 241, 176, 214, 141, 104], [192, 275, 240], [164, 49, 250], [63, 164, 265, 226, 218, 10], [190, 89, 229, 219, 134, 295], [293, 169, 170], [37, 215, 299]], ![[227, 32, 236, 60, 127, 112], [252, 207, 35, 192, 144, 181], [104, 86, 169], [161, 146, 287], [25, 1, 98, 58, 79, 302], [224, 106, 99, 150, 296, 304], [102, 153, 104], [178, 256, 71]]]
 h' := ![![[279, 55, 191, 294], [165, 73, 135, 21], [229, 290, 85, 168], [14, 60, 11, 271], [263, 249, 18, 103], [137, 12, 12, 18], [170, 287, 184, 237], [0, 0, 1], [0, 1]], ![[269, 127, 206, 216], [10, 246, 31, 27], [224, 265, 168, 56], [28, 237, 232, 262], [91, 42, 283, 141], [59, 75, 192, 78], [155, 83, 172, 77], [107, 265, 296, 87], [279, 55, 191, 294]], ![[303, 124, 217, 104], [119, 287, 99, 126], [220, 206, 176, 55], [212, 270, 50, 94], [283, 74, 238, 231], [242, 8, 1, 246], [180, 218, 221, 289], [59, 63, 86, 279], [269, 127, 206, 216]], ![[0, 1], [99, 8, 42, 133], [18, 160, 185, 28], [12, 47, 14, 294], [72, 249, 75, 139], [225, 212, 102, 272], [22, 26, 37, 11], [190, 286, 231, 248], [303, 124, 217, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [199, 144, 135], []]
 b := ![[], [], [265, 113, 61, 268], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 4
  hpos := by decide
  P := [137, 20, 123, 70, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17847, 29772, -31050, 34062, -33270]
  a := ![4, 0, -1, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10779, 6816, 3150, 9756, -33270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 8882874001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 30, 9, -31, -20]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![71, 30, 9, -31, -20]] 
 ![![307, 0, 0, 0, 0], ![129, 1, 0, 0, 0], ![244, 0, 1, 0, 0], ![275, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![71, 30, 9, -31, -20], ![120, 33, -10, -124, -62], ![372, 68, -81, -526, -248], ![660, 112, -156, -969, -454], ![906, 138, -237, -1395, -649]]]
  hmulB := by decide  
  f := ![![![-775, 594, 535, 1, -238]], ![![-321, 243, 225, 1, -100]], ![![-616, 476, 419, 2, -188]], ![![-695, 534, 481, -2, -212]], ![![-69, 48, 48, 6, -25]]]
  g := ![![![10, 30, 9, -31, -20], ![111, 33, -10, -124, -62], ![530, 68, -81, -526, -248], ![987, 112, -156, -969, -454], ![1440, 138, -237, -1395, -649]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N1 : Nat.card (O ⧸ I307N1) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N1)

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := prime_ideal_of_norm_prime hp307.out _ NI307N1
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![-775, 594, 535, 1, -238]] ![![71, 30, 9, -31, -20]]
  ![![307, 0, 0, 0, 0]] where
 M := ![![![307, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC307 : ContainsPrimesAboveP 307 ![I307N0, I307N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI307N0
    exact isPrimeI307N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 307 (by decide) (𝕀 ⊙ MulI307N0)


lemma PB1705I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB1705I6 : PrimesBelowBoundCertificateInterval O 251 307 1705 where
  m := 9
  g := ![3, 1, 2, 3, 2, 2, 2, 1, 2]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB1705I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1, I257N2]
    · exact ![I263N0]
    · exact ![I269N0, I269N1]
    · exact ![I271N0, I271N1, I271N2]
    · exact ![I277N0, I277N1]
    · exact ![I281N0, I281N1]
    · exact ![I283N0, I283N1]
    · exact ![I293N0]
    · exact ![I307N0, I307N1]
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
    · exact ![16974593, 257, 257]
    · exact ![1258284197543]
    · exact ![19465109, 72361]
    · exact ![73441, 73441, 271]
    · exact ![5887339441, 277]
    · exact ![6234839521, 281]
    · exact ![6414247921, 283]
    · exact ![2159424884693]
    · exact ![8882874001, 307]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
      exact NI257N2
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
      exact NI281N1
    · dsimp ; intro j
      fin_cases j
      exact NI283N0
      exact NI283N1
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
  β := ![I257N1, I257N2, I271N2, I277N1, I281N1, I283N1, I307N1]
  Il := ![[I257N1, I257N2], [], [], [I271N2], [I277N1], [I281N1], [I283N1], [], [I307N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
