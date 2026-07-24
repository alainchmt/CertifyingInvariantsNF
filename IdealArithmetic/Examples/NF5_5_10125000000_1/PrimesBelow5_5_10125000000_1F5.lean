
import IdealArithmetic.Examples.NF5_5_10125000000_1.RI5_5_10125000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0, 0, 0]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![0, 0, 0, 199, 0], ![0, 0, 0, 0, 199]] where
  M :=![![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![0, 0, 0, 199, 0], ![0, 0, 0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 5 2 7 [147, 183, 165, 29, 177, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [121, 83, 100, 152, 66], [82, 83, 27, 141, 36], [172, 26, 68, 79, 54], [45, 6, 4, 26, 43], [0, 1]]
 g := ![![[98, 132, 56, 59, 114], [65, 171, 126, 31, 180], [111, 97, 45, 147, 63], [22, 167, 89, 18], [109, 62, 35, 65], [22, 1], []], ![[107, 22, 104, 173, 133, 189, 158, 66], [129, 82, 49, 180, 42, 195, 171, 123], [122, 3, 71, 134, 140, 167, 19, 9], [65, 6, 63, 58], [172, 129, 100, 196], [189, 16, 121, 53], [17, 95, 47, 99, 184, 153, 13, 140]], ![[13, 162, 156, 44, 145, 166, 66, 115], [79, 81, 66, 52, 119, 36, 192, 80], [72, 36, 75, 74, 148, 155, 145, 43], [56, 113, 72, 124], [70, 22, 95, 161], [147, 180, 144, 117], [123, 29, 11, 85, 58, 178, 152, 90]], ![[119, 121, 170, 50, 166, 46, 52, 96], [110, 40, 130, 197, 31, 175, 116, 152], [129, 163, 73, 8, 25, 165, 87, 167], [49, 144, 14, 7], [124, 121, 133, 7], [168, 109, 53, 122], [198, 179, 53, 145, 175, 152, 180, 55]], ![[190, 13, 28, 71, 148, 125, 148, 91], [176, 186, 187, 18, 116, 8, 143, 160], [57, 51, 70, 164, 85, 152, 53, 162], [150, 66, 14, 33], [113, 104, 48, 100], [95, 132, 197, 61], [50, 56, 19, 79, 8, 42, 90, 106]]]
 h' := ![![[121, 83, 100, 152, 66], [196, 182, 195, 68, 121], [1, 20, 135, 15, 141], [31, 100, 43, 120, 62], [9, 189, 3, 19, 60], [149, 6, 167, 192, 57], [0, 0, 0, 1], [0, 1]], ![[82, 83, 27, 141, 36], [107, 90, 153, 179, 1], [160, 86, 127, 57, 167], [48, 40, 123, 137, 42], [38, 77, 112, 53, 43], [192, 59, 168, 122, 185], [151, 166, 10, 66, 75], [121, 83, 100, 152, 66]], ![[172, 26, 68, 79, 54], [63, 145, 36, 168, 8], [41, 28, 184, 127, 82], [27, 111, 172, 135, 96], [189, 144, 8, 72, 70], [176, 98, 12, 81, 34], [166, 182, 35, 142, 147], [82, 83, 27, 141, 36]], ![[45, 6, 4, 26, 43], [43, 40, 185, 81, 65], [184, 192, 75, 81, 107], [100, 85, 153, 55, 161], [61, 127, 85, 74, 112], [141, 120, 152, 31, 112], [165, 86, 46, 26, 91], [172, 26, 68, 79, 54]], ![[0, 1], [182, 140, 28, 101, 4], [71, 72, 76, 118, 100], [86, 62, 106, 150, 37], [68, 60, 190, 180, 113], [180, 115, 98, 171, 10], [195, 163, 108, 163, 85], [45, 6, 4, 26, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101, 96, 192, 137], [], [], []]
 b := ![[], [124, 163, 108, 49, 13], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 5
  hpos := by decide
  P := [147, 183, 165, 29, 177, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![53702882726387031432, -73264590102534852579, -89887022938070948997, -53490042755891743017, -21458075324698283010]
  a := ![-25, -17, 5, -1, -50]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![269863732293402168, -368163769359471621, -451693582603371603, -268794184702973583, -107829524244714990]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 312079600999 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def PBC199 : ContainsPrimesAboveP 199 ![I199N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![199, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 199 (by decide) 𝕀

instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1107, 750, 638, -74, -146]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-1107, 750, 638, -74, -146]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![15, 204, 129, 1, 0], ![39, 62, 95, 0, 1]] where
  M :=![![![-1107, 750, 638, -74, -146], ![4232, -3953, -4192, -1424, -296], ![900, -4272, -6353, -5580, -2700], ![32804, -42036, -50596, -28501, -11012], ![77544, -107814, -133032, -80358, -32531]]]
  hmulB := by decide  
  f := ![![![42335, -31050, -34214, -2794, 3878]], ![![-121928, 89533, 98608, 8048, -11176]], ![![236652, -173712, -191339, -15612, 21684]], ![![28483, -20874, -23003, -1875, 2606]], ![![79631, -58438, -64373, -5252, 7295]]]
  g := ![![![27, 118, 114, -74, -146], ![176, 1445, 984, -1424, -296], ![900, 6168, 4597, -5580, -2700], ![4217, 30592, 22143, -28501, -11012], ![12093, 86740, 63145, -80358, -32531]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [75, 110, 112, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 189, 69], [52, 21, 142], [0, 1]]
 g := ![![[5, 185, 24], [38, 164, 78], [82, 201], [174, 96], [102, 84, 101], [74, 95], [1]], ![[178, 91, 111, 4], [66, 127, 190, 14], [45, 62], [157, 117], [50, 36, 177, 52], [190, 203], [88, 121, 70, 193]], ![[48, 177, 63, 39], [86, 150, 70, 147], [155, 172], [27, 16], [78, 120, 186, 85], [189, 201], [6, 129, 206, 18]]]
 h' := ![![[47, 189, 69], [104, 3, 92], [5, 123, 194], [205, 127, 74], [157, 132, 27], [75, 180, 34], [136, 101, 99], [0, 1]], ![[52, 21, 142], [83, 20, 29], [96, 200, 112], [99, 9, 189], [144, 89, 180], [81, 145, 52], [163, 31, 186], [47, 189, 69]], ![[0, 1], [105, 188, 90], [79, 99, 116], [47, 75, 159], [157, 201, 4], [135, 97, 125], [54, 79, 137], [52, 21, 142]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97, 1], []]
 b := ![[], [155, 157, 159], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [75, 110, 112, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![194801239974, -275364111422, -335693263452, -205341404049, -86832153279]
  a := ![-37, -48, -6, -1, -77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![31570503690, 222738747952, 163044561234, -205341404049, -86832153279]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, -220, -230, -18, 26]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![269, -220, -230, -18, 26]] 
 ![![211, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![122, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![269, -220, -230, -18, 26], ![-816, 573, 636, 52, -72], ![1540, -1134, -1237, -100, 140], ![-1792, 1328, 1448, 117, -164], ![1476, -1068, -1176, -96, 133]]]
  hmulB := by decide  
  f := ![![![-481, 352, 526, 142, -94]], ![![-40, 29, 44, 12, -8]], ![![-330, 242, 359, 96, -64]], ![![149, -112, -158, -41, 26]], ![![-213, 156, 222, 54, -41]]]
  g := ![![![159, -220, -230, -18, 26], ![-436, 573, 636, 52, -72], ![850, -1134, -1237, -100, 140], ![-995, 1328, 1448, 117, -164], ![807, -1068, -1176, -96, 133]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, 101, 126, 75, 30]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![-79, 101, 126, 75, 30]] 
 ![![211, 0, 0, 0, 0], ![141, 1, 0, 0, 0], ![117, 0, 1, 0, 0], ![121, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![-79, 101, 126, 75, 30], ![-750, 1018, 1252, 747, 300], ![-3378, 4601, 5645, 3355, 1344], ![-16430, 22413, 27500, 16362, 6560], ![-46776, 63784, 78260, 46550, 18659]]]
  hmulB := by decide  
  f := ![![![45883, -34259, -31514, -2011, 3454]], ![![30151, -22513, -20710, -1322, 2270]], ![![26291, -19630, -18053, -1150, 1978]], ![![25591, -19108, -17590, -1129, 1930]], ![![10096, -7538, -6916, -432, 755]]]
  g := ![![![-187, 101, 126, 75, 30], ![-1869, 1018, 1252, 747, 300], ![-8425, 4601, 5645, 3355, 1344], ![-41055, 22413, 27500, 16362, 6560], ![-116826, 63784, 78260, 46550, 18659]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-1107, 750, 638, -74, -146]] ![![269, -220, -230, -18, 26]]
  ![![-10151, 7454, 6948, 484, -744]] where
 M := ![![![-10151, 7454, 6948, 484, -744]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![-10151, 7454, 6948, 484, -744]] ![![-79, 101, 126, 75, 30]]
  ![![211, 0, 0, 0, 0]] where
 M := ![![![-1409691, 1923265, 2359402, 1403361, 562526]]]
 hmul := by decide  
 g := ![![![![-6681, 9115, 11182, 6651, 2666]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![105525, 106359, 38430, -1307, -4187]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![105525, 106359, 38430, -1307, -4187]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![0, 0, 223, 0, 0], ![0, 0, 0, 223, 0], ![215, 196, 55, 14, 1]] where
  M :=![![![105525, 106359, 38430, -1307, -4187], ![122996, 128891, 47852, -1386, -5228], ![15536, 9618, 1791, -428, -158], ![-59556, -53264, -17040, 1197, 1758], ![-72470, -81406, -32230, 270, 3651]]]
  hmulB := by decide  
  f := ![![![133, -171, -208, -117, -45]], ![![1116, -1551, -1908, -1154, -468]], ![![5308, -7182, -8803, -5200, -2074]], ![![25352, -34636, -42508, -25329, -10166]], ![![4335, -5917, -7261, -4323, -1734]]]
  g := ![![![4510, 4157, 1205, 257, -4187], ![5592, 5173, 1504, 322, -5228], ![222, 182, 47, 8, -158], ![-1962, -1784, -510, -105, 1758], ![-3845, -3574, -1045, -228, 3651]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 4 2 7 [97, 45, 25, 118, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 156, 67, 178], [70, 79, 184, 207], [164, 210, 195, 61], [0, 1]]
 g := ![![[68, 125, 0, 126], [209, 88, 133, 199], [120, 33, 136, 210], [42, 54, 106, 25], [137, 73, 210, 116], [73, 105, 1], []], ![[157, 183, 61, 101, 73, 78], [24, 106, 94, 139, 81, 196], [62, 67, 185, 117, 119, 19], [168, 183, 111, 144, 117, 120], [109, 165, 15, 135, 167, 28], [6, 135, 82], [161, 154, 168, 135, 186, 82]], ![[151, 191, 110, 185, 208, 67], [141, 118, 132, 89, 132, 163], [214, 127, 79, 92, 38, 13], [161, 132, 52, 73, 27, 206], [147, 24, 108, 118, 10, 99], [128, 65, 164], [149, 83, 78, 196, 17, 141]], ![[93, 97, 160, 160, 203, 216], [219, 153, 219, 41, 153, 45], [88, 121, 170, 3, 65, 206], [153, 133, 14, 165, 153, 61], [68, 92, 59, 78, 143, 160], [167, 171, 25], [36, 167, 160, 94, 185, 190]]]
 h' := ![![[94, 156, 67, 178], [20, 51, 100, 168], [179, 128, 63, 83], [163, 38, 108, 136], [91, 37, 38, 5], [55, 133, 43, 89], [0, 0, 0, 1], [0, 1]], ![[70, 79, 184, 207], [112, 198, 209, 171], [65, 93, 19, 25], [95, 163, 99, 8], [29, 89, 13, 121], [102, 108, 106, 162], [125, 53, 169, 159], [94, 156, 67, 178]], ![[164, 210, 195, 61], [132, 101, 205, 203], [149, 148, 215, 174], [173, 4, 167, 34], [24, 117, 4, 98], [13, 110, 3, 130], [68, 101, 210, 68], [70, 79, 184, 207]], ![[0, 1], [85, 96, 155, 127], [198, 77, 149, 164], [139, 18, 72, 45], [158, 203, 168, 222], [13, 95, 71, 65], [80, 69, 67, 218], [164, 210, 195, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [153, 31, 133], []]
 b := ![[], [], [11, 165, 54, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 4
  hpos := by decide
  P := [97, 45, 25, 118, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24336888541685, 33290313737817, 40823635417499, 24344783381011, 9807144033727]
  a := ![-8, -7, 1, -1, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9564452268130, -8470448057725, -2235736710482, -506525708929, 9807144033727]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 2472973441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-133, 171, 208, 117, 45]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-133, 171, 208, 117, 45]] 
 ![![223, 0, 0, 0, 0], ![167, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![170, 0, 0, 1, 0], ![92, 0, 0, 0, 1]] where
  M :=![![![-133, 171, 208, 117, 45], ![-1116, 1551, 1908, 1154, 468], ![-5308, 7182, 8803, 5200, 2074], ![-25352, 34636, 42508, 25329, 10166], ![-72506, 98816, 121238, 72084, 28885]]]
  hmulB := by decide  
  f := ![![![-105525, -106359, -38430, 1307, 4187]], ![![-79577, -80228, -28994, 985, 3159]], ![![-10007, -10059, -3627, 125, 395]], ![![-80178, -80842, -29220, 991, 3184]], ![![-43210, -43514, -15710, 538, 1711]]]
  g := ![![![-256, 171, 208, 117, 45], ![-2419, 1551, 1908, 1154, 468], ![-11051, 7182, 8803, 5200, 2074], ![-53558, 34636, 42508, 25329, 10166], ![-152612, 98816, 121238, 72084, 28885]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![105525, 106359, 38430, -1307, -4187]] ![![-133, 171, 208, 117, 45]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![-223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-226011, 169730, 156490, 10136, -17201]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-226011, 169730, 156490, 10136, -17201]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![69, 32, 107, 1, 0], ![15, 164, 163, 0, 1]] where
  M :=![![![-226011, 169730, 156490, 10136, -17201], ![536302, -398620, -368852, -23975, 40544], ![-900286, 671613, 620661, 40291, -68222], ![795470, -593915, -548692, -35606, 60310], ![-608398, 452926, 418858, 27204, -46039]]]
  hmulB := by decide  
  f := ![![![18821, -13816, -15220, -1244, 1725]], ![![-54238, 39810, 43856, 3579, -4976]], ![![105338, -77343, -85217, -6995, 9646]], ![![47179, -34642, -38169, -3135, 4319]], ![![38149, -28021, -30879, -2551, 3486]]]
  g := ![![![-2940, 11746, 8263, 10136, -17201], ![6971, -27668, -19437, -23975, 40544], ![-11705, 46567, 32730, 40291, -68222], ![10342, -41169, -28940, -35606, 60310], ![-7907, 31422, 22081, 27204, -46039]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [145, 138, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 60, 135], [158, 166, 92], [0, 1]]
 g := ![![[56, 217, 19], [196, 47, 100], [139, 122], [39, 64], [11, 64], [107, 6, 62], [1]], ![[46, 133, 220, 98], [16, 184, 181, 106], [28, 10], [110, 144], [197, 192], [148, 119, 192, 204], [80, 109, 87, 149]], ![[120, 45, 112, 43], [166, 86, 192, 74], [132, 26], [16, 173], [31, 73], [25, 37, 218, 27], [213, 145, 172, 78]]]
 h' := ![![[52, 60, 135], [182, 13, 143], [31, 76, 10], [133, 214, 203], [106, 113, 8], [148, 168, 8], [82, 89, 210], [0, 1]], ![[158, 166, 92], [80, 112, 69], [195, 186, 116], [13, 2, 163], [46, 12, 12], [224, 134, 173], [72, 200, 113], [52, 60, 135]], ![[0, 1], [106, 102, 15], [67, 192, 101], [162, 11, 88], [165, 102, 207], [44, 152, 46], [174, 165, 131], [158, 166, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 114], []]
 b := ![[], [225, 147, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [145, 138, 17, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-433916728045, 615073569672, 749451603070, 459392297108, 195018463812]
  a := ![52, 39, -8, -1, 103]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-154437278351, -202944969176, -353275479246, 459392297108, 195018463812]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18821, -13816, -15220, -1244, 1725]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![18821, -13816, -15220, -1244, 1725]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![218, 121, 1, 0, 0], ![181, 57, 0, 1, 0], ![14, 34, 0, 0, 1]] where
  M :=![![![18821, -13816, -15220, -1244, 1725], ![-54238, 39810, 43856, 3579, -4976], ![105338, -77343, -85217, -6995, 9646], ![-124566, 91351, 100644, 8128, -11502], ![102446, -75458, -83246, -7188, 9213]]]
  hmulB := by decide  
  f := ![![![-226011, 169730, 156490, 10136, -17201]], ![![536302, -398620, -368852, -23975, 40544]], ![![64854, -46521, -43593, -2868, 4792]], ![![-42041, 32625, 29742, 1905, -3269]], ![![63708, -47242, -43750, -2846, 4809]]]
  g := ![![![15585, 8106, -15220, -1244, 1725], ![-44903, -23355, 43856, 3579, -4976], ![87285, 45395, -85217, -6995, 9646], ![-102974, -53563, 100644, 8128, -11502], ![85560, 44466, -83246, -7188, 9213]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P1 : CertificateIrreducibleZModOfList' 227 2 2 7 [5, 225, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 226], [0, 1]]
 g := ![![[45, 34], [165, 43], [212], [69], [26], [22, 1], [2, 1]], ![[113, 193], [24, 184], [212], [69], [26], [24, 226], [4, 226]]]
 h' := ![![[2, 226], [83, 179], [8, 161], [198, 165], [166, 117], [117, 139], [217, 226], [0, 1]], ![[0, 1], [214, 48], [103, 66], [74, 62], [173, 110], [168, 88], [215, 1], [2, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [85, 142]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N1 : CertifiedPrimeIdeal' SI227N1 227 where
  n := 2
  hpos := by decide
  P := [5, 225, 1]
  hirr := P227P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1257463, 2919638, 3291100, 2656370, 1639441]
  a := ![-35, -20, 10, 2, -69]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5385341, -2653998, 3291100, 2656370, 1639441]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N1 B_one_repr
lemma NI227N1 : Nat.card (O ⧸ I227N1) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-226011, 169730, 156490, 10136, -17201]] ![![18821, -13816, -15220, -1244, 1725]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-627, 525, 596, 137, -7]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-627, 525, 596, 137, -7]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![82, 190, 1, 0, 0], ![221, 104, 0, 1, 0], ![12, 112, 0, 0, 1]] where
  M :=![![![-627, 525, 596, 137, -7], ![484, 291, 496, 922, 548], ![-7540, 8436, 10081, 4780, 1570], ![-19012, 28108, 34808, 22145, 9286], ![-66782, 89282, 109286, 63834, 25255]]]
  hmulB := by decide  
  f := ![![![-5713, -9531, -4354, -3, 477]], ![![-14316, -5765, 24, 358, -12]], ![![-13890, -8228, -1567, 294, 164]], ![![-12033, -11771, -4158, 162, 451]], ![![-7246, -3316, -230, 172, 21]]]
  g := ![![![-348, -551, 596, 137, -7], ![-1094, -1097, 496, 922, 548], ![-8338, -11266, 10081, 4780, 1570], ![-34405, -43356, 34808, 22145, 9286], ![-102352, -131626, 109286, 63834, 25255]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [92, 194, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 228], [0, 1]]
 g := ![![[27, 82], [147], [84, 49], [71], [204], [109, 144], [35, 1]], ![[149, 147], [147], [196, 180], [71], [204], [111, 85], [70, 228]]]
 h' := ![![[35, 228], [145, 51], [58, 39], [227, 7], [24, 206], [48, 152], [215, 217], [0, 1]], ![[0, 1], [98, 178], [49, 190], [14, 222], [135, 23], [101, 77], [24, 12], [35, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [209, 132]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [92, 194, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![102196, -13188, -48912, 40140, 81808]
  a := ![8, -2, -6, -10, 16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-25064, -17716, -48912, 40140, 81808]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![279, -409, -364, -25, 41]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![279, -409, -364, -25, 41]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![76, 193, 1, 0, 0], ![217, 213, 0, 1, 0], ![71, 141, 0, 0, 1]] where
  M :=![![![279, -409, -364, -25, 41], ![-1280, 695, 872, 76, -100], ![2216, -1654, -1817, -154, 202], ![-2544, 1954, 2104, 141, -258], ![2338, -1626, -1874, -238, 157]]]
  hmulB := by decide  
  f := ![![![3645, -2717, -3910, -1017, 677]], ![![-22344, 16651, 23680, 6060, -4068]], ![![-17280, 12877, 18299, 4678, -3142]], ![![-18299, 13636, 19342, 4932, -3317]], ![![-11267, 8396, 11936, 3053, -2050]]]
  g := ![![![133, 303, -364, -25, 41], ![-336, -741, 872, 76, -100], ![696, 1543, -1817, -154, 202], ![-763, -1737, 2104, 141, -258], ![809, 1697, -1874, -238, 157]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P1 : CertificateIrreducibleZModOfList' 229 2 2 7 [103, 161, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 228], [0, 1]]
 g := ![![[215, 209], [224], [50, 11], [203], [226], [162, 46], [68, 1]], ![[0, 20], [224], [111, 218], [203], [226], [84, 183], [136, 228]]]
 h' := ![![[68, 228], [6, 74], [117, 37], [212, 34], [125, 64], [31, 189], [95, 170], [0, 1]], ![[0, 1], [0, 155], [114, 192], [5, 195], [126, 165], [59, 40], [205, 59], [68, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117]]
 b := ![[], [72, 173]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N1 : CertifiedPrimeIdeal' SI229N1 229 where
  n := 2
  hpos := by decide
  P := [103, 161, 1]
  hirr := P229P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1380295, 2996505, 3401462, 2655409, 1607719]
  a := ![40, 24, -6, 1, 67]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4149621, -6313433, 3401462, 2655409, 1607719]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N1 B_one_repr
lemma NI229N1 : Nat.card (O ⧸ I229N1) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-123, -71, -10, 3, 1]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![-123, -71, -10, 3, 1]] 
 ![![229, 0, 0, 0, 0], ![152, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![170, 0, 0, 1, 0], ![135, 0, 0, 0, 1]] where
  M :=![![![-123, -71, -10, 3, 1], ![-24, -175, -108, -4, 12], ![-172, 108, 123, 10, -14], ![232, -86, -128, -13, 14], ![-78, 174, 138, 6, -17]]]
  hmulB := by decide  
  f := ![![![-1361, 1013, 1344, 307, -219]], ![![-872, 649, 860, 196, -140]], ![![-407, 303, 407, 95, -67]], ![![-726, 540, 700, 153, -112]], ![![-1197, 891, 1206, 285, -200]]]
  g := ![![![46, -71, -10, 3, 1], ![136, -175, -108, -4, 12], ![-99, 108, 123, 10, -14], ![88, -86, -128, -13, 14], ![-141, 174, 138, 6, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-627, 525, 596, 137, -7]] ![![279, -409, -364, -25, 41]]
  ![![108909, -85386, -95538, -15226, 5740]] where
 M := ![![![108909, -85386, -95538, -15226, 5740]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![108909, -85386, -95538, -15226, 5740]] ![![-123, -71, -10, 3, 1]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![1105841, -799897, -877528, -54731, 111065]]]
 hmul := by decide  
 g := ![![![![4829, -3493, -3832, -239, 485]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14545, -11832, -12580, -1004, 1426]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![14545, -11832, -12580, -1004, 1426]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![60, 42, 213, 1, 0], ![33, 218, 165, 0, 1]] where
  M :=![![![14545, -11832, -12580, -1004, 1426], ![-44788, 31487, 35384, 2938, -4016], ![85572, -62934, -69463, -5706, 7884], ![-101572, 75162, 82760, 6819, -9404], ![84060, -60852, -67620, -5640, 7697]]]
  hmulB := by decide  
  f := ![![![3729, -5088, -6244, -3716, -1490]], ![![37268, -50813, -62344, -37082, -14864]], ![![167244, -228066, -279839, -166470, -66732]], ![![164068, -223734, -274523, -163307, -65464]], ![![163793, -223352, -274051, -163022, -65349]]]
  g := ![![![119, -1204, -146, -1004, 1426], ![-380, 3363, 310, 2938, -4016], ![720, -6618, -665, -5706, 7884], ![-860, 7892, 781, 6819, -9404], ![723, -6446, -585, -5640, 7697]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [7, 213, 213, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [204, 61, 231], [49, 171, 2], [0, 1]]
 g := ![![[104, 9, 152], [168, 229], [192, 38], [39, 74, 36], [102, 152], [50, 179, 167], [1]], ![[126, 10, 114, 231], [], [135, 152], [40, 172, 90, 4], [231, 126], [85, 27, 87, 112], [137, 23, 106, 225]], ![[142, 165, 90, 131], [164, 229], [196, 109], [137, 58, 232, 15], [1, 121], [175, 92, 126, 109], [157, 16, 115, 8]]]
 h' := ![![[204, 61, 231], [52, 217, 102], [23, 159, 55], [193, 232, 51], [160, 15, 227], [116, 29, 102], [226, 20, 20], [0, 1]], ![[49, 171, 2], [218, 198, 232], [190, 144], [73, 60, 102], [140, 51, 109], [142, 147, 142], [49, 139, 118], [204, 61, 231]], ![[0, 1], [176, 51, 132], [208, 163, 178], [132, 174, 80], [170, 167, 130], [115, 57, 222], [50, 74, 95], [49, 171, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 9], []]
 b := ![[], [112, 94, 121], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [7, 213, 213, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-242554363, 353952327, 428980248, 268611141, 118569303]
  a := ![4, 1, -2, -1, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-87004334, -157836153, -327678660, 268611141, 118569303]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3729, 5088, 6244, 3716, 1490]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-3729, 5088, 6244, 3716, 1490]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![1, 21, 1, 0, 0], ![212, 153, 0, 1, 0], ![94, 48, 0, 0, 1]] where
  M :=![![![-3729, 5088, 6244, 3716, 1490], ![-37268, 50813, 62344, 37082, 14864], ![-167244, 228066, 279839, 166470, 66732], ![-815876, 1112538, 1365064, 812017, 325508], ![-2321028, 3164988, 3883404, 2310072, 926015]]]
  hmulB := by decide  
  f := ![![![-14545, 11832, 12580, 1004, -1426]], ![![44788, -31487, -35384, -2938, 4016]], ![![3607, -2517, -2837, -236, 322]], ![![16612, -10233, -12144, -1045, 1380]], ![![2998, -1452, -1924, -176, 219]]]
  g := ![![![-4025, -3288, 6244, 3716, 1490], ![-40164, -32813, 62344, 37082, 14864], ![-180307, -147303, 279839, 166470, 66732], ![-879512, -718527, 1365064, 812017, 325508], ![-2502082, -2044104, 3883404, 2310072, 926015]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P1 : CertificateIrreducibleZModOfList' 233 2 2 7 [130, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [184, 232], [0, 1]]
 g := ![![[228, 13], [229], [157], [84, 116], [102], [218, 219], [184, 1]], ![[57, 220], [229], [157], [225, 117], [102], [205, 14], [135, 232]]]
 h' := ![![[184, 232], [38, 180], [123, 178], [31, 33], [194, 171], [86, 175], [79, 174], [0, 1]], ![[0, 1], [72, 53], [22, 55], [45, 200], [203, 62], [132, 58], [174, 59], [184, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [189, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N1 : CertifiedPrimeIdeal' SI233N1 233 where
  n := 2
  hpos := by decide
  P := [130, 49, 1]
  hirr := P233P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2223466, 5426140, 6067018, 4977190, 3159149]
  a := ![49, 29, -10, -4, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5838690, -4442620, 6067018, 4977190, 3159149]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N1 B_one_repr
lemma NI233N1 : Nat.card (O ⧸ I233N1) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![14545, -11832, -12580, -1004, 1426]] ![![-3729, 5088, 6244, 3716, 1490]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![-233, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5543, 4084, 4492, 366, -509]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-5543, 4084, 4492, 366, -509]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![71, 5, 1, 0, 0], ![123, 133, 0, 1, 0], ![185, 66, 0, 0, 1]] where
  M :=![![![-5543, 4084, 4492, 366, -509], ![16002, -11728, -12924, -1053, 1464], ![-31014, 22767, 25067, 2037, -2838], ![36606, -26877, -29568, -2386, 3342], ![-29842, 21892, 24070, 1926, -2715]]]
  hmulB := by decide  
  f := ![![![597, -446, -422, -42, 37]], ![![-1194, 802, 672, -99, -168]], ![![165, -127, -123, -18, 7]], ![![-351, 203, 138, -91, -81]], ![![181, -186, -216, -102, -34]]]
  g := ![![![-1152, -140, 4492, 366, -509], ![3315, 403, -12924, -1053, 1464], ![-6428, -779, 25067, 2037, -2838], ![7578, 911, -29568, -2386, 3342], ![-6165, -734, 24070, 1926, -2715]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [168, 131, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [108, 238], [0, 1]]
 g := ![![[153, 136], [230, 17], [204, 29], [148, 133], [193], [72, 98], [108, 1]], ![[23, 103], [154, 222], [229, 210], [172, 106], [193], [140, 141], [216, 238]]]
 h' := ![![[108, 238], [78, 178], [144, 16], [231, 183], [125, 33], [93, 77], [20, 24], [0, 1]], ![[0, 1], [182, 61], [199, 223], [158, 56], [104, 206], [44, 162], [222, 215], [108, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [185, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [168, 131, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-494088, 1150291, 1293240, 1039505, 650009]
  a := ![22, 13, -6, -1, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1424372, -780212, 1293240, 1039505, 650009]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51, 38, 40, 2, -4]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-51, 38, 40, 2, -4]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![89, 132, 1, 0, 0], ![202, 134, 0, 1, 0], ![227, 63, 0, 0, 1]] where
  M :=![![![-51, 38, 40, 2, -4], ![124, -89, -88, 2, 8], ![-180, 134, 113, -14, 0], ![-76, 78, 192, 119, -32], ![216, -116, -256, -64, 113]]]
  hmulB := by decide  
  f := ![![![1851, -1138, -1128, -78, 124]], ![![-3876, 3181, 2840, 178, -312]], ![![-1423, 1312, 1129, 68, -124]], ![![-634, 840, 656, 35, -72]], ![![755, -257, -336, -28, 37]]]
  g := ![![![-13, -22, 40, 2, -4], ![24, 45, -88, 2, 8], ![-31, -54, 113, -14, 0], ![-142, -164, 192, 119, -32], ![43, 147, -256, -64, 113]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P1 : CertificateIrreducibleZModOfList' 239 2 2 7 [166, 164, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 238], [0, 1]]
 g := ![![[168, 36], [52, 216], [51, 136], [21, 204], [124], [32, 10], [75, 1]], ![[0, 203], [0, 23], [213, 103], [25, 35], [124], [65, 229], [150, 238]]]
 h' := ![![[75, 238], [211, 233], [138, 132], [99, 61], [18, 193], [185, 29], [217, 201], [0, 1]], ![[0, 1], [0, 6], [0, 107], [133, 178], [153, 46], [209, 210], [235, 38], [75, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [77, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N1 : CertifiedPrimeIdeal' SI239N1 239 where
  n := 2
  hpos := by decide
  P := [166, 164, 1]
  hirr := P239P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-257388, 541809, 617141, 473938, 283908]
  a := ![16, 10, -3, 1, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-901111, -679141, 617141, 473938, 283908]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N1 B_one_repr
lemma NI239N1 : Nat.card (O ⧸ I239N1) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7525, 5615, 5212, 351, -577]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![-7525, 5615, 5212, 351, -577]] 
 ![![239, 0, 0, 0, 0], ![206, 1, 0, 0, 0], ![189, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![94, 0, 0, 0, 1]] where
  M :=![![![-7525, 5615, 5212, 351, -577], ![18012, -13431, -12552, -890, 1404], ![-30956, 23088, 21815, 1676, -2482], ![29900, -22300, -21952, -2157, 2650], ![-25194, 18786, 19242, 2274, -2447]]]
  hmulB := by decide  
  f := ![![![12043, -16723, -20602, -12511, -5087]], ![![10914, -15137, -18644, -11308, -4594]], ![![11873, -16437, -20235, -12245, -4967]], ![![12956, -17692, -21716, -12941, -5194]], ![![37520, -51290, -62966, -37562, -15087]]]
  g := ![![![-8807, 5615, 5212, 351, -577], ![21130, -13431, -12552, -890, 1404], ![-36501, 23088, 21815, 1676, -2482], ![35916, -22300, -21952, -2157, 2650], ![-30818, 18786, 19242, 2274, -2447]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-5543, 4084, 4492, 366, -509]] ![![-51, 38, 40, 2, -4]]
  ![![-157211, 115410, 127060, 10324, -14385]] where
 M := ![![![-157211, 115410, 127060, 10324, -14385]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![-157211, 115410, 127060, 10324, -14385]] ![![-7525, 5615, 5212, 351, -577]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![-388375, 287995, 375230, 76241, -57838]]]
 hmul := by decide  
 g := ![![![![-1625, 1205, 1570, 319, -242]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1, I239N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
    exact isPrimeI239N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0 ⊙ MulI239N1)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1745, -1302, -1838, -468, 312]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![1745, -1302, -1838, -468, 312]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![124, 136, 112, 1, 0], ![197, 223, 210, 0, 1]] where
  M :=![![![1745, -1302, -1838, -468, 312], ![-10296, 7653, 10812, 2720, -1872], ![35948, -26886, -37913, -9692, 6376], ![-100184, 74200, 104920, 26145, -18448], ![143488, -108256, -152260, -39780, 24565]]]
  hmulB := by decide  
  f := ![![![3513, -2406, -2262, -148, 248]], ![![-7736, 6037, 5404, 336, -592]], ![![13084, -9750, -8841, -556, 968]], ![![3476, -2328, -2192, -143, 240]], ![![7149, -4903, -4576, -296, 501]]]
  g := ![![![-7, -30, -62, -468, 312], ![88, 229, 412, 2720, -1872], ![-76, -542, -1209, -9692, 6376], ![1212, 2624, 4360, 26145, -18448], ![983, -731, -3550, -39780, 24565]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [103, 119, 146, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 174, 87], [36, 66, 154], [0, 1]]
 g := ![![[86, 190, 237], [71, 240], [222, 187], [218, 118], [180, 178, 15], [234, 182, 108], [1]], ![[225, 5, 164, 3], [219, 159], [196, 221], [222, 223], [181, 33, 143, 233], [106, 136, 57, 182], [222, 140, 33, 91]], ![[65, 94, 186, 61], [46, 8], [91, 40], [2, 236], [198, 239, 169, 223], [150, 240, 211, 2], [70, 110, 155, 150]]]
 h' := ![![[59, 174, 87], [217, 203, 113], [78, 10, 177], [7, 10, 123], [17, 15, 212], [239, 167, 225], [138, 122, 95], [0, 1]], ![[36, 66, 154], [121, 81, 55], [54, 146, 20], [203, 232, 71], [74, 148, 114], [178, 101, 218], [76, 74, 14], [59, 174, 87]], ![[0, 1], [88, 198, 73], [214, 85, 44], [195, 240, 47], [94, 78, 156], [170, 214, 39], [163, 45, 132], [36, 66, 154]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 60], []]
 b := ![[], [212, 216, 232], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [103, 119, 146, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4096981230323, -5801230257650, -7070020586158, -4330237955084, -1835505108872]
  a := ![-105, -72, 16, 0, -217]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3745398315803, 4117961705030, 3582459349570, -4330237955084, -1835505108872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 13997521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2491, 1858, 1718, 112, -189]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![-2491, 1858, 1718, 112, -189]] 
 ![![241, 0, 0, 0, 0], ![115, 1, 0, 0, 0], ![78, 0, 1, 0, 0], ![157, 0, 0, 1, 0], ![144, 0, 0, 0, 1]] where
  M :=![![![-2491, 1858, 1718, 112, -189], ![5894, -4396, -4068, -267, 448], ![-9934, 7409, 6865, 455, -758], ![8878, -6623, -6172, -430, 686], ![-6862, 5114, 4794, 344, -543]]]
  hmulB := by decide  
  f := ![![![43927, -30664, -34456, -2852, 3907]], ![![20451, -14250, -16024, -1327, 1817]], ![![15216, -10657, -11959, -989, 1356]], ![![27433, -19111, -21492, -1780, 2437]], ![![27210, -19034, -21370, -1768, 2423]]]
  g := ![![![-1413, 1858, 1718, 112, -189], ![3345, -4396, -4068, -267, 448], ![-5642, 7409, 6865, 455, -758], ![5065, -6623, -6172, -430, 686], ![-3920, 5114, 4794, 344, -543]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-645, -111, 62, 1, -2]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![-645, -111, 62, 1, -2]] 
 ![![241, 0, 0, 0, 0], ![144, 1, 0, 0, 0], ![164, 0, 1, 0, 0], ![170, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-645, -111, 62, 1, -2], ![62, -752, -304, 85, 4], ![-6, -63, -605, -351, 168], ![-2902, 2475, 3800, 1124, -704], ![5436, -3618, -5748, -1620, 1033]]]
  hmulB := by decide  
  f := ![![![-907477, 1237371, 1518226, 903077, 361994]], ![![-579794, 790570, 970012, 576989, 231284]], ![![-786194, 1072011, 1315335, 782401, 313624]], ![![-1462804, 1994649, 2447400, 1455820, 583572]], ![![-2453358, 3345426, 4104792, 2441760, 978805]]]
  g := ![![![21, -111, 62, 1, -2], ![596, -752, -304, 85, 4], ![676, -63, -605, -351, 168], ![-4782, 2475, 3800, 1124, -704], ![7110, -3618, -5748, -1620, 1033]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![1745, -1302, -1838, -468, 312]] ![![-2491, 1858, 1718, 112, -189]]
  ![![-57939, 43192, 60800, 15352, -10361]] where
 M := ![![![-57939, 43192, 60800, 15352, -10361]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![-57939, 43192, 60800, 15352, -10361]] ![![-645, -111, 62, 1, -2]]
  ![![241, 0, 0, 0, 0]] where
 M := ![![![-61190141, 45602743, 64386042, 16313049, -11007675]]]
 hmul := by decide  
 g := ![![![![-253901, 189223, 267162, 67689, -45675]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1, I241N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
    exact isPrimeI241N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0 ⊙ MulI241N1)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0, 0, 0]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0, 0, 0]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![0, 0, 0, 251, 0], ![0, 0, 0, 0, 251]] where
  M :=![![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![0, 0, 0, 251, 0], ![0, 0, 0, 0, 251]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 5 2 7 [129, 10, 30, 101, 18, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 148, 206, 206, 55], [71, 167, 193, 179, 81], [165, 58, 161, 18, 50], [143, 128, 193, 99, 65], [0, 1]]
 g := ![![[221, 20, 118, 10, 237], [183, 170, 156, 238, 92], [180, 42, 63, 118], [111, 106, 99, 10, 197], [19, 3, 30, 222, 85], [223, 233, 1], []], ![[155, 121, 51, 132, 74, 135, 181, 87], [55, 46, 168, 220, 153, 197, 58, 76], [156, 171, 235, 155], [21, 86, 120, 24, 169, 209, 106, 59], [99, 92, 169, 166, 134, 124, 161, 228], [237, 65, 75, 64, 86, 155, 87, 177], [230, 49, 26, 118, 196, 70, 184, 213]], ![[30, 170, 132, 140, 179, 81, 63, 114], [76, 82, 171, 53, 93, 156, 128, 68], [205, 41, 135, 194], [168, 139, 130, 181, 194, 80, 81, 211], [233, 231, 159, 63, 38, 223, 116, 180], [202, 232, 164, 106, 228, 65, 21, 31], [18, 136, 76, 203, 129, 102, 144, 74]], ![[34, 107, 31, 249, 66, 178, 161, 143], [27, 229, 202, 83, 246, 237, 240, 98], [185, 139, 237, 113], [212, 222, 22, 185, 195, 67, 178, 185], [153, 175, 150, 106, 204, 102, 180, 223], [147, 143, 148, 14, 195, 107, 190, 42], [116, 119, 87, 165, 167, 222, 177, 2]], ![[153, 89, 179, 44, 233, 124, 65, 194], [209, 225, 115, 43, 217, 76, 119, 125], [167, 201, 134, 16], [187, 182, 147, 230, 65, 98, 223, 207], [50, 227, 120, 168, 177, 74, 174, 93], [219, 145, 14, 13, 27, 148, 247, 31], [66, 5, 224, 100, 89, 133, 20, 31]]]
 h' := ![![[105, 148, 206, 206, 55], [238, 90, 109, 152, 57], [16, 2, 32, 13, 208], [239, 243, 100, 167, 108], [59, 242, 8, 47, 166], [98, 92, 138, 95, 33], [0, 0, 0, 1], [0, 1]], ![[71, 167, 193, 179, 81], [86, 41, 43, 115, 41], [153, 10, 203, 197, 15], [166, 81, 9, 137, 197], [226, 249, 180, 191, 151], [118, 18, 218, 5, 136], [212, 11, 125, 76, 181], [105, 148, 206, 206, 55]], ![[165, 58, 161, 18, 50], [195, 208, 32, 188, 219], [31, 135, 73, 198, 241], [11, 180, 168, 129, 52], [124, 37, 18, 127, 39], [39, 238, 175, 52, 73], [173, 76, 144, 129, 220], [71, 167, 193, 179, 81]], ![[143, 128, 193, 99, 65], [103, 75, 34, 58, 234], [235, 114, 143, 106, 152], [249, 109, 145, 59, 149], [231, 144, 223, 242, 189], [53, 218, 60, 235, 89], [74, 82, 2, 125, 36], [165, 58, 161, 18, 50]], ![[0, 1], [181, 88, 33, 240, 202], [222, 241, 51, 239, 137], [207, 140, 80, 10, 247], [61, 81, 73, 146, 208], [81, 187, 162, 115, 171], [77, 82, 231, 171, 65], [143, 128, 193, 99, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93, 80, 245, 215], [], [], []]
 b := ![[], [175, 114, 185, 34, 133], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 5
  hpos := by decide
  P := [129, 10, 30, 101, 18, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![462801451292829980205, -631409803683444734508, -774658973705531444588, -461001653074078725148, -184949029576573775524]
  a := ![-38, -25, 7, -1, -77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1843830483238366455, -2515576907105357508, -3086290731894547588, -1836659972406688148, -736848723412644524]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 996250626251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def PBC251 : ContainsPrimesAboveP 251 ![I251N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![251, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 251 (by decide) 𝕀



lemma PB3864I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB3864I5 : PrimesBelowBoundCertificateInterval O 197 251 3864 where
  m := 9
  g := ![1, 3, 2, 2, 3, 2, 3, 3, 1]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB3864I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1, I239N2]
    · exact ![I241N0, I241N1, I241N2]
    · exact ![I251N0]
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
    · exact ![312079600999]
    · exact ![9393931, 211, 211]
    · exact ![2472973441, 223]
    · exact ![11697083, 51529]
    · exact ![52441, 52441, 229]
    · exact ![12649337, 54289]
    · exact ![57121, 57121, 239]
    · exact ![13997521, 241, 241]
    · exact ![996250626251]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
      exact NI211N2
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
      exact NI239N2
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
      exact NI241N2
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
  β := ![I211N1, I211N2, I223N1, I229N2, I239N2, I241N1, I241N2]
  Il := ![[], [I211N1, I211N2], [I223N1], [], [I229N2], [], [I239N2], [I241N1, I241N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
