
import IdealArithmetic.Examples.NF5_3_379687500_1.RI5_3_379687500_1
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


def P199P0 : CertificateIrreducibleZModOfList' 199 5 2 7 [27, 113, 12, 67, 156, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 56, 12, 105, 83], [66, 128, 178, 68, 159], [117, 136, 41, 23, 9], [177, 77, 167, 3, 147], [0, 1]]
 g := ![![[196, 164, 24, 37, 111], [38, 59, 38, 194, 61], [87, 0, 122, 15, 100], [193, 176, 41, 58], [109, 186, 36, 81], [43, 1], []], ![[23, 43, 188, 85, 99, 103, 80, 12], [87, 22, 59, 75, 130, 101, 9, 147], [26, 12, 7, 127, 80, 83, 110, 12], [61, 146, 65, 180], [173, 122, 122, 111], [103, 142, 82, 29], [80, 46, 78, 46, 22, 134, 132, 60]], ![[29, 146, 194, 6, 184, 147, 59, 194], [38, 57, 165, 124, 158, 98, 30, 76], [124, 41, 99, 153, 138, 182, 182, 195], [191, 183, 138, 162], [172, 29, 153, 162], [158, 110, 175, 130], [7, 41, 66, 140, 134, 48, 11, 78]], ![[119, 147, 120, 52, 59, 183, 121, 28], [12, 144, 85, 60, 179, 29, 166, 128], [111, 127, 128, 138, 32, 17, 163, 81], [109, 78, 181, 169], [6, 187, 171, 157], [174, 152, 50, 50], [79, 69, 101, 173, 147, 108, 121, 132]], ![[150, 33, 156, 74, 6, 47, 177, 198], [89, 123, 194, 156, 66, 72, 193, 164], [114, 181, 92, 38, 10, 141, 47, 15], [11, 179, 72, 184], [128, 73, 148, 86], [119, 142, 185, 196], [93, 184, 153, 1, 88, 38, 131, 85]]]
 h' := ![![[81, 56, 12, 105, 83], [168, 12, 153, 169, 132], [39, 35, 181, 177, 114], [151, 154, 18, 134, 10], [136, 77, 23, 108, 43], [33, 89, 167, 92, 190], [0, 0, 0, 1], [0, 1]], ![[66, 128, 178, 68, 159], [24, 118, 67, 17, 187], [125, 170, 171, 15, 42], [173, 18, 133, 2, 187], [167, 188, 11, 162, 58], [103, 163, 165, 155, 132], [140, 53, 154, 183, 167], [81, 56, 12, 105, 83]], ![[117, 136, 41, 23, 9], [177, 63, 71, 116, 5], [157, 135, 129, 103, 60], [119, 152, 98, 10, 152], [36, 72, 21, 54, 180], [125, 74, 149, 195, 180], [150, 2, 194, 122, 145], [66, 128, 178, 68, 159]], ![[177, 77, 167, 3, 147], [105, 146, 193, 1, 141], [104, 18, 39, 106, 13], [60, 181, 73, 130, 3], [139, 137, 175, 196, 186], [36, 192, 189, 11, 117], [117, 133, 197, 89, 100], [117, 136, 41, 23, 9]], ![[0, 1], [113, 59, 113, 95, 132], [82, 40, 77, 196, 169], [111, 92, 76, 122, 46], [127, 123, 168, 77, 130], [198, 79, 126, 144, 177], [174, 11, 52, 3, 185], [177, 77, 167, 3, 147]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [189, 137, 195, 103], [], [], []]
 b := ![[], [23, 19, 73, 49, 157], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 5
  hpos := by decide
  P := [27, 113, 12, 67, 156, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1074493431759596, -2381686369894251, -3887236241314533, -18889059084684488, -37351154669325525]
  a := ![5, -3, -9, -44, -105]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5399464481204, -11968273215549, -19533850458867, -94919894897912, -187694244569475]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-129, -161, -254, 119, 288]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-129, -161, -254, 119, 288]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![112, 143, 1, 0, 0], ![20, 130, 0, 1, 0], ![19, 118, 0, 0, 1]] where
  M :=![![![-129, -161, -254, 119, 288], ![50, -10, -92, 41, 102], ![20, 91, 11, -7, -12], ![2, 13, 82, -36, -90], ![-10, -20, -44, 20, 49]]]
  hmulB := by decide  
  f := ![![![5, 5, -4, -17, -72]], ![![-38, -12, 26, 139, 510]], ![![-22, -5, 15, 82, 294]], ![![-30, -9, 20, 110, 402]], ![![-17, -5, 12, 63, 229]]]
  g := ![![![97, -63, -254, 119, 288], ![36, -20, -92, 41, 102], ![-4, 4, 11, -7, -12], ![-32, 17, 82, -36, -90], ![17, -10, -44, 20, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [136, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [163, 210], [0, 1]]
 g := ![![[50, 45], [167, 87], [51], [65], [16, 148], [199], [163, 1]], ![[0, 166], [0, 124], [51], [65], [86, 63], [199], [115, 210]]]
 h' := ![![[163, 210], [76, 195], [93, 147], [158, 85], [145, 102], [113, 123], [198, 58], [0, 1]], ![[0, 1], [0, 16], [0, 64], [87, 126], [102, 109], [117, 88], [157, 153], [163, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [140, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [136, 48, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2348751, 3171688, 6067455, 30033904, 64349784]
  a := ![59, -60, -118, -533, -1236]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11873117, -58588419, 6067455, 30033904, 64349784]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, 170, 136, -74, -186]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![57, 170, 136, -74, -186]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![157, 80, 1, 0, 0], ![100, 87, 0, 1, 0], ![35, 57, 0, 0, 1]] where
  M :=![![![57, 170, 136, -74, -186], ![-38, -17, 134, -6, 54], ![66, -44, -89, -292, -1170], ![-586, -226, 250, 1967, 7626], ![324, 136, -138, -1066, -4133]]]
  hmulB := by decide  
  f := ![![![1387, -598, 2484, -1262, -3102]], ![![-578, 125, -1282, -358, -270]], ![![815, -402, 1359, -1102, -2460]], ![![424, -257, 612, -915, -1884]], ![![73, -59, 76, -262, -509]]]
  g := ![![![-35, 30, 136, -74, -186], ![-106, -63, 134, -6, 54], ![399, 470, -89, -292, -1170], ![-2386, -2967, 250, 1967, 7626], ![1295, 1609, -138, -1066, -4133]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P1 : CertificateIrreducibleZModOfList' 211 2 2 7 [65, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [147, 210], [0, 1]]
 g := ![![[199, 13], [87, 64], [199], [204], [103, 58], [62], [147, 1]], ![[0, 198], [0, 147], [199], [204], [189, 153], [62], [83, 210]]]
 h' := ![![[147, 210], [42, 60], [121, 203], [117, 58], [57, 41], [203, 144], [151, 22], [0, 1]], ![[0, 1], [0, 151], [0, 8], [203, 153], [176, 170], [60, 67], [9, 189], [147, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [176, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N1 : CertifiedPrimeIdeal' SI211N1 211 where
  n := 2
  hpos := by decide
  P := [65, 64, 1]
  hirr := P211P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9869, 14373, 26833, 132420, 280655]
  a := ![4, -3, -7, -36, -83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-129325, -140522, 26833, 132420, 280655]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N1 B_one_repr
lemma NI211N1 : Nat.card (O ⧸ I211N1) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, 28, -142, 64, 162]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![-77, 28, -142, 64, 162]] 
 ![![211, 0, 0, 0, 0], ![199, 1, 0, 0, 0], ![67, 0, 1, 0, 0], ![171, 0, 0, 1, 0], ![166, 0, 0, 0, 1]] where
  M :=![![![-77, 28, -142, 64, 162], ![34, -13, 58, -26, -66], ![-14, 8, -25, 12, 30], ![6, -2, 14, -1, -6], ![-6, 2, -12, 4, 11]]]
  hmulB := by decide  
  f := ![![![33, 88, 42, -32, -90]], ![![31, 83, 40, -30, -84]], ![![11, 28, 13, -12, -36]], ![![23, 70, 36, -13, -24]], ![![28, 70, 32, -32, -97]]]
  g := ![![![-161, 28, -142, 64, 162], ![67, -13, 58, -26, -66], ![-33, 8, -25, 12, 30], ![3, -2, 14, -1, -6], ![-10, 2, -12, 4, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-129, -161, -254, 119, 288]] ![![57, 170, 136, -74, -186]]
  ![![5579, 4257, -26506, 11745, 29670]] where
 M := ![![![5579, 4257, -26506, 11745, 29670]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![5579, 4257, -26506, 11745, 29670]] ![![-77, 28, -142, 64, 162]]
  ![![211, 0, 0, 0, 0]] where
 M := ![![![-21311, -75327, -74272, 35237, 83556]]]
 hmul := by decide  
 g := ![![![![-101, -357, -352, 167, 396]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0, 0, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0, 0, 0]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![0, 0, 223, 0, 0], ![0, 0, 0, 223, 0], ![0, 0, 0, 0, 223]] where
  M :=![![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![0, 0, 223, 0, 0], ![0, 0, 0, 223, 0], ![0, 0, 0, 0, 223]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 5 2 7 [80, 183, 121, 121, 118, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [128, 192, 69, 211, 183], [180, 201, 119, 139, 105], [81, 93, 180, 117, 142], [162, 182, 78, 202, 16], [0, 1]]
 g := ![![[43, 43, 65, 79, 15], [113, 213, 90, 150, 81], [66, 56, 153, 153, 14], [98, 12, 3, 174, 121], [173, 27, 14, 179, 83], [105, 1], []], ![[217, 29, 91, 155, 144, 35, 51, 69], [151, 216, 24, 176, 213, 108, 104, 127], [193, 212, 139, 80, 54, 191, 10, 203], [137, 24, 183, 6, 27, 217, 27, 50], [199, 36, 158, 125, 111, 31], [78, 134, 18, 32], [170, 53, 101, 137, 97, 119, 39, 1]], ![[131, 54, 54, 170, 127, 152, 90, 196], [76, 77, 114, 38, 24, 193, 55, 2], [15, 176, 174, 35, 145, 164, 17, 146], [41, 9, 192, 162, 20, 61, 70, 76], [193, 156, 162, 162, 117, 26, 130, 50], [30, 138, 51, 19], [176, 144, 7, 115, 31, 94, 72, 32]], ![[155, 5, 148, 78, 4, 108, 210, 193], [18, 58, 188, 1, 54, 99, 58, 161], [121, 42, 184, 31, 72, 14, 178, 219], [46, 10, 107, 17, 94, 43, 15, 198], [184, 89, 49, 185, 177, 203, 49, 21], [30, 33, 81, 47], [172, 216, 76, 85, 181, 112, 198, 191]], ![[57, 47, 209, 72, 2, 92, 164, 110], [19, 180, 201, 176, 78, 221, 6, 177], [18, 167, 161, 39, 176, 35, 83, 62], [120, 122, 41, 210, 195, 202, 148, 126], [11, 165, 56, 112, 49, 137, 56, 164], [155, 133, 202, 164], [63, 62, 119, 17, 33, 43, 64, 82]]]
 h' := ![![[128, 192, 69, 211, 183], [103, 23, 106, 85, 125], [72, 54, 150, 19, 9], [188, 34, 148, 42, 56], [209, 201, 67, 154, 212], [74, 106, 46, 108, 200], [0, 0, 0, 1], [0, 1]], ![[180, 201, 119, 139, 105], [12, 190, 116, 22, 98], [83, 159, 63, 35, 50], [98, 104, 29, 105, 119], [109, 24, 164, 148, 122], [182, 208, 35, 81], [63, 154, 70, 184, 60], [128, 192, 69, 211, 183]], ![[81, 93, 180, 117, 142], [148, 102, 18, 17, 136], [131, 101, 57, 178, 82], [71, 86, 144, 61, 156], [49, 137, 25, 176, 203], [30, 18, 4, 89, 36], [73, 150, 200, 14, 58], [180, 201, 119, 139, 105]], ![[162, 182, 78, 202, 16], [154, 173, 151, 150, 134], [200, 54, 42, 182, 87], [211, 140, 71, 172, 198], [125, 43, 135, 22, 174], [68, 87, 20, 106, 193], [98, 216, 105, 53, 173], [81, 93, 180, 117, 142]], ![[0, 1], [66, 181, 55, 172, 176], [190, 78, 134, 32, 218], [63, 82, 54, 66, 140], [40, 41, 55, 169, 181], [31, 27, 118, 62, 17], [122, 149, 71, 194, 155], [162, 182, 78, 202, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [171, 105, 135, 165], [], [], []]
 b := ![[], [90, 80, 98, 107, 32], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 5
  hpos := by decide
  P := [80, 183, 121, 121, 118, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4423458995593367736, 10308297042076349425, 16604355639699413956, 80549243552139667537, 158050095416740224728]
  a := ![-26, 23, 50, 230, 547]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19836138993692232, 46225547273884975, 74458993899997372, 361207370188967119, 708744822496592936]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 551473077343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def PBC223 : ContainsPrimesAboveP 223 ![I223N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![223, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 223 (by decide) 𝕀

instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 140, 314, -144, -352]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![19, 140, 314, -144, -352]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![201, 117, 129, 1, 0], ![166, 171, 203, 0, 1]] where
  M :=![![![19, 140, 314, -144, -352], ![-64, -125, 60, -22, -64], ![-20, -86, -127, 70, 164], ![24, 50, -40, 79, 152], ![-6, -2, 42, -34, -71]]]
  hmulB := by decide  
  f := ![![![73, -32, 134, -60, -152]], ![![-32, 13, -60, 26, 64]], ![![12, -6, 27, -2, 4]], ![![55, -25, 103, -41, -100]], ![![40, -19, 77, -26, -59]]]
  g := ![![![385, 340, 398, -144, -352], ![66, 59, 70, -22, -64], ![-182, -160, -187, 70, 164], ![-181, -155, -181, 79, 152], ![82, 71, 83, -34, -71]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [34, 14, 213, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [171, 152, 83], [70, 74, 144], [0, 1]]
 g := ![![[15, 166, 27], [115, 1, 176], [110, 167], [137, 192], [99, 110], [145, 82, 196], [1]], ![[0, 27, 79, 72], [69, 116, 75, 105], [134, 90], [93, 97], [99, 59], [147, 63, 171, 200], [95, 133, 21, 201]], ![[167, 90, 175, 113], [84, 203, 131, 44], [212, 84], [208, 161], [94, 131], [222, 100, 197, 97], [13, 194, 196, 26]]]
 h' := ![![[171, 152, 83], [176, 34, 77], [61, 98, 160], [13, 2, 124], [49, 114, 173], [64, 197, 164], [193, 213, 14], [0, 1]], ![[70, 74, 144], [214, 114, 121], [159, 205, 225], [42, 172, 35], [139, 9, 18], [217, 91, 112], [30, 193, 101], [171, 152, 83]], ![[0, 1], [157, 79, 29], [67, 151, 69], [187, 53, 68], [201, 104, 36], [30, 166, 178], [15, 48, 112], [70, 74, 144]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [191, 70], []]
 b := ![[], [120, 49, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [34, 14, 213, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![877734908, -468692442, -1410946840, -7253662908, -17945063352]
  a := ![11, -6, -16, -92, -232]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![19549535224, 17254694718, 20163697924, -7253662908, -17945063352]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, -32, 134, -60, -152]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![73, -32, 134, -60, -152]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![140, 98, 1, 0, 0], ![127, 70, 0, 1, 0], ![143, 53, 0, 0, 1]] where
  M :=![![![73, -32, 134, -60, -152], ![-32, 13, -60, 26, 64], ![12, -6, 27, -2, 4], ![8, 10, -16, -31, -152], ![-2, -6, 14, 18, 83]]]
  hmulB := by decide  
  f := ![![![19, 140, 314, -144, -352]], ![![-64, -125, 60, -22, -64]], ![![-16, 32, 219, -98, -244]], ![![-9, 40, 194, -87, -216]], ![![-3, 59, 212, -96, -237]]]
  g := ![![![47, -4, 134, -60, -152], ![-18, 3, -60, 26, 64], ![-18, -12, 27, -2, 4], ![123, 52, -16, -31, -152], ![-71, -31, 14, 18, 83]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P1 : CertificateIrreducibleZModOfList' 227 2 2 7 [51, 157, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 226], [0, 1]]
 g := ![![[101, 74], [86, 219], [81], [100], [188], [62, 141], [70, 1]], ![[60, 153], [207, 8], [81], [100], [188], [171, 86], [140, 226]]]
 h' := ![![[70, 226], [154, 55], [94, 30], [65, 9], [202, 217], [16, 85], [62, 82], [0, 1]], ![[0, 1], [145, 172], [151, 197], [14, 218], [183, 10], [64, 142], [127, 145], [70, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [15, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N1 : CertifiedPrimeIdeal' SI227N1 227 where
  n := 2
  hpos := by decide
  P := [51, 157, 1]
  hirr := P227P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-34145, -11158, 20108, 118408, 449316]
  a := ![-4, 2, 8, 24, 84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-361847, -150150, 20108, 118408, 449316]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N1 B_one_repr
lemma NI227N1 : Nat.card (O ⧸ I227N1) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![19, 140, 314, -144, -352]] ![![73, -32, 134, -60, -152]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3593, -1455, 6402, -3069, -8022]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![3593, -1455, 6402, -3069, -8022]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![43, 47, 1, 0, 0], ![40, 124, 0, 1, 0], ![110, 114, 0, 0, 1]] where
  M :=![![![3593, -1455, 6402, -3069, -8022], ![-1884, 524, -2640, 2361, 7476], ![2754, 477, 131, -7359, -27930], ![-13212, -4605, 6330, 42608, 165732], ![7284, 2448, -3216, -23202, -90121]]]
  hmulB := by decide  
  f := ![![![2981, 23001, 50100, -23031, -56238]], ![![-10176, -20050, 10146, -3999, -11256]], ![![-1543, 142, 11399, -5103, -12768]], ![![-4972, -6811, 14208, -6172, -15876]], ![![-3638, 1068, 29148, -13068, -32653]]]
  g := ![![![3203, 4335, 6402, -3069, -8022], ![-3516, -4456, -2640, 2361, 7476], ![14689, 17864, 131, -7359, -27930], ![-88298, -106895, 6330, 42608, 165732], ![47978, 58098, -3216, -23202, -90121]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [25, 156, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 228], [0, 1]]
 g := ![![[107, 55], [213], [2, 36], [45], [228], [153, 224], [73, 1]], ![[0, 174], [213], [111, 193], [45], [228], [17, 5], [146, 228]]]
 h' := ![![[73, 228], [152, 183], [179, 30], [201, 6], [69, 31], [68, 122], [7, 37], [0, 1]], ![[0, 1], [0, 46], [79, 199], [181, 223], [42, 198], [43, 107], [189, 192], [73, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [205]]
 b := ![[], [209, 217]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [25, 156, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17217, 19535, 40007, 195892, 434991]
  a := ![-4, 8, 13, 41, 97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-250752, -330744, 40007, 195892, 434991]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51, 60, -210, -82, -432]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![-51, 60, -210, -82, -432]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![189, 133, 1, 0, 0], ![53, 133, 0, 1, 0], ![168, 122, 0, 0, 1]] where
  M :=![![![-51, 60, -210, -82, -432], ![-268, -133, 246, 988, 3900], ![1924, 720, -1069, -6358, -24804], ![-12088, -4434, 6450, 39669, 154632], ![6552, 2406, -3504, -21510, -83851]]]
  hmulB := by decide  
  f := ![![![33, 384, 930, -394, -984]], ![![-196, -361, 186, 136, 180]], ![![-87, 107, 875, -240, -696]], ![![-107, -115, 330, 23, -60]], ![![-80, 88, 780, -226, -643]]]
  g := ![![![509, 400, -210, -82, -432], ![-3294, -2795, 246, 988, 3900], ![20559, 17531, -1069, -6358, -24804], ![-127999, -109185, 6450, 39669, 154632], ![69414, 59210, -3504, -21510, -83851]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P1 : CertificateIrreducibleZModOfList' 229 2 2 7 [76, 220, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 228], [0, 1]]
 g := ![![[27, 226], [213], [51, 148], [184], [168], [26, 25], [9, 1]], ![[0, 3], [213], [9, 81], [184], [168], [22, 204], [18, 228]]]
 h' := ![![[9, 228], [131, 189], [17, 30], [133, 182], [182, 118], [85, 175], [3, 5], [0, 1]], ![[0, 1], [0, 40], [58, 199], [168, 47], [99, 111], [57, 54], [48, 224], [9, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [152]]
 b := ![[], [116, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N1 : CertifiedPrimeIdeal' SI229N1 229 where
  n := 2
  hpos := by decide
  P := [76, 220, 1]
  hirr := P229P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1834, 5326, 8552, 41219, 78851]
  a := ![2, -3, -4, -20, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-74453, -70891, 8552, 41219, 78851]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N1 B_one_repr
lemma NI229N1 : Nat.card (O ⧸ I229N1) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 9, 2, 11, 44]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![1, 9, 2, 11, 44]] 
 ![![229, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![118, 0, 1, 0, 0], ![172, 0, 0, 1, 0], ![129, 0, 0, 0, 1]] where
  M :=![![![1, 9, 2, 11, 44], ![22, 12, -2, -75, -286], ![-136, -53, 73, 439, 1712], ![834, 303, -448, -2736, -10666], ![-452, -164, 242, 1484, 5785]]]
  hmulB := by decide  
  f := ![![![52565, -21923, 95464, -42959, -108940]], ![![11147, -4649, 20244, -9110, -23102]], ![![27130, -11315, 49271, -22173, -56228]], ![![39462, -16459, 71666, -32256, -81794]], ![![29629, -12357, 53810, -24213, -61403]]]
  g := ![![![-36, 9, 2, 11, 44], ![216, 12, -2, -75, -286], ![-1321, -53, 73, 439, 1712], ![8233, 303, -448, -2736, -10666], ![-4465, -164, 242, 1484, 5785]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![3593, -1455, 6402, -3069, -8022]] ![![-51, 60, -210, -82, -432]]
  ![![-2937927, -674451, 357840, 8372977, 32065230]] where
 M := ![![![-2937927, -674451, 357840, 8372977, 32065230]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![-2937927, -674451, 357840, 8372977, 32065230]] ![![1, 9, 2, 11, 44]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![-7576863231, -2775185964, 4030287332, 24851694636, 96867429146]]]
 hmul := by decide  
 g := ![![![![-33086739, -12118716, 17599508, 108522684, 423001874]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-198207, 82569, -360091, 162042, 410952]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![-198207, 82569, -360091, 162042, 410952]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![0, 0, 0, 233, 0], ![123, 150, 227, 72, 1]] where
  M :=![![![-198207, 82569, -360091, 162042, 410952], ![86868, -36165, 157743, -71089, -180420], ![-38242, 15779, -69012, 31750, 81402], ![17902, -6492, 29627, -17674, -50334], ![-16378, 6299, -28184, 15037, 41123]]]
  hmulB := by decide  
  f := ![![![37, 106, 63, -25, -60]], ![![-10, 12, 91, -2, -30]], ![![-26, -12, 36, 237, 426]], ![![-48, 211, 273, 1509, 2712]], ![![-27, 117, 211, 681, 1199]]]
  g := ![![![-217791, -264207, -401915, -126294, 410952], ![95616, 115995, 176451, 55447, -180420], ![-43136, -52337, -79602, -25018, 81402], ![26648, 32376, 49165, 15478, -50334], ![-21779, -26447, -40185, -12643, 41123]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 4 2 7 [37, 226, 62, 51, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [217, 96, 52, 149], [31, 153, 145, 116], [167, 216, 36, 201], [0, 1]]
 g := ![![[76, 25, 58, 14], [45, 84, 196], [229, 49, 25], [200, 46, 219, 16], [65, 13, 92], [199, 209, 182, 1], []], ![[2, 28, 165, 65, 172, 78], [120, 28, 124], [180, 65, 195], [167, 88, 38, 219, 215, 165], [216, 143, 231], [59, 129, 124, 80, 2, 118], [158, 158, 7, 118, 159, 48]], ![[66, 46, 73, 29, 102, 98], [131, 1, 63], [171, 53, 123], [178, 202, 73, 135, 14, 131], [226, 206, 112], [38, 193, 94, 224, 199, 25], [27, 106, 161, 81, 86, 29]], ![[225, 135, 148, 18, 41, 182], [210, 129, 195], [192, 122, 26], [68, 19, 142, 11, 194, 183], [169, 40, 161], [87, 91, 15, 193, 5, 201], [60, 186, 48, 70, 9, 85]]]
 h' := ![![[217, 96, 52, 149], [217, 190, 215, 108], [22, 179, 127, 14], [56, 43, 179, 5], [186, 180, 191, 229], [93, 184, 99, 32], [0, 0, 0, 1], [0, 1]], ![[31, 153, 145, 116], [170, 41, 188, 226], [79, 118, 218, 130], [94, 3, 1, 112], [111, 141, 203, 217], [114, 148, 106, 109], [77, 20, 97, 77], [217, 96, 52, 149]], ![[167, 216, 36, 201], [230, 81, 196, 81], [76, 30, 153, 210], [47, 177, 128, 194], [178, 99, 49, 196], [102, 182, 58, 47], [133, 25, 19, 154], [31, 153, 145, 116]], ![[0, 1], [119, 154, 100, 51], [82, 139, 201, 112], [14, 10, 158, 155], [74, 46, 23, 57], [227, 185, 203, 45], [136, 188, 117, 1], [167, 216, 36, 201]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [13, 90, 180], []]
 b := ![[], [], [210, 106, 149, 127], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 4
  hpos := by decide
  P := [37, 226, 62, 51, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-186230381221, -46891846414, 124530439614, 728855384442, 2562288088380]
  a := ![-3, 3, 13, 23, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1353423456017, -1649742940358, -2495771955462, -788651875446, 2562288088380]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 2947295521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, -106, -63, 25, 60]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-37, -106, -63, 25, 60]] 
 ![![233, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![215, 0, 1, 0, 0], ![163, 0, 0, 1, 0], ![99, 0, 0, 0, 1]] where
  M :=![![![-37, -106, -63, 25, 60], ![10, -12, -91, 2, 30], ![26, 12, -36, -237, -426], ![48, -211, -273, -1509, -2712], ![-16, 45, 64, 399, 719]]]
  hmulB := by decide  
  f := ![![![198207, -82569, 360091, -162042, -410952]], ![![18342, -7641, 33323, -14995, -38028]], ![![183059, -76258, 332569, -149660, -379554]], ![![138583, -57735, 251782, -113284, -287274]], ![![84287, -35110, 153121, -68915, -174787]]]
  g := ![![![25, -106, -63, 25, 60], ![71, -12, -91, 2, 30], ![379, 12, -36, -237, -426], ![2480, -211, -273, -1509, -2712], ![-648, 45, 64, 399, 719]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![-198207, 82569, -360091, 162042, 410952]] ![![-37, -106, -63, 25, 60]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-116595, 48576, -211829, 95313, 241708]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-116595, 48576, -211829, 95313, 241708]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![162, 8, 146, 1, 0], ![111, 172, 236, 0, 1]] where
  M :=![![![-116595, 48576, -211829, 95313, 241708], ![51082, -21282, 92807, -41756, -105890], ![-22378, 9326, -40660, 18295, 46378], ![9788, -4083, 17833, -7913, -20036], ![-9232, 3851, -16796, 7513, 19025]]]
  hmulB := by decide  
  f := ![![![-545, -1367, -365, 200, 416]], ![![16, -345, -1183, 539, 1328]], ![![250, 555, -56, 12, 62]], ![![-216, -598, -319, 160, 362]], ![![5, -336, -1077, 493, 1211]]]
  g := ![![![-177351, -176936, -297785, 95313, 241708], ![77696, 77514, 130457, -41756, -105890], ![-34034, -33950, -57142, 18295, 46378], ![14710, 14667, 24693, -7913, -20036], ![-13967, -13927, -23446, 7513, 19025]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [98, 57, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [161, 67, 211], [21, 171, 28], [0, 1]]
 g := ![![[152, 75, 213], [93, 149, 127], [172, 159, 81], [34, 106, 121], [29, 121], [26, 77, 142], [1]], ![[106, 46, 139, 81], [193, 175, 128, 192], [230, 162, 142, 17], [178, 173, 234, 9], [42, 125], [92, 186, 82, 186], [155, 164, 182, 36]], ![[168, 62, 152, 73], [144, 196, 27, 111], [83, 61, 216, 230], [90, 154, 225, 13], [135, 182], [124, 145, 26, 179], [72, 182, 95, 203]]]
 h' := ![![[161, 67, 211], [207, 36, 90], [113, 144, 102], [14, 133, 230], [134, 214, 228], [81, 98, 228], [141, 182, 182], [0, 1]], ![[21, 171, 28], [137, 210, 42], [126, 78, 26], [169, 97, 234], [2, 60, 14], [154, 175, 155], [208, 109, 214], [161, 67, 211]], ![[0, 1], [28, 232, 107], [6, 17, 111], [152, 9, 14], [188, 204, 236], [89, 205, 95], [54, 187, 82], [21, 171, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [216, 48], []]
 b := ![[], [158, 168, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [98, 57, 57, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-329608592, 236667864, 602318234, 3059765305, 7254942973]
  a := ![-8, 5, 12, 68, 169]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5444812795, -5322559188, -9030501916, 3059765305, 7254942973]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-545, -1367, -365, 200, 416]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-545, -1367, -365, 200, 416]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![236, 93, 1, 0, 0], ![40, 191, 0, 1, 0], ![9, 29, 0, 0, 1]] where
  M :=![![![-545, -1367, -365, 200, 416], ![16, -345, -1183, 539, 1328], ![250, 555, -56, 12, 62], ![38, 262, 529, -224, -550], ![-62, -207, -196, 87, 205]]]
  hmulB := by decide  
  f := ![![![-116595, 48576, -211829, 95313, 241708]], ![![51082, -21282, 92807, -41756, -105890]], ![![-95348, 39724, -173227, 77945, 197664]], ![![21350, -8895, 38790, -17451, -44254]], ![![1769, -737, 3214, -1446, -3667]]]
  g := ![![![309, -74, -365, 200, 416], ![1028, -133, -1183, 539, 1328], ![52, 7, -56, 12, 62], ![-464, 41, 529, -224, -550], ![171, -19, -196, 87, 205]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P1 : CertificateIrreducibleZModOfList' 239 2 2 7 [213, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [203, 238], [0, 1]]
 g := ![![[17, 193], [125, 196], [238, 226], [156, 25], [183], [187, 116], [203, 1]], ![[0, 46], [0, 43], [228, 13], [212, 214], [183], [74, 123], [167, 238]]]
 h' := ![![[203, 238], [143, 77], [213, 225], [232, 153], [10, 5], [82, 30], [20, 127], [0, 1]], ![[0, 1], [0, 162], [0, 14], [221, 86], [69, 234], [197, 209], [228, 112], [203, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [211]]
 b := ![[], [226, 225]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N1 : CertifiedPrimeIdeal' SI239N1 239 where
  n := 2
  hpos := by decide
  P := [213, 36, 1]
  hirr := P239P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12349, 13219, 27914, 139631, 311882]
  a := ![-4, 4, 7, 37, 88]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-62729, -160238, 27914, 139631, 311882]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N1 B_one_repr
lemma NI239N1 : Nat.card (O ⧸ I239N1) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-116595, 48576, -211829, 95313, 241708]] ![![-545, -1367, -365, 200, 416]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![239, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


def P241P0 : CertificateIrreducibleZModOfList' 241 5 2 7 [150, 90, 24, 48, 25, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 149, 83, 227, 2], [98, 201, 21, 36, 158], [185, 183, 11, 176, 214], [154, 189, 126, 43, 108], [0, 1]]
 g := ![![[32, 165, 189, 127, 233], [120, 73, 118, 238], [51, 165, 147, 161], [76, 117, 45, 119], [231, 223, 214, 146, 36], [95, 216, 1], []], ![[195, 224, 8, 156, 103, 144, 161, 212], [152, 99, 40, 182], [91, 161, 71, 193], [217, 35, 81, 121], [74, 153, 168, 208, 45, 144, 144, 77], [234, 128, 227, 236, 133, 220, 131, 47], [205, 85, 132, 89, 202, 143, 114, 8]], ![[70, 224, 149, 149, 94, 101, 63, 36], [17, 59, 117, 9], [80, 235, 114, 188], [61, 49, 73, 106], [225, 206, 176, 168, 97, 238, 152, 209], [204, 144, 56, 129, 121, 5, 174, 134], [87, 121, 224, 79, 149, 230, 46, 106]], ![[124, 120, 89, 47, 4, 151, 209, 75], [42, 172, 193, 159], [227, 215, 195, 67], [14, 89, 163, 119], [205, 160, 57, 165, 97, 113, 106, 221], [191, 5, 134, 112, 38, 169, 203, 113], [164, 10, 12, 116, 123, 75, 229, 79]], ![[116, 107, 200, 119, 204, 231, 2, 30], [198, 184, 53, 141], [18, 106, 101, 166], [205, 173, 59, 81], [213, 34, 68, 116, 147, 13, 163, 100], [143, 196, 206, 101, 141, 18, 217, 5], [199, 169, 107, 220, 77, 166, 209, 5]]]
 h' := ![![[20, 149, 83, 227, 2], [233, 184, 92, 166, 76], [53, 166, 138, 59, 31], [192, 176, 206, 172, 99], [54, 223, 91, 232, 100], [210, 20, 61, 47, 6], [0, 0, 0, 1], [0, 1]], ![[98, 201, 21, 36, 158], [155, 170, 148, 146, 61], [209, 139, 164, 159, 69], [107, 11, 120, 58, 117], [107, 144, 4, 56, 230], [41, 235, 70, 112, 221], [145, 108, 44, 19, 12], [20, 149, 83, 227, 2]], ![[185, 183, 11, 176, 214], [83, 107, 29, 108, 182], [114, 9, 68, 57, 3], [233, 163, 185, 152, 195], [226, 153, 133, 48, 61], [168, 194, 63, 38, 129], [51, 30, 45, 156, 97], [98, 201, 21, 36, 158]], ![[154, 189, 126, 43, 108], [175, 201, 135, 192, 187], [152, 94, 82, 185, 221], [71, 39, 121, 227, 157], [22, 196, 1, 235, 100], [52, 62, 107, 169, 50], [55, 88, 204, 32, 24], [185, 183, 11, 176, 214]], ![[0, 1], [102, 61, 78, 111, 217], [221, 74, 30, 22, 158], [92, 93, 91, 114, 155], [200, 7, 12, 152, 232], [29, 212, 181, 116, 76], [184, 15, 189, 33, 108], [154, 189, 126, 43, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135, 123, 167, 76], [], [], []]
 b := ![[], [60, 195, 196, 26, 203], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 5
  hpos := by decide
  P := [150, 90, 24, 48, 25, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-39461888712521522, 69590096907944686, 121401081742133636, 594731018368806854, 1219623202413737786]
  a := ![-11, 10, -4, 98, 238]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-163742276815442, 288755588829646, 503738928390596, 2467763561696294, 5060677188438746]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 137, 287, -132, -322]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![13, 137, 287, -132, -322]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![236, 179, 1, 0, 0], ![175, 72, 0, 1, 0], ![183, 8, 0, 0, 1]] where
  M :=![![![13, 137, 287, -132, -322], ![-58, -119, 63, -25, -70], ![-20, -83, -124, 58, 140], ![24, 38, -49, 22, 56], ![-6, 1, 42, -19, -47]]]
  hmulB := by decide  
  f := ![![![-29, 10, -49, 27, 70]], ![![16, -2, 21, -10, -56]], ![![-16, 8, -31, 19, 28]], ![![-15, 7, -28, 16, 28]], ![![-21, 7, -35, 20, 53]]]
  g := ![![![57, -156, 287, -132, -322], ![9, -36, 63, -25, -70], ![-26, 67, -124, 58, 140], ![-10, 27, -49, 22, 56], ![8, -23, 42, -19, -47]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [180, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [209, 250], [0, 1]]
 g := ![![[109, 152], [59, 103], [125], [227, 16], [238, 208], [152, 60], [209, 1]], ![[0, 99], [0, 148], [125], [57, 235], [36, 43], [142, 191], [167, 250]]]
 h' := ![![[209, 250], [173, 34], [138, 75], [53, 171], [81, 4], [250, 31], [30, 78], [0, 1]], ![[0, 1], [0, 217], [0, 176], [150, 80], [164, 247], [203, 220], [17, 173], [209, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [137, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [180, 42, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2246, 2679, 5279, 27324, 60805]
  a := ![-2, 3, -1, 18, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-68355, -13530, 5279, 27324, 60805]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 143, -49, 18, 54]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![67, 143, -49, 18, 54]] 
 ![![251, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![248, 0, 1, 0, 0], ![228, 0, 0, 1, 0], ![121, 0, 0, 0, 1]] where
  M :=![![![67, 143, -49, 18, 54], ![18, 85, 143, -67, -162], ![-28, -49, 46, -24, -60], ![-12, -52, -61, -2, 12], ![10, 29, 14, 1, -1]]]
  hmulB := by decide  
  f := ![![![697, 314, -553, -2473, -9726]], ![![192, 88, -157, -686, -2700]], ![![808, 354, -610, -2835, -11136]], ![![-110, 13, -107, 191, 666]], ![![739, 299, -481, -2514, -9841]]]
  g := ![![![-37, 143, -49, 18, 54], ![-28, 85, 143, -67, -162], ![20, -49, 46, -24, -60], ![72, -52, -61, -2, 12], ![-23, 29, 14, 1, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![351, -146, 638, -286, -726]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![351, -146, 638, -286, -726]] 
 ![![251, 0, 0, 0, 0], ![123, 1, 0, 0, 0], ![182, 0, 1, 0, 0], ![204, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![351, -146, 638, -286, -726], ![-154, 65, -278, 132, 330], ![66, -22, 131, -14, -66], ![-38, 52, 2, 289, 534], ![30, -22, 36, -92, -181]]]
  hmulB := by decide  
  f := ![![![-1499, -4294, -2658, 1306, 3006]], ![![-733, -2105, -1316, 646, 1488]], ![![-1084, -3106, -1925, 946, 2178]], ![![-1218, -3488, -2154, 1057, 2430]], ![![-377, -1080, -670, 330, 761]]]
  g := ![![![25, -146, 638, -286, -726], ![-21, 65, -278, 132, 330], ![-56, -22, 131, -14, -66], ![-396, 52, 2, 289, 534], ![105, -22, 36, -92, -181]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2

def I251N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-183, -1005, -1816, 843, 2046]] i)))

def SI251N3: IdealEqSpanCertificate' Table ![![-183, -1005, -1816, 843, 2046]] 
 ![![251, 0, 0, 0, 0], ![124, 1, 0, 0, 0], ![186, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![69, 0, 0, 0, 1]] where
  M :=![![![-183, -1005, -1816, 843, 2046], ![360, 660, -522, 239, 624], ![146, 599, 753, -203, -570], ![-164, -57, 560, 722, 1164], ![32, -70, -332, -104, -97]]]
  hmulB := by decide  
  f := ![![![-47165, 21745, -91974, 31967, 69114]], ![![-23280, 10682, -45244, 15939, 34812]], ![![-34576, 16281, -68445, 22365, 46014]], ![![-7816, 1477, -8862, 11986, 40548]], ![![-11587, 6495, -26054, 4227, 1205]]]
  g := ![![![1185, -1005, -1816, 843, 2046], ![-136, 660, -522, 239, 624], ![-674, 599, 753, -203, -570], ![-788, -57, 560, 722, 1164], ![319, -70, -332, -104, -97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N3 : Nat.card (O ⧸ I251N3) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N3)

lemma isPrimeI251N3 : Ideal.IsPrime I251N3 := prime_ideal_of_norm_prime hp251.out _ NI251N3
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![13, 137, 287, -132, -322]] ![![67, 143, -49, 18, 54]]
  ![![-6335, -3033, 35700, -15891, -39974]] where
 M := ![![![-6335, -3033, 35700, -15891, -39974]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![-6335, -3033, 35700, -15891, -39974]] ![![351, -146, 638, -286, -726]]
  ![![4335, -4539, 7298, -3237, -8380]] where
 M := ![![![4335, -4539, 7298, -3237, -8380]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI251N2 : IdealMulLeCertificate' Table 
  ![![4335, -4539, 7298, -3237, -8380]] ![![-183, -1005, -1816, 843, 2046]]
  ![![251, 0, 0, 0, 0]] where
 M := ![![![-1099129, -2209804, 961832, -377504, -1077794]]]
 hmul := by decide  
 g := ![![![![-4379, -8804, 3832, -1504, -4294]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1, I251N2, I251N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
    exact isPrimeI251N2
    exact isPrimeI251N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0 ⊙ MulI251N1 ⊙ MulI251N2)


lemma PB953I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB953I5 : PrimesBelowBoundCertificateInterval O 197 251 953 where
  m := 9
  g := ![1, 3, 1, 2, 3, 2, 2, 1, 4]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB953I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
    · exact ![I251N0, I251N1, I251N2, I251N3]
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
    · exact ![44521, 44521, 211]
    · exact ![551473077343]
    · exact ![11697083, 51529]
    · exact ![52441, 52441, 229]
    · exact ![2947295521, 233]
    · exact ![13651919, 57121]
    · exact ![812990017201]
    · exact ![63001, 251, 251, 251]
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
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
      exact NI251N2
      exact NI251N3
  β := ![I211N2, I229N2, I233N1, I251N1, I251N2, I251N3]
  Il := ![[], [I211N2], [], [], [I229N2], [I233N1], [], [], [I251N1, I251N2, I251N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
