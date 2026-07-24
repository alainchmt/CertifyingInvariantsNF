
import IdealArithmetic.Examples.NF5_3_1012500000_1.RI5_3_1012500000_1
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


def P257P0 : CertificateIrreducibleZModOfList' 257 5 2 8 [225, 117, 43, 28, 39, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 24, 176, 231, 108], [12, 132, 235, 134, 73], [157, 101, 89, 213, 216], [226, 256, 14, 193, 117], [0, 1]]
 g := ![![[131, 82, 96, 73, 231], [113, 1, 3, 84], [185, 5, 0, 117], [45, 155, 4, 4], [256, 73, 171, 23], [133, 208, 218, 1], [], []], ![[244, 2, 228, 197, 82, 140, 203, 247], [226, 191, 152, 104], [152, 217, 104, 241], [144, 190, 11, 139], [166, 5, 74, 25], [88, 242, 237, 62], [132, 148, 58, 4], [0, 234, 32, 99]], ![[82, 3, 106, 189, 46, 187, 183, 134], [147, 147, 38, 139], [187, 0, 222, 104], [192, 116, 52, 165], [91, 192, 104, 23], [159, 217, 136, 13], [159, 201, 76, 30], [87, 123, 114, 189]], ![[12, 67, 80, 65, 116, 214, 123, 6], [88, 115, 6, 4], [72, 9, 173, 234], [149, 25, 117, 62], [102, 44, 73, 223], [156, 22, 126, 4], [0, 58, 10, 29], [4, 30, 243, 139]], ![[246, 22, 238, 122, 0, 144, 203, 44], [231, 41, 40, 165], [129, 129, 85, 46], [36, 239, 127, 100], [21, 56, 55, 46], [15, 215, 106, 239], [24, 253, 75, 144], [243, 88, 105, 68]]]
 h' := ![![[80, 24, 176, 231, 108], [52, 210, 195, 62, 152], [88, 136, 153, 20, 37], [74, 61, 110, 96, 84], [144, 103, 230, 217, 255], [144, 90, 51, 151, 58], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[12, 132, 235, 134, 73], [11, 59, 141, 144, 113], [177, 189, 9, 11, 238], [14, 91, 166, 245, 193], [240, 51, 206, 103, 216], [117, 233, 152, 75, 252], [223, 114, 229, 25, 233], [232, 20, 69, 75, 255], [80, 24, 176, 231, 108]], ![[157, 101, 89, 213, 216], [162, 93, 176, 244, 95], [37, 184, 138, 170, 41], [161, 205, 141, 72, 19], [106, 127, 10, 235, 57], [147, 14, 222, 224, 199], [126, 184, 124, 39, 229], [101, 9, 99, 126, 162], [12, 132, 235, 134, 73]], ![[226, 256, 14, 193, 117], [187, 220, 151, 189, 43], [202, 50, 86, 88, 255], [168, 237, 11, 166, 100], [119, 86, 54, 156, 233], [14, 122, 168, 184, 123], [231, 105, 93, 58, 255], [105, 81, 93, 108, 85], [157, 101, 89, 213, 216]], ![[0, 1], [192, 189, 108, 132, 111], [32, 212, 128, 225, 200], [253, 177, 86, 192, 118], [30, 147, 14, 60, 10], [227, 55, 178, 137, 139], [255, 111, 68, 135, 53], [256, 147, 252, 205, 12], [226, 256, 14, 193, 117]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 158, 29, 135], [], [], []]
 b := ![[], [181, 242, 188, 147, 63], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 5
  hpos := by decide
  P := [225, 117, 43, 28, 39, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-163560751863, -413042005866, 138712905010, 509270333910, 45112415330]
  a := ![0, -1, -4, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-636423159, -1607167338, 539738930, 1981596630, 175534690]
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

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![70259, 117429, -37299, 17052, -14132]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![70259, 117429, -37299, 17052, -14132]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![0, 0, 0, 263, 0], ![241, 201, 42, 191, 1]] where
  M :=![![![70259, 117429, -37299, 17052, -14132], ![-84792, -141721, 45008, -20574, 17052], ![102312, 170988, -54331, 24834, -20574], ![-71730, -119877, 38075, -17443, 14426], ![-26322, -43983, 13981, -6384, 5261]]]
  hmulB := by decide  
  f := ![![![-263, -141, 61, -12, 22]], ![![132, 67, -34, 6, -12]], ![![-72, -48, 7, -6, 6]], ![![42, 27, -11, -5, -4]], ![![-121, -66, 23, -11, 9]]]
  g := ![![![13217, 11247, 2115, 10328, -14132], ![-15948, -13571, -2552, -12462, 17052], ![19242, 16374, 3079, 15036, -20574], ![-13492, -11481, -2159, -10543, 14426], ![-4921, -4188, -787, -3845, 5261]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 4 2 8 [218, 243, 237, 159, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [125, 211, 196, 162], [143, 36, 142, 198], [99, 15, 188, 166], [0, 1]]
 g := ![![[32, 12, 255, 35], [144, 174, 112, 23], [196, 81, 9, 124], [127, 221, 64], [76, 193, 132], [83, 161, 33], [1], []], ![[260, 31, 253, 99, 245, 64], [194, 215, 105, 57, 197, 206], [239, 13, 184, 184, 3, 147], [86, 197, 13], [234, 48, 105], [191, 158, 129], [152, 6, 172], [77, 83, 207]], ![[131, 35, 197, 171, 256, 27], [32, 126, 126, 231, 208, 70], [158, 136, 248, 89, 70, 27], [74, 154, 203], [36, 122, 54], [261, 121, 52], [183, 233, 70], [241, 140, 17]], ![[192, 145, 83, 165, 186, 26], [69, 66, 136, 179, 101, 183], [138, 0, 48, 221, 126, 166], [30, 214, 223], [51, 103, 17], [91, 116, 48], [125, 233, 68], [184, 261, 204]]]
 h' := ![![[125, 211, 196, 162], [168, 83, 98, 78], [141, 121, 125, 54], [112, 58, 0, 85], [151, 59, 57, 255], [237, 185, 135, 208], [45, 20, 26, 104], [0, 0, 1], [0, 1]], ![[143, 36, 142, 198], [48, 44, 64, 195], [152, 209, 197, 200], [104, 29, 57, 185], [53, 218, 69, 146], [116, 10, 194, 216], [48, 215, 137, 38], [154, 165, 246, 232], [125, 211, 196, 162]], ![[99, 15, 188, 166], [223, 50, 121, 257], [10, 243, 156, 60], [222, 245, 54, 257], [171, 143, 242, 236], [38, 242, 139, 37], [91, 54, 258, 29], [260, 113, 191, 164], [143, 36, 142, 198]], ![[0, 1], [229, 86, 243, 259], [213, 216, 48, 212], [83, 194, 152, 262], [171, 106, 158, 152], [56, 89, 58, 65], [250, 237, 105, 92], [197, 248, 88, 130], [99, 15, 188, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [181, 31, 99], []]
 b := ![[], [], [68, 252, 193, 131], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 4
  hpos := by decide
  P := [218, 243, 237, 159, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22267142, 94988956, -12050223, -226431313, -34686089]
  a := ![3, -64, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![31869257, 26870315, 5493405, 24329322, -34686089]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 4784350561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 141, -61, 12, -22]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 141, -61, 12, -22]] 
 ![![263, 0, 0, 0, 0], ![72, 1, 0, 0, 0], ![76, 0, 1, 0, 0], ![102, 0, 0, 1, 0], ![139, 0, 0, 0, 1]] where
  M :=![![![263, 141, -61, 12, -22], ![-132, -67, 34, -6, 12], ![72, 48, -7, 6, -6], ![-42, -27, 11, 5, 4], ![-30, -15, 11, 0, 11]]]
  hmulB := by decide  
  f := ![![![-70259, -117429, 37299, -17052, 14132]], ![![-18912, -31609, 10040, -4590, 3804]], ![![-20692, -34584, 10985, -5022, 4162]], ![![-26976, -45087, 14321, -6547, 5426]], ![![-37033, -61896, 19660, -8988, 7449]]]
  g := ![![![-13, 141, -61, 12, -22], ![4, -67, 34, -6, 12], ![-10, 48, -7, 6, -6], ![0, -27, 11, 5, 4], ![-5, -15, 11, 0, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![70259, 117429, -37299, 17052, -14132]] ![![263, 141, -61, 12, -22]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7963, 4258, -1881, 329, -681]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![7963, 4258, -1881, 329, -681]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![137, 65, 18, 1, 0], ![141, 37, 111, 0, 1]] where
  M :=![![![7963, 4258, -1881, 329, -681], ![-4086, -2252, 1010, -15, 329], ![1974, 849, -523, 183, -15], ![-1002, -133, 121, -661, 38], ![-804, 18, 579, 225, -562]]]
  hmulB := by decide  
  f := ![![![4583, 13100, 12695, 6247, 2199]], ![![13194, 37568, 36142, 17847, 6247]], ![![37482, 106899, 103159, 50865, 17847]], ![![8027, 22893, 22092, 10893, 3822]], ![![19803, 56485, 54521, 26880, 9433]]]
  g := ![![![219, 30, 252, 329, -681], ![-180, -50, -131, -15, 329], ![-78, -39, -8, 183, -15], ![313, 154, 29, -661, 38], ![177, 23, 219, 225, -562]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [204, 249, 116, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [247, 127, 249], [175, 141, 20], [0, 1]]
 g := ![![[219, 119, 258], [261, 231], [4, 43, 264], [266, 15, 64], [243, 217], [156, 138], [153, 1], []], ![[65, 169, 85, 119], [262, 211], [94, 203, 79, 231], [198, 207, 36, 151], [134, 79], [264, 11], [165, 244], [168, 131]], ![[153, 258, 194, 149], [208, 36], [195, 130, 170, 121], [191, 205, 38, 93], [176, 268], [241, 118], [86, 258], [128, 131]]]
 h' := ![![[247, 127, 249], [99, 113, 127], [260, 12, 85], [74, 11, 159], [248, 258, 261], [251, 19, 237], [261, 166, 26], [0, 0, 1], [0, 1]], ![[175, 141, 20], [46, 151, 45], [129, 71, 178], [8, 81, 141], [180, 224, 168], [207, 20, 219], [172, 10, 77], [106, 100, 141], [247, 127, 249]], ![[0, 1], [149, 5, 97], [219, 186, 6], [260, 177, 238], [148, 56, 109], [116, 230, 82], [44, 93, 166], [209, 169, 127], [175, 141, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 17], []]
 b := ![[], [7, 40, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [204, 249, 116, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-78354, -190116, 107682, 302036, -9200]
  a := ![1, -3, -2, -1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-149294, -72424, -16014, 302036, -9200]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4583, 13100, 12695, 6247, 2199]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![4583, 13100, 12695, 6247, 2199]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![159, 164, 1, 0, 0], ![13, 259, 0, 1, 0], ![174, 173, 0, 0, 1]] where
  M :=![![![4583, 13100, 12695, 6247, 2199], ![13194, 37568, 36142, 17847, 6247], ![37482, 106899, 103159, 50865, 17847], ![-894, -2585, -2559, -1247, -446], ![32124, 91560, 88251, 43539, 15262]]]
  hmulB := by decide  
  f := ![![![7963, 4258, -1881, 329, -681]], ![![-4086, -2252, 1010, -15, 329]], ![![2223, 1147, -498, 186, -202]], ![![-3553, -1963, 882, -1, 284]], ![![2520, 1306, -565, 204, -231]]]
  g := ![![![-9211, -15120, 12695, 6247, 2199], ![-26217, -43096, 36142, 17847, 6247], ![-74838, -122947, 103159, 50865, 17847], ![1858, 3038, -2559, -1247, -446], ![-64020, -105199, 88251, 43539, 15262]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P1 : CertificateIrreducibleZModOfList' 269 2 2 8 [4, 243, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 268], [0, 1]]
 g := ![![[128, 202], [214], [248, 144], [14, 67], [263], [239], [138], [1]], ![[0, 67], [214], [226, 125], [142, 202], [263], [239], [138], [1]]]
 h' := ![![[26, 268], [13, 134], [84, 131], [213, 12], [67, 228], [124, 97], [2, 152], [265, 26], [0, 1]], ![[0, 1], [0, 135], [262, 138], [256, 257], [77, 41], [225, 172], [188, 117], [134, 243], [26, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [194]]
 b := ![[], [84, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N1 : CertifiedPrimeIdeal' SI269N1 269 where
  n := 2
  hpos := by decide
  P := [4, 243, 1]
  hirr := P269P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2870, 10707, -1598, -9165, 3171]
  a := ![1, 19, 3, -1, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-653, 7799, -1598, -9165, 3171]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N1 B_one_repr
lemma NI269N1 : Nat.card (O ⧸ I269N1) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![7963, 4258, -1881, 329, -681]] ![![4583, 13100, 12695, 6247, 2199]]
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

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1531, 4855, 5652, 2559, 1027]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![1531, 4855, 5652, 2559, 1027]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![0, 0, 0, 271, 0], ![92, 105, 72, 112, 1]] where
  M :=![![![1531, 4855, 5652, 2559, 1027], ![6162, 16936, 15144, 7749, 2559], ![15354, 44547, 44383, 21555, 7749], ![72, -342, -1334, -419, -282], ![13878, 39363, 37584, 18627, 6484]]]
  hmulB := by decide  
  f := ![![![25, 11, -6, 3, -1]], ![![-6, 10, -6, -27, 3]], ![![18, 39, 7, -9, -27]], ![![-36, -84, 26, 97, 12]], ![![-4, -17, 8, 28, -1]]]
  g := ![![![-343, -380, -252, -415, 1027], ![-846, -929, -624, -1029, 2559], ![-2574, -2838, -1895, -3123, 7749], ![96, 108, 70, 115, -282], ![-2150, -2367, -1584, -2611, 6484]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 4 2 8 [11, 200, 102, 39, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [212, 134, 123, 237], [205, 254, 117, 229], [86, 153, 31, 76], [0, 1]]
 g := ![![[30, 9, 89, 176], [0, 159, 141, 34], [205, 230, 38, 250], [154, 127, 39, 55], [199, 215, 119], [54, 127, 166], [1], []], ![[94, 50, 258, 200, 94, 73], [70, 242, 84, 123, 20, 131], [253, 85, 77, 87, 83, 201], [69, 154, 99, 199, 166, 133], [62, 88, 163], [126, 11, 70], [209, 221, 141], [239, 210, 72]], ![[88, 83, 32, 186, 27, 85], [193, 256, 214, 47, 266, 72], [119, 190, 54, 232, 253, 238], [28, 44, 252, 173, 15, 7], [209, 254, 45], [42, 74, 241], [256, 122, 83], [199, 237, 138]], ![[262, 42, 248, 244, 133, 12], [112, 91, 210, 22, 106, 159], [194, 59, 57, 139, 159, 227], [179, 172, 112, 154, 77, 24], [36, 149, 35], [28, 14, 114], [37, 95, 100], [88, 42, 85]]]
 h' := ![![[212, 134, 123, 237], [0, 129, 46, 161], [184, 118, 88, 247], [203, 126, 222, 149], [133, 266, 139, 41], [69, 62, 25, 173], [260, 71, 169, 232], [0, 0, 1], [0, 1]], ![[205, 254, 117, 229], [122, 224, 245, 59], [103, 63, 106, 265], [12, 48, 4, 254], [36, 94, 85, 205], [110, 108, 116, 71], [35, 251, 191, 137], [39, 202, 228, 236], [212, 134, 123, 237]], ![[86, 153, 31, 76], [53, 33, 226, 61], [95, 267, 264, 120], [242, 58, 194, 63], [176, 241, 100, 172], [265, 261, 69, 99], [166, 142, 18, 90], [270, 216, 181, 25], [205, 254, 117, 229]], ![[0, 1], [175, 156, 25, 261], [157, 94, 84, 181], [41, 39, 122, 76], [53, 212, 218, 124], [125, 111, 61, 199], [220, 78, 164, 83], [195, 124, 132, 10], [86, 153, 31, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [76, 257, 69], []]
 b := ![[], [], [181, 39, 19, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 4
  hpos := by decide
  P := [11, 200, 102, 39, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![958975093, 2382207132, -919089800, -3139830868, -129027358]
  a := ![-1, 0, -2, 2, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![47341299, 58782582, 30888856, 41738868, -129027358]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 5393580481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 11, -6, 3, -1]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![25, 11, -6, 3, -1]] 
 ![![271, 0, 0, 0, 0], ![159, 1, 0, 0, 0], ![193, 0, 1, 0, 0], ![209, 0, 0, 1, 0], ![109, 0, 0, 0, 1]] where
  M :=![![![25, 11, -6, 3, -1], ![-6, 10, -6, -27, 3], ![18, 39, 7, -9, -27], ![-36, -84, 26, 97, 12], ![-18, -69, -66, -69, 106]]]
  hmulB := by decide  
  f := ![![![1531, 4855, 5652, 2559, 1027]], ![![921, 2911, 3372, 1530, 612]], ![![1147, 3622, 4189, 1902, 760]], ![![1181, 3743, 4354, 1972, 791]], ![![667, 2098, 2412, 1098, 437]]]
  g := ![![![-4, 11, -6, 3, -1], ![18, 10, -6, -27, 3], ![-10, 39, 7, -9, -27], ![-49, -84, 26, 97, 12], ![98, -69, -66, -69, 106]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![1531, 4855, 5652, 2559, 1027]] ![![25, 11, -6, 3, -1]]
  ![![271, 0, 0, 0, 0]] where
 M := ![![![271, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-179, -209, 347, 42, 88]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![-179, -209, 347, 42, 88]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![66, 145, 1, 0, 0], ![34, 220, 0, 1, 0], ![52, 240, 0, 0, 1]] where
  M :=![![![-179, -209, 347, 42, 88], ![528, 1141, 438, 372, 42], ![252, 1158, 1915, 756, 372], ![246, 393, -181, 43, -60], ![630, 1683, 1419, 750, 235]]]
  hmulB := by decide  
  f := ![![![1741, 935, -419, 54, -142]], ![![-852, -389, 192, -120, 54]], ![![-30, 19, 1, -48, -6]], ![![-464, -195, 101, -89, 26]], ![![-410, -157, 85, -102, 21]]]
  g := ![![![-105, -292, 347, 42, 88], ![-156, -557, 438, 372, 42], ![-618, -1921, 1915, 756, 372], ![50, 114, -181, 43, -60], ![-472, -1536, 1419, 750, 235]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 2 2 8 [270, 208, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 276], [0, 1]]
 g := ![![[89, 79], [215], [270, 41], [270], [98, 229], [203], [52], [1]], ![[0, 198], [215], [52, 236], [270], [110, 48], [203], [52], [1]]]
 h' := ![![[69, 276], [28, 112], [228, 40], [201, 128], [132, 230], [250, 101], [136, 122], [7, 69], [0, 1]], ![[0, 1], [0, 165], [218, 237], [169, 149], [213, 47], [17, 176], [244, 155], [59, 208], [69, 276]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [180]]
 b := ![[], [219, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 2
  hpos := by decide
  P := [270, 208, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-570, -2288, -552, 376, 284]
  a := ![0, 0, -6, -10, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![30, -264, -552, 376, 284]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 76729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3431, 1842, -814, 150, -292]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![3431, 1842, -814, 150, -292]] 
 ![![277, 0, 0, 0, 0], ![198, 1, 0, 0, 0], ![130, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![3431, 1842, -814, 150, -292], ![-1752, -949, 418, -78, 150], ![900, 498, -217, 42, -78], ![-528, -294, 128, -25, 46], ![-408, -222, 98, -18, 35]]]
  hmulB := by decide  
  f := ![![![59, 150, 18, -78, -8]], ![![42, 107, 14, -54, -6]], ![![26, 66, 11, -30, -2]], ![![19, 48, 2, -31, -2]], ![![23, 60, 4, -36, -9]]]
  g := ![![![-887, 1842, -814, 150, -292], ![458, -949, 418, -78, 150], ![-242, 498, -217, 42, -78], ![143, -294, 128, -25, 46], ![107, -222, 98, -18, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1

def I277N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 108, -37, -135, -9]] i)))

def SI277N2: IdealEqSpanCertificate' Table ![![43, 108, -37, -135, -9]] 
 ![![277, 0, 0, 0, 0], ![215, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![242, 0, 0, 1, 0], ![252, 0, 0, 0, 1]] where
  M :=![![![43, 108, -37, -135, -9], ![-54, -92, 168, 345, -135], ![-810, -2079, 607, 2403, 345], ![750, 1767, -977, -2831, 228], ![2808, 7392, -1569, -7563, -1802]]]
  hmulB := by decide  
  f := ![![![421759, 763434, -239033, 112635, -90813]], ![![325391, 589162, -184459, 86928, -70080]], ![![54208, 97839, -30649, 14427, -11643]], ![![366752, 664071, -207911, 97981, -78990]], ![![383076, 693474, -217125, 102315, -82490]]]
  g := ![![![47, 108, -37, -135, -9], ![-128, -92, 168, 345, -135], ![-877, -2079, 607, 2403, 345], ![1017, 1767, -977, -2831, 228], ![2712, 7392, -1569, -7563, -1802]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N2 : Nat.card (O ⧸ I277N2) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N2)

lemma isPrimeI277N2 : Ideal.IsPrime I277N2 := prime_ideal_of_norm_prime hp277.out _ NI277N2

def I277N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-139, -125, 46, -15, 17]] i)))

def SI277N3: IdealEqSpanCertificate' Table ![![-139, -125, 46, -15, 17]] 
 ![![277, 0, 0, 0, 0], ![273, 1, 0, 0, 0], ![261, 0, 1, 0, 0], ![182, 0, 0, 1, 0], ![150, 0, 0, 0, 1]] where
  M :=![![![-139, -125, 46, -15, 17], ![102, 116, -40, 15, -15], ![-90, -123, 41, -15, 15], ![60, 84, -28, 11, -10], ![30, 39, -14, -3, -4]]]
  hmulB := by decide  
  f := ![![![509, 1469, 1432, 711, 247]], ![![507, 1463, 1426, 708, 246]], ![![495, 1428, 1391, 690, 240]], ![![334, 964, 940, 467, 162]], ![![288, 831, 812, 405, 140]]]
  g := ![![![80, -125, 46, -15, 17], ![-78, 116, -40, 15, -15], ![84, -123, 41, -15, 15], ![-58, 84, -28, 11, -10], ![-21, 39, -14, -3, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N3 : Nat.card (O ⧸ I277N3) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N3)

lemma isPrimeI277N3 : Ideal.IsPrime I277N3 := prime_ideal_of_norm_prime hp277.out _ NI277N3
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![-179, -209, 347, 42, 88]] ![![3431, 1842, -814, 150, -292]]
  ![![6239, 9545, -2955, 1392, -1136]] where
 M := ![![![6239, 9545, -2955, 1392, -1136]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI277N1 : IdealMulLeCertificate' Table 
  ![![6239, 9545, -2955, 1392, -1136]] ![![43, 108, -37, -135, -9]]
  ![![509, 1469, 1432, 711, 247]] where
 M := ![![![509, 1469, 1432, 711, 247]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI277N2 : IdealMulLeCertificate' Table 
  ![![509, 1469, 1432, 711, 247]] ![![-139, -125, 46, -15, 17]]
  ![![277, 0, 0, 0, 0]] where
 M := ![![![277, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC277 : ContainsPrimesAboveP 277 ![I277N0, I277N1, I277N2, I277N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
    exact isPrimeI277N1
    exact isPrimeI277N2
    exact isPrimeI277N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 277 (by decide) (𝕀 ⊙ MulI277N0 ⊙ MulI277N1 ⊙ MulI277N2)
instance hp281 : Fact (Nat.Prime 281) := {out := by norm_num}

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3973, -6644, 2109, -953, 801]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![-3973, -6644, 2109, -953, 801]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![148, 248, 1, 0, 0], ![178, 47, 0, 1, 0], ![189, 151, 0, 0, 1]] where
  M :=![![![-3973, -6644, 2109, -953, 801], ![4806, 8042, -2568, 1095, -953], ![-5718, -9489, 3055, -1539, 1095], ![3954, 6529, -2055, 1309, -804], ![1320, 1992, -839, 603, -8]]]
  hmulB := by decide  
  f := ![![![-14741, -15078, -5811, -4723, -495]], ![![-2970, -22166, -25808, -11787, -4723]], ![![-10486, -27767, -26083, -13013, -4471]], ![![-9826, -13249, -7993, -4960, -1103]], ![![-11583, -22270, -17990, -9615, -2908]]]
  g := ![![![-1060, -2156, 2109, -953, 801], ![1317, 2624, -2568, 1095, -953], ![-1391, -3061, 3055, -1539, 1095], ![808, 2050, -2055, 1309, -804], ![70, 651, -839, 603, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 2 2 8 [50, 277, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 280], [0, 1]]
 g := ![![[191, 163], [4], [7], [100, 238], [18, 155], [215], [16], [1]], ![[0, 118], [4], [7], [209, 43], [76, 126], [215], [16], [1]]]
 h' := ![![[4, 280], [109, 43], [204, 279], [58, 179], [224, 111], [124, 163], [14, 226], [231, 4], [0, 1]], ![[0, 1], [0, 238], [196, 2], [212, 102], [106, 170], [214, 118], [75, 55], [247, 277], [4, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [226, 168]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 2
  hpos := by decide
  P := [50, 277, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5158, 2467, -3076, -5887, 99]
  a := ![13, -1, -2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5301, 3655, -3076, -5887, 99]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 78961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85, 217, 159, 84, 26]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![85, 217, 159, 84, 26]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![184, 99, 1, 0, 0], ![244, 221, 0, 1, 0], ![154, 202, 0, 0, 1]] where
  M :=![![![85, 217, 159, 84, 26], ![156, 475, 506, 234, 84], ![504, 1416, 1423, 822, 234], ![-18, -39, -57, -101, 20], ![570, 1581, 1063, 120, 193]]]
  hmulB := by decide  
  f := ![![![-6250135, -3333215, 1477157, -269316, 529664]], ![![3177984, 1694825, -751084, 136938, -269316]], ![![-2978720, -1588561, 703991, -128352, 252430]], ![![-2924390, -1559588, 691151, -126011, 247826]], ![![-1138184, -606999, 268999, -49044, 96455]]]
  g := ![![![-191, -140, 159, 84, 26], ![-580, -421, 506, 234, 84], ![-1772, -1311, 1423, 822, 234], ![114, 85, -57, -101, 20], ![-904, -602, 1063, 120, 193]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P1 : CertificateIrreducibleZModOfList' 281 2 2 8 [61, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [179, 280], [0, 1]]
 g := ![![[232, 78], [137], [201], [149, 280], [78, 141], [126], [7], [1]], ![[144, 203], [137], [201], [251, 1], [27, 140], [126], [7], [1]]]
 h' := ![![[179, 280], [151, 42], [239, 74], [184, 117], [19, 53], [84, 66], [203, 209], [220, 179], [0, 1]], ![[0, 1], [82, 239], [278, 207], [52, 164], [233, 228], [96, 215], [241, 72], [227, 102], [179, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [36, 166]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N1 : CertifiedPrimeIdeal' SI281N1 281 where
  n := 2
  hpos := by decide
  P := [61, 102, 1]
  hirr := P281P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![62, -92, -117, -644, 365]
  a := ![-1, -3, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![436, 285, -117, -644, 365]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N1 B_one_repr
lemma NI281N1 : Nat.card (O ⧸ I281N1) = 78961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N1

def I281N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14861, -24838, 7889, -3607, 2989]] i)))

def SI281N2: IdealEqSpanCertificate' Table ![![-14861, -24838, 7889, -3607, 2989]] 
 ![![281, 0, 0, 0, 0], ![215, 1, 0, 0, 0], ![140, 0, 1, 0, 0], ![65, 0, 0, 1, 0], ![129, 0, 0, 0, 1]] where
  M :=![![![-14861, -24838, 7889, -3607, 2989], ![17934, 29974, -9520, 4353, -3607], ![-21642, -36171, 11489, -5253, 4353], ![15174, 25361, -8055, 3683, -3052], ![5568, 9306, -2955, 1353, -1120]]]
  hmulB := by decide  
  f := ![![![3347, 1836, -767, 115, -275]], ![![2555, 1402, -585, 88, -210]], ![![1670, 915, -381, 61, -137]], ![![773, 425, -178, 24, -63]], ![![1539, 852, -354, 42, -127]]]
  g := ![![![14483, -24838, 7889, -3607, 2989], ![-17478, 29974, -9520, 4353, -3607], ![21091, -36171, 11489, -5253, 4353], ![-14788, 25361, -8055, 3683, -3052], ![-5427, 9306, -2955, 1353, -1120]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N2 : Nat.card (O ⧸ I281N2) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N2)

lemma isPrimeI281N2 : Ideal.IsPrime I281N2 := prime_ideal_of_norm_prime hp281.out _ NI281N2
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![-3973, -6644, 2109, -953, 801]] ![![85, 217, 159, 84, 26]]
  ![![162491, 271851, -86680, 37543, -32355]] where
 M := ![![![162491, 271851, -86680, 37543, -32355]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI281N1 : IdealMulLeCertificate' Table 
  ![![162491, 271851, -86680, 37543, -32355]] ![![-14861, -24838, 7889, -3607, 2989]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![4726050485, 7898845089, -2508796381, 1147086960, -950542634]]]
 hmul := by decide  
 g := ![![![![16818685, 28109769, -8928101, 4082160, -3382714]]]]
 hle2 := by decide  


def PBC281 : ContainsPrimesAboveP 281 ![I281N0, I281N1, I281N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI281N0
    exact isPrimeI281N1
    exact isPrimeI281N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 281 (by decide) (𝕀 ⊙ MulI281N0 ⊙ MulI281N1)
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


def P283P0 : CertificateIrreducibleZModOfList' 283 5 2 8 [208, 227, 35, 28, 28, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [155, 169, 92, 116, 165], [238, 213, 193, 92, 159], [42, 28, 14, 172, 24], [103, 155, 267, 186, 218], [0, 1]]
 g := ![![[153, 40, 31, 135, 93], [169, 282, 274, 182, 151], [12, 218, 168, 230], [144, 237, 141, 146, 168], [6, 261, 15, 275, 240], [240, 190, 255, 1], [], []], ![[214, 108, 79, 282, 43, 21, 138, 78], [121, 0, 87, 28, 194, 257, 200, 137], [102, 151, 196, 74], [171, 228, 44, 183, 224, 125, 116, 127], [202, 17, 184, 282, 31, 36, 157, 62], [159, 239, 222, 74], [191, 104, 27, 51], [8, 191, 177, 57]], ![[148, 253, 270, 277, 101, 275, 242, 64], [69, 182, 182, 110, 118, 191, 183, 15], [82, 233, 243, 9], [47, 140, 223, 107, 229, 58, 138, 176], [129, 184, 187, 234, 124, 129, 135, 62], [203, 85, 77, 41], [268, 29, 29, 136], [174, 85, 22, 94]], ![[3, 267, 169, 175, 105, 152, 102, 116], [201, 224, 8, 47, 128, 215, 145, 93], [167, 221, 158, 29], [275, 79, 93, 64, 175, 237, 134, 77], [217, 148, 127, 3, 186, 263, 31, 103], [217, 205, 274, 233], [220, 274, 237, 176], [175, 220, 52, 10]], ![[253, 48, 54, 135, 218, 171, 237, 143], [68, 125, 15, 4, 141, 233, 251, 13], [169, 211, 175, 38], [165, 171, 243, 25, 221, 187, 153, 97], [13, 66, 154, 253, 10, 259, 30, 99], [30, 166, 264, 266], [77, 41, 99, 9], [46, 152, 152, 263]]]
 h' := ![![[155, 169, 92, 116, 165], [223, 120, 154, 27, 35], [186, 140, 54, 150, 43], [46, 241, 67, 198, 71], [167, 193, 200, 1, 161], [171, 239, 140, 136, 33], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[238, 213, 193, 92, 159], [200, 109, 139, 105, 269], [216, 197, 134, 204, 232], [168, 24, 92, 56, 91], [27, 138, 245, 163, 80], [13, 171, 143, 82, 166], [191, 271, 93, 137, 91], [4, 92, 117, 188, 253], [155, 169, 92, 116, 165]], ![[42, 28, 14, 172, 24], [162, 92, 270, 281, 277], [161, 5, 229, 169, 130], [246, 214, 120, 59, 280], [232, 163, 237, 94, 209], [73, 12, 205, 261, 78], [123, 5, 19, 262, 18], [76, 62, 19, 227, 226], [238, 213, 193, 92, 159]], ![[103, 155, 267, 186, 218], [30, 250, 142, 238, 202], [236, 24, 169, 107, 26], [27, 123, 132, 50, 38], [207, 144, 135, 248, 204], [150, 161, 177, 70, 64], [17, 144, 75, 123, 214], [173, 69, 169, 68, 90], [42, 28, 14, 172, 24]], ![[0, 1], [107, 278, 144, 198, 66], [53, 200, 263, 219, 135], [148, 247, 155, 203, 86], [87, 211, 32, 60, 195], [49, 266, 184, 17, 225], [189, 146, 96, 44, 242], [192, 60, 260, 83, 280], [103, 155, 267, 186, 218]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 164, 105, 244], [], [], []]
 b := ![[], [159, 143, 111, 52, 98], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 5
  hpos := by decide
  P := [208, 227, 35, 28, 28, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2021178359, -4687423522, 2866951593, 7959283874, -845260721]
  a := ![3, 0, 3, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7141973, -16563334, 10130571, 28124678, -2986787]
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

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 153, -98, -213, 33]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![89, 153, -98, -213, 33]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![0, 0, 0, 293, 0], ![127, 271, 219, 180, 1]] where
  M :=![![![89, 153, -98, -213, 33], ![198, 584, -60, -543, -213], ![-1278, -2997, 1799, 5103, -543], ![96, -72, -988, -1675, 1122], ![5742, 13713, -7014, -21021, 1148]]]
  hmulB := by decide  
  f := ![![![49, 63, 28, 21, 3]], ![![18, 94, 114, 51, 21]], ![![126, 333, 301, 153, 51]], ![![-12, -18, -4, -5, 0]], ![![125, 353, 341, 168, 59]]]
  g := ![![![-14, -30, -25, -21, 33], ![93, 199, 159, 129, -213], ![231, 492, 412, 351, -543], ![-486, -1038, -842, -695, 1122], ![-478, -1015, -882, -777, 1148]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 4 2 8 [127, 80, 34, 142, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [250, 20, 270, 284], [117, 218, 245, 139], [77, 54, 71, 163], [0, 1]]
 g := ![![[118, 225, 76, 150], [154, 3, 84], [129, 119, 229, 277], [91, 240, 189], [198, 214, 235], [201, 154, 188, 240], [1], []], ![[68, 171, 18, 207, 270, 160], [254, 150, 148], [212, 202, 79, 95, 126, 24], [166, 157, 16], [111, 193, 100], [67, 192, 233, 46, 84, 71], [86, 37, 276], [259, 46, 81]], ![[35, 60, 61, 131, 57, 20], [19, 263, 225], [89, 287, 123, 185, 157, 249], [269, 146, 202], [188, 164, 54], [199, 258, 70, 86, 274, 79], [236, 256, 189], [237, 204, 276]], ![[2, 94, 192, 98, 285, 264], [121, 117, 254], [57, 247, 122, 110, 105, 45], [178, 168, 107], [17, 117, 278], [221, 9, 77, 4, 274, 163], [186, 151, 287], [200, 162, 199]]]
 h' := ![![[250, 20, 270, 284], [112, 51, 97, 83], [25, 173, 113, 233], [81, 2, 155, 259], [176, 59, 43, 90], [257, 122, 144, 198], [166, 213, 259, 151], [0, 0, 1], [0, 1]], ![[117, 218, 245, 139], [216, 176, 151, 261], [87, 5, 96, 272], [40, 159, 223, 55], [57, 154, 267, 4], [26, 76, 119, 10], [115, 224, 64, 146], [14, 139, 115, 154], [250, 20, 270, 284]], ![[77, 54, 71, 163], [87, 69, 258, 238], [50, 262, 185, 15], [202, 223, 181, 233], [60, 177, 118, 219], [221, 61, 141, 167], [211, 212, 278, 290], [291, 284, 9, 203], [117, 218, 245, 139]], ![[0, 1], [78, 290, 80, 4], [76, 146, 192, 66], [238, 202, 27, 39], [24, 196, 158, 273], [194, 34, 182, 211], [220, 230, 278, 292], [160, 163, 168, 229], [77, 54, 71, 163]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [76, 127, 277], []]
 b := ![[], [], [203, 210, 48, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 4
  hpos := by decide
  P := [127, 80, 34, 142, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![167729514, 408790008, -181028521, -578893116, 4967339]
  a := ![1, 1, 1, -1, 4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1580623, -3199177, -4330634, -5027352, 4967339]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 7370050801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -63, -28, -21, -3]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![-49, -63, -28, -21, -3]] 
 ![![293, 0, 0, 0, 0], ![113, 1, 0, 0, 0], ![123, 0, 1, 0, 0], ![259, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![-49, -63, -28, -21, -3], ![-18, -94, -114, -51, -21], ![-126, -333, -301, -153, -51], ![12, 18, 4, 5, 0], ![-90, -267, -264, -129, -46]]]
  hmulB := by decide  
  f := ![![![-89, -153, 98, 213, -33]], ![![-35, -61, 38, 84, -12]], ![![-33, -54, 35, 72, -12]], ![![-79, -135, 90, 194, -33]], ![![-36, -75, 42, 111, -10]]]
  g := ![![![55, -63, -28, -21, -3], ![133, -94, -114, -51, -21], ![399, -333, -301, -153, -51], ![-13, 18, 4, 5, 0], ![336, -267, -264, -129, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N1 : Nat.card (O ⧸ I293N1) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N1)

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := prime_ideal_of_norm_prime hp293.out _ NI293N1
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![89, 153, -98, -213, 33]] ![![-49, -63, -28, -21, -3]]
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


def P307P0 : CertificateIrreducibleZModOfList' 307 5 2 8 [280, 20, 228, 64, 257, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [276, 172, 194, 301, 152], [242, 208, 150, 191, 71], [259, 170, 104, 54, 134], [194, 63, 166, 68, 257], [0, 1]]
 g := ![![[249, 68, 130, 90, 187], [117, 214, 282, 109, 96], [229, 223, 106, 240], [128, 266, 199, 90], [42, 288, 103, 255, 6], [245, 177, 287, 50, 1], [], []], ![[205, 277, 203, 38, 206, 72, 75, 35], [132, 208, 213, 111, 3, 137, 75, 239], [48, 182, 214, 225], [256, 110, 236, 105], [213, 299, 36, 120, 26, 11, 170, 221], [65, 286, 221, 165, 143, 164, 43, 210], [207, 14, 211, 64], [57, 2, 284, 79]], ![[257, 247, 297, 157, 27, 198, 89, 286], [112, 36, 135, 28, 39, 292, 256, 286], [98, 122, 188, 53], [14, 146, 192, 176], [17, 242, 166, 53, 75, 152, 74, 1], [141, 302, 149, 243, 288, 233, 150, 233], [80, 187, 249, 209], [279, 22, 109, 129]], ![[3, 134, 4, 119, 303, 285, 231, 39], [139, 233, 89, 152, 84, 96, 168, 99], [93, 90, 154, 278], [166, 134, 203, 81], [199, 224, 147, 172, 30, 136, 251, 100], [238, 65, 171, 10, 62, 22, 282, 209], [52, 172, 41, 219], [1, 159, 175, 150]], ![[132, 105, 30, 262, 123, 66, 130, 119], [199, 135, 208, 178, 176, 251, 104, 225], [106, 92, 204, 150], [51, 282, 222, 115], [289, 174, 235, 244, 88, 219, 80, 104], [215, 134, 190, 118, 49, 243, 293, 187], [131, 66, 253, 269], [274, 194, 5, 44]]]
 h' := ![![[276, 172, 194, 301, 152], [89, 32, 158, 290, 164], [187, 30, 193, 135, 77], [12, 261, 256, 247, 94], [213, 162, 207, 208, 107], [168, 186, 232, 53, 211], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[242, 208, 150, 191, 71], [137, 178, 258, 301, 155], [283, 234, 159, 279, 231], [198, 279, 223, 286, 292], [31, 262, 33, 4, 64], [224, 270, 116, 142, 55], [157, 205, 161, 223, 144], [44, 223, 215, 206, 299], [276, 172, 194, 301, 152]], ![[259, 170, 104, 54, 134], [134, 163, 207, 193, 289], [74, 213, 20, 133, 289], [240, 281, 119, 208, 214], [294, 71, 130, 178, 100], [158, 120, 243, 135, 245], [186, 153, 281, 58, 146], [92, 209, 109, 37, 165], [242, 208, 150, 191, 71]], ![[194, 63, 166, 68, 257], [36, 210, 227, 58, 199], [83, 252, 181, 217, 179], [86, 16, 243, 111, 187], [165, 228, 35, 8, 9], [252, 211, 157, 225, 249], [144, 0, 72, 33, 271], [182, 233, 278, 243, 126], [259, 170, 104, 54, 134]], ![[0, 1], [181, 31, 71, 79, 114], [32, 192, 61, 157, 145], [94, 84, 80, 69, 134], [258, 198, 209, 216, 27], [264, 134, 173, 59, 161], [282, 256, 100, 300, 52], [212, 256, 11, 128, 24], [194, 63, 166, 68, 257]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 287, 62, 280], [], [], []]
 b := ![[], [236, 263, 6, 297, 289], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 5
  hpos := by decide
  P := [280, 20, 228, 64, 257, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-247442, -536943, 990689, 2086986, -833198]
  a := ![4, 0, 0, 1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-806, -1749, 3227, 6798, -2714]
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



lemma PB1556I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB1556I6 : PrimesBelowBoundCertificateInterval O 251 307 1556 where
  m := 9
  g := ![1, 2, 2, 2, 4, 3, 1, 2, 1]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB1556I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0]
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1]
    · exact ![I271N0, I271N1]
    · exact ![I277N0, I277N1, I277N2, I277N3]
    · exact ![I281N0, I281N1, I281N2]
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
    · exact ![1121154893057]
    · exact ![4784350561, 263]
    · exact ![19465109, 72361]
    · exact ![5393580481, 271]
    · exact ![76729, 277, 277, 277]
    · exact ![78961, 78961, 281]
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
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
      exact NI277N1
      exact NI277N2
      exact NI277N3
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
      exact NI281N1
      exact NI281N2
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
  β := ![I263N1, I271N1, I277N1, I277N2, I277N3, I281N2, I293N1]
  Il := ![[], [I263N1], [], [I271N1], [I277N1, I277N2, I277N3], [I281N2], [], [I293N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
