
import IdealArithmetic.Examples.NF5_3_405000000_1.RI5_3_405000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25541, -65323, 11161, -2514, 8354]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![25541, -65323, 11161, -2514, 8354]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![114, 32, 1, 0, 0], ![207, 118, 0, 1, 0], ![254, 157, 0, 0, 1]] where
  M :=![![![25541, -65323, 11161, -2514, 8354], ![5028, -12903, 2321, -519, 1624], ![1038, -2506, 156, 111, 134], ![-222, 724, -967, -334, 934], ![6356, -16750, 3901, -1193, 2465]]]
  hmulB := by decide  
  f := ![![![60759, -381009, 59325, -13730, 47080]], ![![27460, -155021, 1521, -7375, 11780]], ![![30428, -188444, 26228, -7037, 22270]], ![![61603, -377737, 47538, -14504, 42998]], ![![76878, -471171, 58988, -18116, 53533]]]
  g := ![![![-11083, -5593, 11161, -2514, 8354], ![-2197, -1093, 2321, -519, 1624], ![-287, -162, 156, 111, 134], ![-226, -294, -967, -334, 934], ![-3181, -1509, 3901, -1193, 2465]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [171, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [194, 256], [0, 1]]
 g := ![![[68, 52], [16], [46], [141], [144], [13], [114], [1]], ![[133, 205], [16], [46], [141], [144], [13], [114], [1]]]
 h' := ![![[194, 256], [117, 201], [119, 4], [77, 139], [162, 150], [194, 245], [238, 229], [86, 194], [0, 1]], ![[0, 1], [47, 56], [124, 253], [58, 118], [221, 107], [179, 12], [203, 28], [200, 63], [194, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [202]]
 b := ![[], [226, 101]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [171, 63, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1253, -8887, 15635, -3134, 276]
  a := ![5, -6, -8, 4, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4679, -711, 15635, -3134, 276]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 40, -84, -8, -30]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![3, 40, -84, -8, -30]] 
 ![![257, 0, 0, 0, 0], ![65, 1, 0, 0, 0], ![144, 0, 1, 0, 0], ![149, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![3, 40, -84, -8, -30], ![16, 107, -254, -8, -108], ![16, 432, -889, -22, -264], ![44, 1028, -2010, -317, -660], ![108, 446, -1146, -104, -599]]]
  hmulB := by decide  
  f := ![![![474019, -2886316, 516152, -99064, 378330]], ![![120659, -734817, 131406, -25220, 96318]], ![![265928, -1619320, 289579, -55578, 212256]], ![![274963, -1674296, 299410, -57465, 219462]], ![![22384, -136234, 24362, -4676, 17857]]]
  g := ![![![43, 40, -84, -8, -30], ![125, 107, -254, -8, -108], ![414, 432, -889, -22, -264], ![1081, 1028, -2010, -317, -660], ![618, 446, -1146, -104, -599]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1

def I257N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2181, -5578, 954, -214, 712]] i)))

def SI257N2: IdealEqSpanCertificate' Table ![![2181, -5578, 954, -214, 712]] 
 ![![257, 0, 0, 0, 0], ![192, 1, 0, 0, 0], ![144, 0, 1, 0, 0], ![108, 0, 0, 1, 0], ![213, 0, 0, 0, 1]] where
  M :=![![![2181, -5578, 954, -214, 712], ![428, -1095, 188, -42, 140], ![84, -216, 39, -8, 28], ![16, -44, 12, -1, 8], ![548, -1404, 244, -54, 181]]]
  hmulB := by decide  
  f := ![![![-1875, 11978, -2142, 414, -1576]], ![![-1404, 8969, -1604, 310, -1180]], ![![-1052, 6720, -1201, 232, -884]], ![![-788, 5036, -900, 175, -664]], ![![-1555, 9934, -1778, 344, -1307]]]
  g := ![![![3141, -5578, 954, -214, 712], ![616, -1095, 188, -42, 140], ![120, -216, 39, -8, 28], ![20, -44, 12, -1, 8], ![787, -1404, 244, -54, 181]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N2 : Nat.card (O ⧸ I257N2) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N2)

lemma isPrimeI257N2 : Ideal.IsPrime I257N2 := prime_ideal_of_norm_prime hp257.out _ NI257N2

def I257N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 7, -9, -4, 0]] i)))

def SI257N3: IdealEqSpanCertificate' Table ![![-1, 7, -9, -4, 0]] 
 ![![257, 0, 0, 0, 0], ![225, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![128, 0, 0, 1, 0], ![134, 0, 0, 0, 1]] where
  M :=![![![-1, 7, -9, -4, 0], ![8, -9, -5, -1, -24], ![2, 102, -228, 45, -54], ![-90, 308, -249, -210, 162], ![36, -136, 219, -119, -67]]]
  hmulB := by decide  
  f := ![![![-161715, 496389, -85997, 18468, -63846]], ![![-141723, 435090, -75378, 16187, -55962]], ![![-2554, 7882, -1366, 293, -1014]], ![![-80554, 247284, -42841, 9200, -31806]], ![![-84466, 259236, -44911, 9645, -33343]]]
  g := ![![![-4, 7, -9, -4, 0], ![21, -9, -5, -1, -24], ![-80, 102, -228, 45, -54], ![-246, 308, -249, -210, 162], ![210, -136, 219, -119, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N3 : Nat.card (O ⧸ I257N3) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N3)

lemma isPrimeI257N3 : Ideal.IsPrime I257N3 := prime_ideal_of_norm_prime hp257.out _ NI257N3
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![25541, -65323, 11161, -2514, 8354]] ![![3, 40, -84, -8, -30]]
  ![![1647, -4877, 3925, 836, -2656]] where
 M := ![![![1647, -4877, 3925, 836, -2656]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI257N1 : IdealMulLeCertificate' Table 
  ![![1647, -4877, 3925, 836, -2656]] ![![2181, -5578, 954, -214, 712]]
  ![![392339, -1002211, 169405, -36436, 125736]] where
 M := ![![![392339, -1002211, 169405, -36436, 125736]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI257N2 : IdealMulLeCertificate' Table 
  ![![392339, -1002211, 169405, -36436, 125736]] ![![-1, 7, -9, -4, 0]]
  ![![257, 0, 0, 0, 0]] where
 M := ![![![-265481, 723198, -535588, -254944, 578250]]]
 hmul := by decide  
 g := ![![![![-1033, 2814, -2084, -992, 2250]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1, I257N2, I257N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
    exact isPrimeI257N2
    exact isPrimeI257N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0 ⊙ MulI257N1 ⊙ MulI257N2)
instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1569, 4253, -957, 144, -618]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![-1569, 4253, -957, 144, -618]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![231, 257, 40, 1, 0], ![27, 33, 53, 0, 1]] where
  M :=![![![-1569, 4253, -957, 144, -618], ![-288, 1191, -877, -9, -372], ![18, 1182, -2184, -115, -798], ![230, 2980, -6345, -358, -2286], ![-240, 2866, -4161, -187, -1565]]]
  hmulB := by decide  
  f := ![![![-5, 21, 17, -8, 0]], ![![16, -21, -3, 33, -48]], ![![-66, 274, -354, 27, 102]], ![![1, 38, -37, 27, -30]], ![![-11, 52, -67, 9, 13]]]
  g := ![![![-69, -47, 99, 144, -618], ![45, 60, 73, -9, -372], ![183, 217, 170, -115, -798], ![550, 648, 491, -358, -2286], ![324, 390, 328, -187, -1565]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [225, 215, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [126, 231, 15], [83, 31, 248], [0, 1]]
 g := ![![[31, 166, 43], [50, 45, 223], [106, 15, 36], [38, 48], [68, 61], [0, 44], [209, 1], []], ![[79, 34, 81, 76], [190, 157, 122, 20], [45, 65, 114, 59], [42, 103], [229, 216], [242, 35], [231, 172], [40, 225]], ![[222, 99, 88, 181], [13, 211, 99, 16], [224, 2, 186, 124], [131, 234], [250, 48], [251, 49], [63, 235], [70, 225]]]
 h' := ![![[126, 231, 15], [59, 216, 147], [83, 205, 152], [99, 229, 6], [170, 0, 171], [74, 108, 18], [52, 76, 71], [0, 0, 1], [0, 1]], ![[83, 31, 248], [249, 136, 170], [129, 157, 160], [251, 7, 202], [93, 94, 41], [164, 139, 74], [228, 74, 185], [38, 39, 31], [126, 231, 15]], ![[0, 1], [175, 174, 209], [217, 164, 214], [130, 27, 55], [82, 169, 51], [239, 16, 171], [13, 113, 7], [81, 224, 231], [83, 31, 248]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131, 44], []]
 b := ![[], [75, 135, 225], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [225, 215, 54, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1534229, -2605106, -662579, 3052067, -4046394]
  a := ![-6, -55, 11, -7, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2259470, -2484621, 348721, 3052067, -4046394]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 18191447 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -43, 64, 3, 24]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![-1, -43, 64, 3, 24]] 
 ![![263, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![67, 0, 1, 0, 0], ![114, 0, 0, 1, 0], ![128, 0, 0, 0, 1]] where
  M :=![![![-1, -43, 64, 3, 24], ![-6, -91, 182, 10, 66], ![-20, -250, 533, 30, 192], ![-60, -728, 1568, 89, 564], ![-38, -458, 986, 56, 355]]]
  hmulB := by decide  
  f := ![![![-445, 989, -194, 41, -114]], ![![-24, 53, -10, 2, -6]], ![![-113, 251, -49, 11, -30]], ![![-194, 434, -92, 19, -48]], ![![-218, 484, -94, 18, -53]]]
  g := ![![![-27, -43, 64, 3, 24], ![-78, -91, 182, 10, 66], ![-229, -250, 533, 30, 192], ![-674, -728, 1568, 89, 564], ![-424, -458, 986, 56, 355]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1

def I263N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 70, -81, 5, 24]] i)))

def SI263N2: IdealEqSpanCertificate' Table ![![-17, 70, -81, 5, 24]] 
 ![![263, 0, 0, 0, 0], ![209, 1, 0, 0, 0], ![240, 0, 1, 0, 0], ![73, 0, 0, 1, 0], ![53, 0, 0, 0, 1]] where
  M :=![![![-17, 70, -81, 5, 24], ![-10, -103, 301, -139, 78], ![278, -600, 182, 423, -678], ![-846, 3836, -5433, 692, 1182], ![-654, 938, 729, -1463, 1801]]]
  hmulB := by decide  
  f := ![![![-10035, -97906, 220007, 12679, 78876]], ![![-8071, -78945, 177306, 10216, 63570]], ![![-9438, -92716, 208048, 11983, 74598]], ![![-3611, -37110, 82512, 4735, 29610]], ![![-2543, -25976, 57826, 3320, 20749]]]
  g := ![![![12, 70, -81, 5, 24], ![-170, -103, 301, -139, 78], ![331, -600, 182, 423, -678], ![1476, 3836, -5433, 692, 1182], ![-1370, 938, 729, -1463, 1801]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N2 : Nat.card (O ⧸ I263N2) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N2)

lemma isPrimeI263N2 : Ideal.IsPrime I263N2 := prime_ideal_of_norm_prime hp263.out _ NI263N2
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![-1569, 4253, -957, 144, -618]] ![![-1, -43, 64, 3, 24]]
  ![![10035, 97906, -220007, -12679, -78876]] where
 M := ![![![10035, 97906, -220007, -12679, -78876]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI263N1 : IdealMulLeCertificate' Table 
  ![![10035, 97906, -220007, -12679, -78876]] ![![-17, 70, -81, 5, 24]]
  ![![263, 0, 0, 0, 0]] where
 M := ![![![-263, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1, I263N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
    exact isPrimeI263N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0 ⊙ MulI263N1)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0, 0, 0]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![269, 0, 0, 0, 0]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![0, 0, 0, 269, 0], ![0, 0, 0, 0, 269]] where
  M :=![![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![0, 0, 0, 269, 0], ![0, 0, 0, 0, 269]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 5 2 8 [236, 78, 0, 0, 75, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [126, 193, 89, 233, 214], [148, 67, 139, 138, 235], [192, 148, 34, 102, 58], [266, 129, 7, 65, 31], [0, 1]]
 g := ![![[175, 157, 203, 262, 214], [167, 159, 118, 51], [105, 45, 152, 175, 61], [169, 212, 261, 10, 92], [67, 125, 84, 255], [186, 245, 194, 1], [], []], ![[36, 27, 203, 149, 189, 222, 199, 67], [87, 112, 143, 100], [251, 37, 260, 51, 69, 64, 28, 30], [198, 213, 259, 93, 50, 166, 69, 47], [3, 108, 62, 211], [142, 183, 134, 100], [144, 227, 211, 249], [215, 120, 86, 66]], ![[69, 198, 81, 257, 226, 135, 43, 41], [209, 145, 166, 127], [205, 119, 25, 14, 197, 143, 14, 115], [175, 46, 220, 258, 245, 240, 45, 143], [58, 3, 18, 228], [127, 186, 39, 45], [245, 143, 2, 217], [237, 236, 218, 80]], ![[256, 121, 140, 156, 216, 92, 246, 218], [195, 86, 256, 260], [191, 149, 92, 152, 188, 50, 106, 96], [92, 74, 218, 217, 26, 156, 68, 24], [214, 131, 116, 260], [175, 18, 118, 144], [189, 262, 78, 103], [169, 86, 18, 136]], ![[78, 58, 109, 241, 265, 242, 246, 168], [202, 137, 116, 216], [157, 238, 15, 240, 126, 51, 100, 102], [184, 156, 39, 190, 45, 132, 149, 227], [88, 127, 48, 248], [0, 46, 220, 133], [155, 36, 179, 235], [18, 262, 12, 154]]]
 h' := ![![[126, 193, 89, 233, 214], [79, 257, 75, 206, 131], [237, 93, 228, 151, 201], [197, 177, 150, 159, 64], [39, 238, 212, 196, 19], [220, 33, 204, 234, 229], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[148, 67, 139, 138, 235], [238, 174, 116, 210, 142], [47, 29, 201, 19, 10], [41, 233, 128, 91, 141], [263, 196, 224, 126, 202], [83, 114, 224, 6, 91], [117, 191, 178, 32, 10], [106, 49, 162, 39, 49], [126, 193, 89, 233, 214]], ![[192, 148, 34, 102, 58], [159, 232, 60, 188, 96], [16, 157, 162, 161, 193], [199, 116, 243, 90, 66], [148, 187, 84, 226, 41], [170, 118, 69, 237, 94], [217, 123, 72, 241, 160], [135, 257, 256, 187, 237], [148, 67, 139, 138, 235]], ![[266, 129, 7, 65, 31], [28, 117, 187, 75, 51], [262, 11, 158, 102, 23], [190, 218, 202, 28, 22], [4, 160, 148, 144, 11], [151, 21, 144, 251, 23], [5, 151, 256, 29, 12], [208, 220, 63, 130, 209], [192, 148, 34, 102, 58]], ![[0, 1], [68, 27, 100, 128, 118], [193, 248, 58, 105, 111], [94, 63, 84, 170, 245], [252, 26, 139, 115, 265], [245, 252, 166, 79, 101], [194, 73, 32, 236, 86], [65, 12, 56, 182, 43], [266, 129, 7, 65, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [261, 57, 41, 251], [], [], []]
 b := ![[], [205, 111, 144, 211, 254], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 5
  hpos := by decide
  P := [236, 78, 0, 0, 75, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![33559902, -102144949, 90871697, 28492480, -68523446]
  a := ![1, -3, -1, 0, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![124758, -379721, 337813, 105920, -254734]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 1408514752349 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def PBC269 : ContainsPrimesAboveP 269 ![I269N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![269, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 269 (by decide) 𝕀

instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5331, -39548, 14214, -788, 7514]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![5331, -39548, 14214, -788, 7514]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![182, 231, 1, 0, 0], ![234, 208, 0, 1, 0], ![91, 70, 0, 0, 1]] where
  M :=![![![5331, -39548, 14214, -788, 7514], ![1576, -26301, 25714, 762, 10300], ![-1524, -38100, 68685, 3590, 25172], ![-7180, -95032, 199218, 11161, 71884], ![-4100, -62442, 125798, 6930, 45569]]]
  hmulB := by decide  
  f := ![![![-56715, 145088, -24882, 5604, -18538]], ![![-11208, 28645, -4942, 986, -3452]], ![![-47650, 121873, -20921, 4604, -15396]], ![![-57574, 147272, -25294, 5605, -18664]], ![![-21995, 56264, -9668, 2142, -7129]]]
  g := ![![![-11369, -13598, 14214, -788, 7514], ![-21380, -25261, 25714, 762, 10300], ![-57686, -67945, 68685, 3590, 25172], ![-167594, -197298, 199218, 11161, 71884], ![-105785, -124550, 125798, 6930, 45569]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [86, 237, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 270], [0, 1]]
 g := ![![[258, 100], [30, 67], [184, 219], [91, 83], [81], [224], [72], [1]], ![[135, 171], [140, 204], [42, 52], [203, 188], [81], [224], [72], [1]]]
 h' := ![![[34, 270], [130, 261], [165, 164], [33, 46], [5, 25], [14, 9], [120, 123], [185, 34], [0, 1]], ![[0, 1], [61, 10], [50, 107], [242, 225], [42, 246], [49, 262], [237, 148], [257, 237], [34, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [237, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 2
  hpos := by decide
  P := [86, 237, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3248, -26273, 57632, -10461, 3460]
  a := ![-8, 28, 13, -9, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30822, -42087, 57632, -10461, 3460]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -20, 37, -1, 6]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![1, -20, 37, -1, 6]] 
 ![![271, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![235, 0, 1, 0, 0], ![216, 0, 0, 1, 0], ![233, 0, 0, 0, 1]] where
  M :=![![![1, -20, 37, -1, 6], ![2, -25, 31, 27, 6], ![-54, 32, 110, -35, 174], ![70, -820, 1493, -168, 138], ![106, -424, 431, 211, -163]]]
  hmulB := by decide  
  f := ![![![524563, -1471824, 253429, -55563, 188622]], ![![12024, -33845, 5829, -1277, 4338]], ![![454973, -1276636, 219821, -48194, 163608]], ![![418126, -1173216, 202013, -44290, 150354]], ![![451479, -1266708, 218110, -47820, 162335]]]
  g := ![![![-36, -20, 37, -1, 6], ![-53, -25, 31, 27, 6], ![-218, 32, 110, -35, 174], ![-1261, -820, 1493, -168, 138], ![-392, -424, 431, 211, -163]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1

def I271N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![449, -2868, 514, -98, 376]] i)))

def SI271N2: IdealEqSpanCertificate' Table ![![449, -2868, 514, -98, 376]] 
 ![![271, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![192, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![151, 0, 0, 0, 1]] where
  M :=![![![449, -2868, 514, -98, 376], ![196, -1251, 222, -42, 164], ![84, -544, 99, -22, 76], ![44, -264, 74, -9, 20], ![60, -364, 54, -2, 37]]]
  hmulB := by decide  
  f := ![![![-1457, 5772, -4342, -50, -1832]], ![![-462, 1853, -1418, -18, -596]], ![![-1028, 4144, -3193, -42, -1340]], ![![-89, 564, -648, -23, -252]], ![![-805, 3320, -2636, -40, -1099]]]
  g := ![![![345, -2868, 514, -98, 376], ![152, -1251, 222, -42, 164], ![62, -544, 99, -22, 76], ![21, -264, 74, -9, 20], ![57, -364, 54, -2, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N2 : Nat.card (O ⧸ I271N2) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N2)

lemma isPrimeI271N2 : Ideal.IsPrime I271N2 := prime_ideal_of_norm_prime hp271.out _ NI271N2

def I271N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-57, 444, -183, 7, -92]] i)))

def SI271N3: IdealEqSpanCertificate' Table ![![-57, 444, -183, 7, -92]] 
 ![![271, 0, 0, 0, 0], ![219, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![41, 0, 0, 1, 0], ![112, 0, 0, 0, 1]] where
  M :=![![![-57, 444, -183, 7, -92], ![-14, 325, -363, -13, -142], ![26, 528, -992, -53, -362], ![106, 1368, -2889, -162, -1042], ![62, 890, -1823, -101, -659]]]
  hmulB := by decide  
  f := ![![![34453, -88100, 15041, -3375, 11248]], ![![27867, -71259, 12166, -2730, 9098]], ![![768, -1964, 336, -75, 250]], ![![5213, -13328, 2270, -509, 1702]], ![![14270, -36490, 6229, -1399, 4661]]]
  g := ![![![-318, 444, -183, 7, -92], ![-194, 325, -363, -13, -142], ![-247, 528, -992, -53, -362], ![-586, 1368, -2889, -162, -1042], ![-391, 890, -1823, -101, -659]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N3 : Nat.card (O ⧸ I271N3) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N3)

lemma isPrimeI271N3 : Ideal.IsPrime I271N3 := prime_ideal_of_norm_prime hp271.out _ NI271N3
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![5331, -39548, 14214, -788, 7514]] ![![1, -20, 37, -1, 6]]
  ![![-99997, -1202848, 2596849, 147221, 934408]] where
 M := ![![![-99997, -1202848, 2596849, 147221, 934408]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI271N1 : IdealMulLeCertificate' Table 
  ![![-99997, -1202848, 2596849, 147221, 934408]] ![![449, -2868, 514, -98, 376]]
  ![![20659, -122468, 9723, -5161, 12096]] where
 M := ![![![20659, -122468, 9723, -5161, 12096]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI271N2 : IdealMulLeCertificate' Table 
  ![![20659, -122468, 9723, -5161, 12096]] ![![-57, 444, -183, 7, -92]]
  ![![271, 0, 0, 0, 0]] where
 M := ![![![992673, -21790568, 23889192, 835764, 9376600]]]
 hmul := by decide  
 g := ![![![![3663, -80408, 88152, 3084, 34600]]]]
 hle2 := by decide  


def PBC271 : ContainsPrimesAboveP 271 ![I271N0, I271N1, I271N2, I271N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
    exact isPrimeI271N1
    exact isPrimeI271N2
    exact isPrimeI271N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 271 (by decide) (𝕀 ⊙ MulI271N0 ⊙ MulI271N1 ⊙ MulI271N2)
instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![557, -3211, 130, -145, 276]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![557, -3211, 130, -145, 276]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![166, 121, 238, 1, 0], ![26, 70, 262, 0, 1]] where
  M :=![![![557, -3211, 130, -145, 276], ![290, -837, -1162, -132, -318], ![264, 1298, -4095, -262, -1428], ![524, 5452, -12340, -715, -4428], ![370, 3178, -7726, -454, -2755]]]
  hmulB := by decide  
  f := ![![![4243, -10853, 1856, -417, 1386]], ![![834, -2135, 370, -82, 270]], ![![164, -410, 49, -6, 48]], ![![3048, -7789, 1316, -291, 990]], ![![768, -1956, 316, -66, 245]]]
  g := ![![![63, -18, -136, -145, 276], ![110, 135, 410, -132, -318], ![292, 480, 1561, -262, -1428], ![846, 1451, 4758, -715, -4428], ![532, 906, 2968, -454, -2755]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 3 2 8 [249, 193, 167, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 109, 143], [35, 167, 134], [0, 1]]
 g := ![![[250, 230, 57], [163, 165], [169, 200, 87], [210, 267], [102, 92, 116], [190, 16], [110, 1], []], ![[222, 197, 30, 178], [172, 237], [143, 99, 31, 167], [204, 264], [247, 222, 20, 257], [170, 102], [202, 189], [23, 228]], ![[260, 213, 115, 56], [261, 193], [253, 255, 118, 253], [1, 39], [141, 11, 118, 239], [24, 59], [237, 247], [32, 228]]]
 h' := ![![[75, 109, 143], [107, 265, 67], [23, 252, 188], [257, 13, 151], [86, 123, 199], [38, 137, 160], [33, 127, 273], [0, 0, 1], [0, 1]], ![[35, 167, 134], [129, 117, 55], [24, 273, 121], [234, 56, 207], [93, 205, 131], [87, 116, 52], [271, 218, 42], [175, 13, 167], [75, 109, 143]], ![[0, 1], [247, 172, 155], [124, 29, 245], [217, 208, 196], [167, 226, 224], [159, 24, 65], [149, 209, 239], [182, 264, 109], [35, 167, 134]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113, 223], []]
 b := ![[], [153, 152, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 3
  hpos := by decide
  P := [249, 193, 167, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8353689, -6491725, 54637443, -37839188, 31061303]
  a := ![10, -11, -15, 12, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![19730533, 8656169, 3329613, -37839188, 31061303]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 21253933 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4243, 10853, -1856, 417, -1386]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![-4243, 10853, -1856, 417, -1386]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![20, 39, 1, 0, 0], ![51, 161, 0, 1, 0], ![24, 243, 0, 0, 1]] where
  M :=![![![-4243, 10853, -1856, 417, -1386], ![-834, 2135, -370, 82, -270], ![-164, 410, -49, 6, -48], ![-12, 40, -4, 35, -60], ![-1070, 2764, -538, 128, -353]]]
  hmulB := by decide  
  f := ![![![-557, 3211, -130, 145, -276]], ![![-290, 837, 1162, 132, 318]], ![![-82, 345, 169, 30, 30]], ![![-273, 1058, 696, 106, 150]], ![![-304, 1001, 1036, 130, 265]]]
  g := ![![![162, 1274, -1856, 417, -1386], ![32, 249, -370, 82, -270], ![6, 47, -49, 6, -48], ![-1, 33, -4, 35, -60], ![42, 321, -538, 128, -353]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P1 : CertificateIrreducibleZModOfList' 277 2 2 8 [211, 139, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [138, 276], [0, 1]]
 g := ![![[128, 256], [81], [188, 40], [112], [176, 261], [92], [208], [1]], ![[0, 21], [81], [168, 237], [112], [184, 16], [92], [208], [1]]]
 h' := ![![[138, 276], [8, 16], [220, 268], [237, 219], [259, 77], [125, 240], [79, 107], [66, 138], [0, 1]], ![[0, 1], [0, 261], [86, 9], [266, 58], [82, 200], [5, 37], [164, 170], [274, 139], [138, 276]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [223]]
 b := ![[], [201, 250]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N1 : CertifiedPrimeIdeal' SI277N1 277 where
  n := 2
  hpos := by decide
  P := [211, 139, 1]
  hirr := P277P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9445, -27970, 25098, 6160, -18942]
  a := ![-6, 6, 10, -16, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1271, 9402, 25098, 6160, -18942]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N1 B_one_repr
lemma NI277N1 : Nat.card (O ⧸ I277N1) = 76729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N1
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![557, -3211, 130, -145, 276]] ![![-4243, 10853, -1856, 417, -1386]]
  ![![277, 0, 0, 0, 0]] where
 M := ![![![-277, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![281, 0, 0, 0, 0]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![281, 0, 0, 0, 0]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![0, 0, 0, 281, 0], ![0, 0, 0, 0, 281]] where
  M :=![![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![0, 0, 0, 281, 0], ![0, 0, 0, 0, 281]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 5 2 8 [74, 54, 1, 68, 107, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 258, 65, 219, 81], [119, 1, 261, 257, 93], [167, 259, 56, 265, 88], [122, 43, 180, 102, 19], [0, 1]]
 g := ![![[231, 127, 217, 158, 36], [105, 60, 278, 209], [242, 138, 225, 56], [117, 243, 239, 186, 163], [86, 130, 151, 186, 126], [56, 141, 174, 1], [], []], ![[51, 56, 43, 234, 55, 130, 154, 191], [259, 22, 229, 138], [12, 265, 20, 136], [147, 8, 269, 150, 147, 146, 234, 56], [42, 50, 51, 14, 125, 248, 278, 248], [271, 115, 141, 32], [52, 139, 138, 1], [96, 256, 264, 98]], ![[229, 172, 7, 252, 34, 7, 69, 197], [18, 70, 62, 195], [234, 268, 63, 232], [198, 9, 124, 267, 176, 112, 115, 92], [72, 123, 224, 66, 196, 216, 63, 110], [203, 190, 243, 149], [187, 280, 271, 157], [270, 145, 203, 219]], ![[248, 129, 229, 223, 20, 253, 43, 147], [22, 191, 191, 212], [185, 100, 240, 162], [233, 140, 216, 187, 130, 89, 259, 150], [135, 189, 154, 62, 42, 255, 12, 199], [191, 80, 186, 140], [54, 93, 44, 249], [181, 14, 55, 157]], ![[224, 175, 44, 174, 156, 241, 46, 139], [278, 178, 216, 128], [230, 115, 146, 248], [110, 183, 1, 42, 92, 51, 79, 174], [142, 263, 208, 2, 250, 280, 150, 84], [176, 202, 221, 223], [243, 106, 11, 167], [31, 167, 93, 80]]]
 h' := ![![[47, 258, 65, 219, 81], [103, 260, 259, 100, 6], [75, 219, 188, 145, 174], [53, 113, 50, 266, 233], [99, 50, 30, 71, 43], [71, 30, 248, 69, 209], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[119, 1, 261, 257, 93], [63, 126, 216, 194, 163], [270, 102, 23, 267, 177], [92, 74, 183, 275, 97], [176, 48, 258, 263, 99], [92, 240, 91, 136, 216], [241, 73, 265, 164, 34], [163, 124, 159, 263, 1], [47, 258, 65, 219, 81]], ![[167, 259, 56, 265, 88], [91, 77, 88, 123, 209], [115, 236, 127, 237, 40], [3, 18, 151, 60, 191], [29, 40, 179, 173, 173], [205, 141, 212, 146, 242], [192, 157, 28, 270, 235], [82, 218, 219, 279, 88], [119, 1, 261, 257, 93]], ![[122, 43, 180, 102, 19], [225, 252, 30, 141, 28], [254, 3, 20, 257, 103], [229, 30, 219, 89, 64], [83, 188, 224, 112, 111], [129, 40, 51, 197, 84], [139, 8, 1, 116, 155], [164, 107, 131, 126, 165], [167, 259, 56, 265, 88]], ![[0, 1], [221, 128, 250, 4, 156], [53, 2, 204, 218, 68], [142, 46, 240, 153, 258], [264, 236, 152, 224, 136], [64, 111, 241, 14, 92], [217, 43, 268, 12, 137], [226, 113, 52, 175, 27], [122, 43, 180, 102, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [280, 177, 82, 184], [], [], []]
 b := ![[], [169, 24, 32, 59, 192], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 5
  hpos := by decide
  P := [74, 54, 1, 68, 107, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18716571966394, 47220956474731, -30037813267344, -18920017437148, 42752906052621]
  a := ![-6, 18, 16, -5, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-66607017674, 168046108451, -106896132624, -67331022908, 152145573141]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 1751989905401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def PBC281 : ContainsPrimesAboveP 281 ![I281N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI281N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![281, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 281 (by decide) 𝕀

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


def P283P0 : CertificateIrreducibleZModOfList' 283 5 2 8 [91, 53, 185, 44, 265, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [235, 114, 226, 213, 48], [188, 228, 79, 126, 74], [237, 219, 173, 80, 28], [207, 4, 88, 147, 133], [0, 1]]
 g := ![![[212, 168, 47, 137, 96], [168, 172, 83, 150, 64], [220, 134, 232, 44], [198, 272, 33, 73, 57], [255, 133, 197, 72, 41], [101, 280, 18, 1], [], []], ![[9, 4, 122, 43, 35, 113, 95, 229], [134, 257, 175, 258, 250, 233, 125, 18], [96, 242, 79, 256], [207, 43, 19, 94, 34, 63, 218, 194], [129, 235, 5, 208, 246, 41, 141, 109], [84, 112, 221, 151], [134, 238, 274, 252], [0, 38, 226, 40]], ![[141, 108, 214, 138, 130, 182, 97, 112], [9, 116, 130, 267, 82, 124, 82, 40], [216, 21, 241, 61], [135, 156, 118, 87, 100, 111, 105, 41], [105, 127, 59, 282, 90, 228, 272, 233], [236, 48, 187, 25], [181, 209, 130, 95], [191, 129, 54, 99]], ![[144, 113, 193, 150, 89, 185, 25, 113], [70, 96, 240, 11, 210, 268, 152, 111], [21, 233, 114, 99], [98, 261, 80, 239, 204, 229, 58, 157], [197, 155, 85, 80, 158, 257, 198, 175], [142, 35, 86, 236], [227, 36, 150, 181], [204, 137, 197, 218]], ![[244, 98, 193, 281, 274, 76, 185, 232], [46, 276, 42, 201, 150, 187, 222, 249], [267, 84, 255, 25], [7, 60, 90, 125, 180, 148, 79, 46], [26, 280, 99, 148, 21, 1, 231, 242], [16, 68, 22, 1], [156, 148, 171, 151], [277, 172, 75, 143]]]
 h' := ![![[235, 114, 226, 213, 48], [277, 166, 141, 32, 68], [136, 20, 102, 185, 8], [94, 130, 217, 132, 238], [1, 248, 196, 225, 118], [148, 14, 212, 160, 265], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[188, 228, 79, 126, 74], [85, 249, 119, 197, 117], [43, 14, 80, 212, 75], [17, 32, 176, 168, 16], [243, 97, 271, 177, 189], [127, 100, 273, 268, 216], [160, 39, 203, 277, 43], [40, 31, 133, 225, 188], [235, 114, 226, 213, 48]], ![[237, 219, 173, 80, 28], [162, 107, 252, 275, 264], [224, 255, 201, 158, 212], [97, 41, 145, 262, 108], [117, 205, 93, 129, 221], [121, 200, 44, 45, 49], [70, 219, 174, 2, 5], [134, 191, 76, 206, 183], [188, 228, 79, 126, 74]], ![[207, 4, 88, 147, 133], [7, 82, 155, 146, 100], [213, 64, 88, 218, 269], [133, 265, 180, 126, 209], [263, 99, 186, 255, 234], [206, 249, 106, 57, 139], [26, 189, 50, 2, 233], [249, 155, 247, 135, 152], [237, 219, 173, 80, 28]], ![[0, 1], [26, 245, 182, 199, 17], [122, 213, 95, 76, 2], [274, 98, 131, 161, 278], [215, 200, 103, 63, 87], [220, 3, 214, 36, 180], [114, 119, 139, 2, 1], [96, 189, 109, 0, 43], [207, 4, 88, 147, 133]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 144, 221, 218], [], [], []]
 b := ![[], [282, 38, 42, 185, 78], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 5
  hpos := by decide
  P := [91, 53, 185, 44, 265, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1720367471, -14634347425, 27659780986, -8139051417, 588268138]
  a := ![-2, -2, 3, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6079037, -51711475, 97737742, -28759899, 2078686]
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

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28585, 480211, -943029, -51364, -342484]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![28585, 480211, -943029, -51364, -342484]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![0, 0, 0, 293, 0], ![76, 257, 164, 166, 1]] where
  M :=![![![28585, 480211, -943029, -51364, -342484], ![102728, 1295793, -2756237, -155333, -993152], ![310666, 3764670, -8108574, -459267, -2918302], ![918534, 11065340, -23877849, -1353436, -8592206], ![577276, 6964332, -15021397, -851283, -5405533]]]
  hmulB := by decide  
  f := ![![![71, -215, 147, -4, -38]], ![![8, 215, -569, 231, -100]], ![![-462, 870, 8, -831, 1186]], ![![1662, -6868, 9051, -702, -2614]], ![![712, -3275, 4664, -652, -925]]]
  g := ![![![88933, 302043, 188479, 193860, -342484], ![257960, 875549, 546487, 562143, -993152], ![758026, 2572588, 1605778, 1651805, -2918302], ![2231830, 7574274, 4727795, 4863320, -8592206], ![1404088, 4765141, 2974355, 3059615, -5405533]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 4 2 8 [68, 27, 259, 105, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [216, 170, 247, 18], [194, 172, 41, 105], [71, 243, 5, 170], [0, 1]]
 g := ![![[83, 39, 234, 95], [102, 102, 77], [79, 68, 168, 258], [70, 197, 178], [74, 84, 26], [136, 264, 203, 184], [1], []], ![[58, 70, 93, 232, 182, 136], [168, 125, 161], [167, 155, 92, 39, 170, 62], [110, 58, 6], [119, 81, 167], [14, 140, 80, 169, 280, 285], [18, 88, 84], [182, 70, 31]], ![[49, 223, 207, 82, 233, 98], [233, 152, 279], [237, 40, 158, 197, 168, 252], [115, 114, 39], [277, 213, 107], [59, 31, 92, 60, 102, 11], [75, 254, 149], [123, 131, 184]], ![[156, 151, 23, 115, 200, 81], [165, 29, 203], [161, 166, 187, 156, 183, 150], [271, 13, 15], [192, 265, 96], [114, 167, 93, 103, 2, 124], [266, 217, 167], [70, 43, 186]]]
 h' := ![![[216, 170, 247, 18], [31, 251, 75, 238], [195, 178, 50, 202], [279, 81, 62, 234], [218, 130, 178, 44], [128, 287, 256, 57], [225, 266, 34, 188], [0, 0, 1], [0, 1]], ![[194, 172, 41, 105], [286, 113, 29, 189], [269, 74, 105, 109], [65, 29, 82, 6], [147, 204, 64, 42], [62, 287, 65, 131], [242, 192, 211, 201], [292, 185, 84, 60], [216, 170, 247, 18]], ![[71, 243, 5, 170], [246, 99, 74, 115], [104, 241, 156, 54], [235, 78, 184, 103], [12, 126, 8, 25], [168, 173, 124, 273], [79, 123, 109, 21], [265, 9, 223, 102], [194, 172, 41, 105]], ![[0, 1], [86, 123, 115, 44], [240, 93, 275, 221], [128, 105, 258, 243], [119, 126, 43, 182], [24, 132, 141, 125], [222, 5, 232, 176], [281, 99, 278, 131], [71, 243, 5, 170]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [138, 258, 101], []]
 b := ![[], [], [225, 53, 209, 186], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 4
  hpos := by decide
  P := [68, 27, 259, 105, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31819363500, 84999990372, -60812224974, -31244659396, 70462577184]
  a := ![-10, 13, 20, -14, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18385580988, -61514956812, -39647354550, -40027414580, 70462577184]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 7370050801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71, 215, -147, 4, 38]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![-71, 215, -147, 4, 38]] 
 ![![293, 0, 0, 0, 0], ![174, 1, 0, 0, 0], ![196, 0, 1, 0, 0], ![177, 0, 0, 1, 0], ![239, 0, 0, 0, 1]] where
  M :=![![![-71, 215, -147, 4, 38], ![-8, -215, 569, -231, 100], ![462, -870, -8, 831, -1186], ![-1662, 6868, -9051, 702, 2614], ![-1040, 1082, 2165, -2717, 3017]]]
  hmulB := by decide  
  f := ![![![-28585, -480211, 943029, 51364, 342484]], ![![-17326, -289599, 569431, 31033, 206776]], ![![-20182, -334082, 658506, 35927, 239062]], ![![-20403, -327859, 651174, 35648, 236218]], ![![-25287, -415477, 820496, 44803, 297813]]]
  g := ![![![-63, 215, -147, 4, 38], ![-195, -215, 569, -231, 100], ![989, -870, -8, 831, -1186], ![-586, 6868, -9051, 702, 2614], ![-2914, 1082, 2165, -2717, 3017]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N1 : Nat.card (O ⧸ I293N1) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N1)

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := prime_ideal_of_norm_prime hp293.out _ NI293N1
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![28585, 480211, -943029, -51364, -342484]] ![![-71, 215, -147, 4, 38]]
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


def P307P0 : CertificateIrreducibleZModOfList' 307 5 2 8 [303, 211, 175, 194, 8, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 214, 14, 226, 105], [234, 189, 303, 268, 160], [224, 126, 236, 198, 164], [14, 84, 61, 229, 185], [0, 1]]
 g := ![![[187, 1, 11, 64, 153], [305, 125, 169, 162, 287], [226, 217, 232, 250], [176, 124, 22, 240], [3, 149, 299, 236, 256], [12, 268, 177, 299, 1], [], []], ![[28, 184, 235, 131, 29, 54, 7, 153], [156, 211, 295, 10, 171, 180, 107, 113], [55, 294, 133, 37], [273, 190, 64, 28], [38, 97, 119, 59, 184, 106, 159, 24], [180, 285, 258, 162, 81, 128, 170, 302], [199, 234], [238, 196, 91, 280]], ![[83, 170, 192, 221, 82, 51, 81, 94], [220, 294, 138, 161, 101, 280, 70, 216], [277, 101, 208, 79], [74, 277, 173, 170], [58, 274, 176, 18, 38, 153, 90, 269], [251, 191, 170, 77, 274, 27, 271, 227], [13, 269, 177, 105], [96, 186, 76, 119]], ![[253, 110, 3, 146, 66, 244, 247, 199], [35, 301, 107, 289, 85, 301, 305, 10], [95, 252, 258, 276], [78, 107, 292, 101], [248, 252, 163, 184, 61, 30, 243, 101], [147, 254, 80, 85, 222, 285, 98, 107], [4, 136, 122, 26], [250, 94, 206, 187]], ![[304, 107, 94, 146, 292, 37, 271, 132], [99, 165, 59, 156, 110, 206, 203, 207], [101, 104, 123, 68], [118, 221, 262, 284], [118, 110, 213, 293, 113, 303, 138, 193], [306, 293, 38, 174, 159, 205, 264, 108], [300, 92, 72, 223], [185, 220, 42, 148]]]
 h' := ![![[134, 214, 14, 226, 105], [299, 54, 140, 137, 54], [93, 175, 21, 53, 168], [234, 269, 197, 47, 76], [12, 118, 71, 6, 213], [48, 75, 83, 274, 291], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[234, 189, 303, 268, 160], [63, 62, 302, 169, 239], [136, 30, 290, 249, 305], [60, 146, 154, 306, 246], [293, 15, 141, 223, 86], [31, 275, 201, 86, 304], [94, 249, 57, 112, 174], [181, 243, 62, 242], [134, 214, 14, 226, 105]], ![[224, 126, 236, 198, 164], [263, 262, 237, 191, 29], [212, 23, 12, 49, 268], [302, 272, 72, 27, 152], [96, 29, 134, 296, 28], [148, 212, 204, 139, 267], [23, 33, 131, 55, 253], [187, 172, 211, 76, 243], [234, 189, 303, 268, 160]], ![[14, 84, 61, 229, 185], [123, 70, 45, 210, 165], [177, 277, 297, 55, 67], [59, 44, 163, 239, 176], [288, 191, 122, 108, 79], [227, 113, 18, 25, 84], [69, 226, 265, 18, 103], [214, 83, 207, 291, 124], [224, 126, 236, 198, 164]], ![[0, 1], [195, 166, 197, 214, 127], [45, 109, 301, 208, 113], [191, 190, 28, 302, 271], [124, 261, 146, 288, 208], [239, 246, 108, 90, 282], [197, 106, 161, 122, 83], [15, 116, 133, 5, 247], [14, 84, 61, 229, 185]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110, 122, 130, 44], [], [], []]
 b := ![[], [1, 19, 25, 28, 137], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 5
  hpos := by decide
  P := [303, 211, 175, 194, 8, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19348983535, -5107308583170, 12313942151171, -4937074505291, 2171759581615]
  a := ![-6, 8, 9, -7, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![63026005, -16636184310, 40110560753, -16081675913, 7074135445]
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



lemma PB984I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB984I6 : PrimesBelowBoundCertificateInterval O 251 307 984 where
  m := 9
  g := ![4, 3, 1, 4, 2, 1, 1, 2, 1]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB984I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1, I257N2, I257N3]
    · exact ![I263N0, I263N1, I263N2]
    · exact ![I269N0]
    · exact ![I271N0, I271N1, I271N2, I271N3]
    · exact ![I277N0, I277N1]
    · exact ![I281N0]
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
    · exact ![66049, 257, 257, 257]
    · exact ![18191447, 263, 263]
    · exact ![1408514752349]
    · exact ![73441, 271, 271, 271]
    · exact ![21253933, 76729]
    · exact ![1751989905401]
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
      exact NI257N2
      exact NI257N3
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
      exact NI263N2
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
      exact NI271N2
      exact NI271N3
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
      exact NI277N1
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
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
  β := ![I257N1, I257N2, I257N3, I263N1, I263N2, I271N1, I271N2, I271N3, I293N1]
  Il := ![[I257N1, I257N2, I257N3], [I263N1, I263N2], [], [I271N1, I271N2, I271N3], [], [], [], [I293N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
