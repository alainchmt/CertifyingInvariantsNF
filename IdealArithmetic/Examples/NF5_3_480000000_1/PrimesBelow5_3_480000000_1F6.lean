
import IdealArithmetic.Examples.NF5_3_480000000_1.RI5_3_480000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19025, -26782, -19778, 2976, 5524]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![-19025, -26782, -19778, 2976, 5524]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![224, 151, 245, 1, 0], ![239, 215, 0, 0, 1]] where
  M :=![![![-19025, -26782, -19778, 2976, 5524], ![44192, -14159, -59516, -3864, 14452], ![57808, 30400, -10295, -7002, 1430], ![-16376, 37912, 67160, 143, -17014], ![2440, 16708, 20864, -882, -5429]]]
  hmulB := by decide  
  f := ![![![85007, 49666, 16454, 86292, -47392]], ![![-379136, -221791, -73252, -385128, 211484]], ![![845936, 495080, 163337, 859506, -471950]], ![![651160, 381071, 125737, 661589, -363276]], ![![-228791, -133895, -44178, -232458, 127643]]]
  g := ![![![-7805, -6474, -2914, 2976, 5524], ![-9900, -9875, 3452, -3864, 14452], ![4998, 3036, 6635, -7002, 1430], ![15634, 14297, 125, 143, -17014], ![5827, 5125, 922, -882, -5429]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [63, 91, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [108, 202, 31], [135, 54, 226], [0, 1]]
 g := ![![[35, 89, 120], [147, 199], [9, 64], [150, 146], [8, 143], [244, 231], [243, 1], []], ![[170, 198, 12, 207], [6, 213], [10, 32], [], [137, 205], [136, 197], [242, 89], [98, 190]], ![[83, 192, 177, 162], [5, 4], [177, 111], [124, 146], [217, 231], [184, 68], [0, 198], [160, 190]]]
 h' := ![![[108, 202, 31], [16, 88, 67], [5, 133, 126], [217, 169, 8], [71, 182, 143], [33, 14, 237], [111, 183, 105], [0, 0, 1], [0, 1]], ![[135, 54, 226], [74, 138, 178], [130, 75, 133], [195, 210, 17], [130, 70], [199, 11, 125], [85, 34, 35], [93, 128, 54], [108, 202, 31]], ![[0, 1], [178, 31, 12], [39, 49, 255], [41, 135, 232], [237, 5, 114], [162, 232, 152], [73, 40, 117], [178, 129, 202], [135, 54, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [142, 9], []]
 b := ![[], [148, 97, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [63, 91, 14, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-640673, -455097, 47645, -403327, -585418]
  a := ![0, 1, 1, 0, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![893461, 724950, 384680, -403327, -585418]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 16974593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-377, -256, 4, -269, -219]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![-377, -256, 4, -269, -219]] 
 ![![257, 0, 0, 0, 0], ![43, 1, 0, 0, 0], ![232, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![141, 0, 0, 0, 1]] where
  M :=![![![-377, -256, 4, -269, -219], ![-1752, -1199, 26, -1256, -1026], ![-4104, -2800, 57, -2937, -2397], ![-8712, -5948, 124, -6236, -5091], ![-19800, -13518, 280, -14173, -11570]]]
  hmulB := by decide  
  f := ![![![887, 642, 260, 835, -495]], ![![133, 99, 42, 125, -75]], ![![832, 598, 241, 787, -465]], ![![-58, -34, -12, -60, 33]], ![![579, 406, 160, 552, -323]]]
  g := ![![![160, -256, 4, -269, -219], ![743, -1199, 26, -1256, -1026], ![1739, -2800, 57, -2937, -2397], ![3691, -5948, 124, -6236, -5091], ![8390, -13518, 280, -14173, -11570]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1

def I257N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9279, 3628, -3381, -1075, 676]] i)))

def SI257N2: IdealEqSpanCertificate' Table ![![9279, 3628, -3381, -1075, 676]] 
 ![![257, 0, 0, 0, 0], ![238, 1, 0, 0, 0], ![205, 0, 1, 0, 0], ![158, 0, 0, 1, 0], ![70, 0, 0, 0, 1]] where
  M :=![![![9279, 3628, -3381, -1075, 676], ![5408, 10353, 9406, -955, -2549], ![-10196, 1512, 11308, 962, -2707], ![-13532, -11869, -4153, 1830, 1364], ![-5868, -3729, 157, 737, 85]]]
  hmulB := by decide  
  f := ![![![-22473, 6367, -13659, -4323, 4034]], ![![-20686, 5851, -12566, -3983, 3701]], ![![-18065, 5086, -10961, -3497, 3231]], ![![-13826, 3892, -8383, -2663, 2431]], ![![-6306, 1638, -3743, -1308, 1058]]]
  g := ![![![-150, 3628, -3381, -1075, 676], ![-15788, 10353, 9406, -955, -2549], ![-10314, 1512, 11308, 962, -2707], ![12755, -11869, -4153, 1830, 1364], ![2829, -3729, 157, 737, 85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N2 : Nat.card (O ⧸ I257N2) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N2)

lemma isPrimeI257N2 : Ideal.IsPrime I257N2 := prime_ideal_of_norm_prime hp257.out _ NI257N2
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![-19025, -26782, -19778, 2976, 5524]] ![![-377, -256, 4, -269, -219]]
  ![![-38711, -14262, 15966, -6085, -10823]] where
 M := ![![![-38711, -14262, 15966, -6085, -10823]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI257N1 : IdealMulLeCertificate' Table 
  ![![-38711, -14262, 15966, -6085, -10823]] ![![9279, 3628, -3381, -1075, 676]]
  ![![257, 0, 0, 0, 0]] where
 M := ![![![-453266017, -151375570, 200848841, 51481726, -42254655]]]
 hmul := by decide  
 g := ![![![![-1763681, -589010, 781513, 200318, -164415]]]]
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

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6991, 6004, 14615, 462, -3631]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![-6991, 6004, 14615, 462, -3631]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![48, 80, 151, 1, 0], ![181, 17, 244, 0, 1]] where
  M :=![![![-6991, 6004, 14615, 462, -3631], ![-29048, -10993, 11084, 3351, -2245], ![-8980, -16270, -14344, 1551, 3904], ![30140, 2819, -23363, -3131, 5401], ![8780, -1267, -9689, -822, 2324]]]
  hmulB := by decide  
  f := ![![![-8249, -4873, -1571, -8424, 4621]], ![![36968, 21709, 7102, 37629, -20651]], ![![-82604, -48407, -15920, -83991, 46118]], ![![-37056, -21709, -7145, -37673, 20688]], ![![-80815, -47382, -15564, -82194, 45129]]]
  g := ![![![2388, 117, 3159, 462, -3631], ![823, -916, 201, 3351, -2245], ![-3004, -786, -4567, 1551, 3904], ![-3031, 614, -3302, -3131, 5401], ![-1416, 95, -1721, -822, 2324]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [36, 225, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [251, 218, 122], [196, 44, 141], [0, 1]]
 g := ![![[88, 216, 52], [225, 103, 244], [251, 212, 121], [47, 2], [142, 121], [72, 37], [184, 1], []], ![[150, 79, 151, 128], [131, 238, 242, 204], [128, 193, 110, 162], [257, 86], [94, 103], [156, 93], [90, 95], [103, 156]], ![[37, 172, 83, 231], [214, 232, 85, 230], [137, 255, 85, 40], [174, 26], [232, 111], [153, 50], [231, 184], [84, 156]]]
 h' := ![![[251, 218, 122], [53, 2, 29], [169, 134, 36], [73, 217, 11], [72, 17, 153], [72, 97, 252], [214, 118, 230], [0, 0, 1], [0, 1]], ![[196, 44, 141], [32, 19, 205], [179, 245, 48], [82, 225, 132], [38, 64, 127], [240, 110, 41], [164, 225, 57], [118, 167, 44], [251, 218, 122]], ![[0, 1], [61, 242, 29], [10, 147, 179], [71, 84, 120], [54, 182, 246], [76, 56, 233], [245, 183, 239], [150, 96, 218], [196, 44, 141]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [253, 26], []]
 b := ![[], [211, 46, 155], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [36, 225, 79, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-557249063, -392118676, 32740980, -363022634, -462591562]
  a := ![3, -2, 0, -3, -61]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![382497757, 138835546, 637724334, -363022634, -462591562]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 18191447 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![169447, 121007, 13869, -21814, -7215]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![169447, 121007, 13869, -21814, -7215]] 
 ![![263, 0, 0, 0, 0], ![83, 1, 0, 0, 0], ![106, 0, 1, 0, 0], ![162, 0, 0, 1, 0], ![229, 0, 0, 0, 1]] where
  M :=![![![169447, 121007, 13869, -21814, -7215], ![-57720, 169055, 285642, -953, -72657], ![-290628, -67205, 170008, 31819, -37758], ![-122172, -255142, -241845, 22422, 65178], ![-79908, -93682, -57105, 11747, 16483]]]
  hmulB := by decide  
  f := ![![![404465, -138670, 260175, 61928, -83103]], ![![125117, -43051, 80583, 19075, -25836]], ![![164578, -56706, 106042, 25035, -34002]], ![![248370, -85709, 160131, 37745, -51525]], ![![351223, -121873, 226848, 52946, -73193]]]
  g := ![![![-23415, 121007, 13869, -21814, -7215], ![-104846, 169055, 285642, -953, -72657], ![-35139, -67205, 170008, 31819, -37758], ![106966, -255142, -241845, 22422, 65178], ![30689, -93682, -57105, 11747, 16483]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1

def I263N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 39, -184, -28, 42]] i)))

def SI263N2: IdealEqSpanCertificate' Table ![![263, 39, -184, -28, 42]] 
 ![![263, 0, 0, 0, 0], ![141, 1, 0, 0, 0], ![185, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![197, 0, 0, 0, 1]] where
  M :=![![![263, 39, -184, -28, 42], ![336, 317, 134, -46, -42], ![-168, 153, 363, 10, -90], ![-528, -291, 76, 66, -9], ![-200, -77, 74, 21, -14]]]
  hmulB := by decide  
  f := ![![![-12527, 3945, -7838, -2120, 2334]], ![![-6645, 2090, -4156, -1126, 1236]], ![![-8873, 2790, -5549, -1504, 1650]], ![![-1765, 546, -1098, -304, 321]], ![![-9421, 2944, -5880, -1607, 1738]]]
  g := ![![![82, 39, -184, -28, 42], ![-225, 317, 134, -46, -42], ![-272, 153, 363, 10, -90], ![98, -291, 76, 66, -9], ![-4, -77, 74, 21, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N2 : Nat.card (O ⧸ I263N2) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N2)

lemma isPrimeI263N2 : Ideal.IsPrime I263N2 := prime_ideal_of_norm_prime hp263.out _ NI263N2
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![-6991, 6004, 14615, 462, -3631]] ![![169447, 121007, 13869, -21814, -7215]]
  ![![-5544980593, -590871054, 4198319174, 579520154, -967363270]] where
 M := ![![![-5544980593, -590871054, 4198319174, 579520154, -967363270]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI263N1 : IdealMulLeCertificate' Table 
  ![![-5544980593, -590871054, 4198319174, 579520154, -967363270]] ![![263, 39, -184, -28, 42]]
  ![![263, 0, 0, 0, 0]] where
 M := ![![![-2474694178647, 144629073353, 2437548217762, 242356418322, -577593921904]]]
 hmul := by decide  
 g := ![![![![-9409483569, 549920431, 9268244174, 921507294, -2196174608]]]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, 174, 105, -25, -26]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![-35, 174, 105, -25, -26]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![4, 246, 220, 1, 0], ![132, 212, 250, 0, 1]] where
  M :=![![![-35, 174, 105, -25, -26], ![-208, -35, 398, 53, -101], ![-404, -184, -88, 18, 29], ![220, -165, -401, -22, 92], ![-20, -89, -155, -23, 25]]]
  hmulB := by decide  
  f := ![![![329, 193, 63, 335, -184]], ![![-1472, -863, -284, -1497, 821]], ![![3284, 1923, 634, 3338, -1835]], ![![1320, 772, 255, 1341, -739]], ![![2088, 1222, 403, 2122, -1168]]]
  g := ![![![13, 44, 45, -25, -26], ![48, 31, 52, 53, -101], ![-16, -40, -42, 18, 29], ![-44, -53, -69, -22, 92], ![-12, 1, -5, -23, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [18, 81, 163, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [170, 200, 34], [205, 68, 235], [0, 1]]
 g := ![![[140, 118, 255], [65, 173], [217, 158, 152], [127, 183, 13], [215, 79], [193, 5], [106, 1], []], ![[40, 243, 29, 136], [106, 232], [230, 59, 73, 34], [240, 50, 75, 55], [158, 55], [0, 70], [84, 51], [22, 80]], ![[75, 52, 0, 131], [48, 100], [210, 65, 74, 142], [167, 239, 117, 21], [160, 51], [7, 57], [247, 188], [90, 80]]]
 h' := ![![[170, 200, 34], [138, 175, 229], [129, 225, 119], [135, 183, 221], [160, 120, 236], [110, 217, 50], [244, 4, 126], [0, 0, 1], [0, 1]], ![[205, 68, 235], [160, 187, 2], [67, 195, 140], [252, 43, 268], [177, 128, 222], [185, 231, 18], [202, 23, 96], [259, 218, 68], [170, 200, 34]], ![[0, 1], [188, 176, 38], [75, 118, 10], [40, 43, 49], [80, 21, 80], [1, 90, 201], [193, 242, 47], [55, 51, 200], [205, 68, 235]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [232, 104], []]
 b := ![[], [15, 84, 171], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [18, 81, 163, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-355009, -239610, 4672, -259717, -194619]
  a := ![1, 0, 1, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![98043, 390000, 393298, -259717, -194619]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45, 28, -37, 0, 19]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![-45, 28, -37, 0, 19]] 
 ![![269, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![94, 0, 1, 0, 0], ![245, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![-45, 28, -37, 0, 19], ![152, 13, 56, 59, 19], ![76, 122, -46, 93, 98], ![316, 207, 1, 221, 179], ![684, 485, -21, 500, 412]]]
  hmulB := by decide  
  f := ![![![-3537, -729, 2191, 388, -493]], ![![-133, -40, 65, 15, -14]], ![![-1226, -261, 748, 135, -168]], ![![-3197, -649, 1994, 350, -449]], ![![-516, -104, 323, 57, -73]]]
  g := ![![![9, 28, -37, 0, 19], ![-76, 13, 56, 59, 19], ![-87, 122, -46, 93, 98], ![-234, 207, 1, 221, 179], ![-523, 485, -21, 500, 412]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1

def I269N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-173, -97, -28, -178, 96]] i)))

def SI269N2: IdealEqSpanCertificate' Table ![![-173, -97, -28, -178, 96]] 
 ![![269, 0, 0, 0, 0], ![89, 1, 0, 0, 0], ![209, 0, 1, 0, 0], ![70, 0, 0, 1, 0], ![178, 0, 0, 0, 1]] where
  M :=![![![-173, -97, -28, -178, 96], ![768, 457, 162, 794, -438], ![-1752, -1027, -337, -1768, 972], ![3504, 2041, 660, 3552, -1947], ![-4936, -2893, -958, -5017, 2756]]]
  hmulB := by decide  
  f := ![![![10319, -3693, 6730, 1506, -2256]], ![![3347, -1206, 2188, 484, -738]], ![![8051, -2894, 5259, 1168, -1770]], ![![2650, -979, 1748, 370, -603]], ![![6774, -2493, 4462, 951, -1534]]]
  g := ![![![36, -97, -28, -178, 96], ![-191, 457, 162, 794, -438], ![412, -1027, -337, -1768, 972], ![-811, 2041, 660, 3552, -1947], ![1165, -2893, -958, -5017, 2756]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N2 : Nat.card (O ⧸ I269N2) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N2)

lemma isPrimeI269N2 : Ideal.IsPrime I269N2 := prime_ideal_of_norm_prime hp269.out _ NI269N2
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![-35, 174, 105, -25, -26]] ![![-45, 28, -37, 0, 19]]
  ![![10319, -3693, 6730, 1506, -2256]] where
 M := ![![![10319, -3693, 6730, 1506, -2256]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI269N1 : IdealMulLeCertificate' Table 
  ![![10319, -3693, 6730, 1506, -2256]] ![![-173, -97, -28, -178, 96]]
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

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, -11, -2, 3]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![7, 0, -11, -2, 3]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![54, 123, 1, 0, 0], ![133, 210, 0, 1, 0], ![18, 49, 0, 0, 1]] where
  M :=![![![7, 0, -11, -2, 3], ![24, 13, 4, 1, -3], ![-12, 6, 12, -7, 0], ![-12, -3, 11, 15, -9], ![-28, -13, 1, -18, 8]]]
  hmulB := by decide  
  f := ![![![-23, 9, -17, -8, 3]], ![![24, -17, 34, -5, -21]], ![![6, -6, 12, -4, -9]], ![![7, -9, 18, -8, -15]], ![![2, -3, 5, -2, -4]]]
  g := ![![![3, 6, -11, -2, 3], ![-1, -2, 4, 1, -3], ![1, 0, 12, -7, 0], ![-9, -15, 11, 15, -9], ![8, 12, 1, -18, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [254, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [166, 270], [0, 1]]
 g := ![![[217, 44], [139, 53], [66, 124], [29, 106], [206], [245], [185], [1]], ![[204, 227], [265, 218], [54, 147], [10, 165], [206], [245], [185], [1]]]
 h' := ![![[166, 270], [195, 216], [38, 18], [222, 143], [207, 169], [162, 217], [182, 40], [17, 166], [0, 1]], ![[0, 1], [8, 55], [45, 253], [112, 128], [77, 102], [141, 54], [47, 231], [202, 105], [166, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [211]]
 b := ![[], [51, 241]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 2
  hpos := by decide
  P := [254, 105, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12248, 9814, -4827, 1269, 35068]
  a := ![1, -4, -2, -5, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1945, -5097, -4827, 1269, 35068]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55, -289, 215, -124, -267]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![55, -289, 215, -124, -267]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![141, 211, 1, 0, 0], ![59, 265, 0, 1, 0], ![226, 189, 0, 0, 1]] where
  M :=![![![55, -289, 215, -124, -267], ![-2136, -941, -330, -1315, -639], ![-2556, -2173, 374, -1909, -2292], ![-8100, -5396, -99, -6036, -3690], ![-14956, -10432, 533, -10387, -10237]]]
  hmulB := by decide  
  f := ![![![62281, 43830, 4205, -7992, -2421]], ![![-19368, 62373, 103644, -545, -26397]], ![![16935, 71281, 83117, -4540, -21864]], ![![-5551, 70190, 101944, -2242, -26253]], ![![38322, 79926, 75715, -7029, -20407]]]
  g := ![![![138, 139, 215, -124, -267], ![983, 1985, -330, -1315, -639], ![2123, 3166, 374, -1909, -2292], ![4413, 8533, -99, -6036, -3690], ![10466, 16843, 533, -10387, -10237]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P1 : CertificateIrreducibleZModOfList' 271 2 2 8 [38, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [168, 270], [0, 1]]
 g := ![![[181, 136], [94, 250], [31, 169], [95, 18], [268], [79], [40], [1]], ![[265, 135], [89, 21], [239, 102], [138, 253], [268], [79], [40], [1]]]
 h' := ![![[168, 270], [222, 223], [177, 122], [184, 258], [145, 17], [64, 57], [195, 185], [233, 168], [0, 1]], ![[0, 1], [17, 48], [77, 149], [168, 13], [20, 254], [155, 214], [110, 86], [2, 103], [168, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [242]]
 b := ![[], [134, 121]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N1 : CertifiedPrimeIdeal' SI271N1 271 where
  n := 2
  hpos := by decide
  P := [38, 103, 1]
  hirr := P271P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4768, -1663, -1240, -5217, 6303]
  a := ![-1, 7, 6, 9, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3493, 1665, -1240, -5217, 6303]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N1 B_one_repr
lemma NI271N1 : Nat.card (O ⧸ I271N1) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N1

def I271N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1735, 2208, 1480, -262, -420]] i)))

def SI271N2: IdealEqSpanCertificate' Table ![![1735, 2208, 1480, -262, -420]] 
 ![![271, 0, 0, 0, 0], ![145, 1, 0, 0, 0], ![192, 0, 1, 0, 0], ![235, 0, 0, 1, 0], ![188, 0, 0, 0, 1]] where
  M :=![![![1735, 2208, 1480, -262, -420], ![-3360, 1377, 4940, 282, -1206], ![-4824, -2366, 1095, 578, -180], ![960, -3292, -5414, 35, 1380], ![-336, -1412, -1646, 90, 433]]]
  hmulB := by decide  
  f := ![![![-167, 1376, -812, 1042, 12]], ![![-89, 729, -432, 548, 18]], ![![-72, 1010, -573, 786, 0]], ![![-179, 1176, -718, 857, 72]], ![![68, 1072, -546, 886, 1]]]
  g := ![![![-1705, 2208, 1480, -262, -420], ![-3657, 1377, 4940, 282, -1206], ![96, -2366, 1095, 578, -180], ![4613, -3292, -5414, 35, 1380], ![1542, -1412, -1646, 90, 433]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N2 : Nat.card (O ⧸ I271N2) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N2)

lemma isPrimeI271N2 : Ideal.IsPrime I271N2 := prime_ideal_of_norm_prime hp271.out _ NI271N2
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![7, 0, -11, -2, 3]] ![![55, -289, 215, -124, -267]]
  ![![-167, 1376, -812, 1042, 12]] where
 M := ![![![-167, 1376, -812, 1042, 12]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI271N1 : IdealMulLeCertificate' Table 
  ![![-167, 1376, -812, 1042, 12]] ![![1735, 2208, 1480, -262, -420]]
  ![![271, 0, 0, 0, 0]] where
 M := ![![![271, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0, 0, 0]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![277, 0, 0, 0, 0]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![0, 0, 0, 277, 0], ![0, 0, 0, 0, 277]] where
  M :=![![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![0, 0, 0, 277, 0], ![0, 0, 0, 0, 277]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 5 2 8 [114, 97, 211, 198, 74, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 261, 36, 153, 245], [77, 234, 239, 272, 230], [153, 218, 121, 43, 136], [132, 117, 158, 86, 220], [0, 1]]
 g := ![![[67, 275, 262, 271, 4], [173, 173, 249, 89], [118, 70, 129, 200, 236], [182, 150, 271, 268], [257, 119, 26, 44, 225], [35, 15, 203, 1], [], []], ![[185, 90, 247, 264, 130, 120, 76, 114], [151, 155, 170, 165], [88, 114, 262, 107, 76, 199, 67, 135], [133, 71, 229, 186], [102, 14, 95, 235, 103, 83, 92, 232], [85, 114, 2, 10], [106, 156, 91, 203], [122, 154, 25, 193]], ![[67, 229, 139, 129, 125, 176, 242, 83], [250, 269, 50, 230], [85, 200, 53, 123, 31, 140, 183, 57], [263, 47, 161, 237], [113, 13, 276, 180, 140, 6, 15, 144], [95, 29, 3, 196], [190, 35, 189, 215], [166, 13, 157, 270]], ![[215, 23, 178, 140, 1, 5, 249, 265], [240, 123, 62, 190], [156, 170, 157, 110, 231, 271, 40, 268], [117, 209, 175, 108], [256, 35, 8, 119, 75, 59, 134, 213], [224, 37, 105, 261], [254, 125, 241, 229], [193, 143, 15, 214]], ![[238, 247, 68, 237, 179, 162, 31, 141], [207, 83, 120, 123], [161, 160, 117, 61, 92, 214, 269, 222], [169, 135, 63, 252], [243, 217, 68, 188, 206, 254, 106, 228], [161, 105, 77, 39], [241, 92, 142, 84], [172, 203, 178, 202]]]
 h' := ![![[118, 261, 36, 153, 245], [182, 106, 244, 66, 275], [121, 157, 105, 202, 56], [245, 204, 179, 15, 201], [64, 87, 26, 72, 180], [165, 158, 150, 16, 262], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[77, 234, 239, 272, 230], [117, 194, 2, 238, 174], [59, 245, 276, 195, 188], [206, 88, 216, 108, 214], [111, 216, 253, 77, 179], [246, 20, 217, 74, 184], [83, 63, 75, 51, 29], [16, 74, 124, 138, 122], [118, 261, 36, 153, 245]], ![[153, 218, 121, 43, 136], [195, 8, 211, 171, 26], [256, 196, 163, 81, 249], [232, 48, 116, 225, 131], [129, 166, 73, 262, 121], [166, 146, 190, 46, 237], [245, 144, 123, 26, 263], [24, 170, 259, 100, 237], [77, 234, 239, 272, 230]], ![[132, 117, 158, 86, 220], [259, 244, 23, 37, 154], [263, 143, 33, 265, 81], [24, 142, 99, 91, 38], [73, 240, 83, 224, 51], [105, 249, 219, 5, 268], [59, 168, 173, 79, 37], [22, 107, 269, 207, 176], [153, 218, 121, 43, 136]], ![[0, 1], [31, 2, 74, 42, 202], [258, 90, 254, 88, 257], [124, 72, 221, 115, 247], [0, 122, 119, 196, 23], [148, 258, 55, 136, 157], [142, 179, 183, 121, 224], [32, 203, 178, 109, 19], [132, 117, 158, 86, 220]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 208, 241, 119], [], [], []]
 b := ![[], [175, 24, 90, 40, 47], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 5
  hpos := by decide
  P := [114, 97, 211, 198, 74, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3998213184078, -2341792326948, -768929525328, -4058832435806, 2215459709838]
  a := ![0, -12, 0, -22, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14433982614, -8454123924, -2775918864, -14652824678, 7998049494]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 1630793025157 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def PBC277 : ContainsPrimesAboveP 277 ![I277N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![277, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 277 (by decide) 𝕀

instance hp281 : Fact (Nat.Prime 281) := {out := by norm_num}

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1167, 1403, 882, -173, -253]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![1167, 1403, 882, -173, -253]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![77, 43, 84, 1, 0], ![116, 95, 129, 0, 1]] where
  M :=![![![1167, 1403, 882, -173, -253], ![-2024, 957, 3152, 166, -772], ![-3088, -1449, 791, 367, -137], ![464, -2153, -3392, 45, 868], ![-264, -909, -1018, 64, 275]]]
  hmulB := by decide  
  f := ![![![-2793, 905, -1764, -459, 541]], ![![4328, -1393, 2728, 718, -836]], ![![-3344, 1079, -2111, -557, 659]], ![![-1101, 357, -696, -182, 217]], ![![-1228, 399, -777, -203, 244]]]
  g := ![![![156, 117, 171, -173, -253], ![266, 239, 316, 166, -772], ![-55, -15, -44, 367, -137], ![-369, -308, -424, 45, 868], ![-132, -106, -149, 64, 275]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 3 2 8 [33, 137, 155, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [188, 208, 94], [219, 72, 187], [0, 1]]
 g := ![![[105, 103, 59], [144, 167], [243, 64], [133, 81, 256], [11, 177, 17], [210, 9], [126, 1], []], ![[197, 25, 188, 159], [222, 62], [243, 114], [63, 109, 24, 146], [207, 5, 130, 198], [92, 264], [158, 126], [59, 125]], ![[2, 134, 253, 208], [264, 170], [70, 43], [11, 48, 83, 235], [21, 27, 28, 229], [20, 137], [93, 271], [247, 125]]]
 h' := ![![[188, 208, 94], [17, 119, 79], [58, 175, 27], [107, 161, 8], [199, 180, 16], [253, 23, 110], [57, 127, 3], [0, 0, 1], [0, 1]], ![[219, 72, 187], [244, 69, 14], [71, 49, 129], [253, 50, 255], [209, 69, 88], [238, 91, 247], [203, 178, 71], [239, 246, 72], [188, 208, 94]], ![[0, 1], [264, 93, 188], [212, 57, 125], [67, 70, 18], [212, 32, 177], [228, 167, 205], [56, 257, 207], [189, 35, 208], [219, 72, 187]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [159, 139], []]
 b := ![[], [280, 236, 145], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 3
  hpos := by decide
  P := [33, 137, 155, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![425742, 137134, 345640, 787969, -1620639]
  a := ![13, 5, 5, 6, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![454613, 427812, 509675, 787969, -1620639]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 22188041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2793, -905, 1764, 459, -541]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![2793, -905, 1764, 459, -541]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![248, 197, 1, 0, 0], ![38, 234, 0, 1, 0], ![268, 25, 0, 0, 1]] where
  M :=![![![2793, -905, 1764, 459, -541], ![-4328, 1393, -2728, -718, 836], ![3344, -1079, 2111, 557, -659], ![-472, 105, -272, -115, 88], ![864, -283, 554, 156, -217]]]
  hmulB := by decide  
  f := ![![![-1167, -1403, -882, 173, 253]], ![![2024, -957, -3152, -166, 772]], ![![400, -1904, -2991, 35, 765]], ![![1526, -979, -2732, -115, 674]], ![![-932, -1420, -1118, 150, 309]]]
  g := ![![![-1093, -1574, 1764, 459, -541], ![1692, 2441, -2728, -718, 836], ![-1298, -1889, 2111, 557, -659], ![170, 279, -272, -115, 88], ![-300, -500, 554, 156, -217]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P1 : CertificateIrreducibleZModOfList' 281 2 2 8 [162, 194, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 280], [0, 1]]
 g := ![![[192, 85], [156], [249], [200, 58], [169, 40], [181], [263], [1]], ![[0, 196], [156], [249], [188, 223], [277, 241], [181], [263], [1]]]
 h' := ![![[87, 280], [76, 180], [45, 76], [196, 165], [160, 236], [64, 130], [217, 32], [119, 87], [0, 1]], ![[0, 1], [0, 101], [194, 205], [220, 116], [179, 45], [134, 151], [191, 249], [101, 194], [87, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [227]]
 b := ![[], [191, 254]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N1 : CertifiedPrimeIdeal' SI281N1 281 where
  n := 2
  hpos := by decide
  P := [162, 194, 1]
  hirr := P281P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31, -378, -25, -624, 144]
  a := ![-1, -2, 0, -3, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-31, 523, -25, -624, 144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N1 B_one_repr
lemma NI281N1 : Nat.card (O ⧸ I281N1) = 78961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N1
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![1167, 1403, 882, -173, -253]] ![![2793, -905, 1764, 459, -541]]
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

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1272629, 412856, -803922, -208541, 245869]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![-1272629, 412856, -803922, -208541, 245869]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![27, 46, 241, 1, 0], ![199, 166, 255, 0, 1]] where
  M :=![![![-1272629, 412856, -803922, -208541, 245869], ![1966952, -638665, 1242794, 321780, -379754], ![-1519016, 494598, -960445, -247235, 292793], ![187696, -64798, 120436, 27058, -34579], ![-386672, 131304, -247124, -57957, 72616]]]
  hmulB := by decide  
  f := ![![![-42767, 16830, 61914, 3617, -15101]], ![![-120808, -59975, 26426, 14504, -4250]], ![![-17000, -65068, -74479, 4299, 19631]], ![![-37703, -63444, -53515, 6310, 14651]], ![![-116099, -81970, -8205, 14909, 4608]]]
  g := ![![![-157491, -108864, -46792, -208541, 245869], ![243286, 168193, 72548, 321780, -379754], ![-187666, -129810, -56675, -247235, 292793], ![22397, 15656, 8541, 27058, -34579], ![-46899, -32710, -16949, -57957, 72616]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 3 2 8 [215, 245, 144, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 229, 268], [33, 53, 15], [0, 1]]
 g := ![![[193, 111, 66], [240, 125, 236], [162, 266], [162, 99, 93], [249, 99, 214], [206, 207], [139, 1], []], ![[269, 212, 99, 206], [138, 256, 113, 242], [100, 281], [200, 255, 209, 191], [254, 108, 203, 166], [271, 81], [31, 262], [67, 225]], ![[198, 158, 102, 42], [3, 54, 282, 36], [194, 207], [247, 227, 231, 199], [138, 56, 103, 7], [72, 199], [249, 86], [37, 225]]]
 h' := ![![[106, 229, 268], [189, 165, 42], [137, 7, 233], [262, 193, 41], [235, 124, 35], [175, 237, 110], [113, 256, 115], [0, 0, 1], [0, 1]], ![[33, 53, 15], [45, 12, 34], [0, 78, 75], [29, 26, 127], [99, 173, 278], [176, 179, 11], [150, 13, 274], [227, 172, 53], [106, 229, 268]], ![[0, 1], [262, 106, 207], [106, 198, 258], [201, 64, 115], [39, 269, 253], [139, 150, 162], [51, 14, 177], [209, 111, 229], [33, 53, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 222], []]
 b := ![[], [117, 44, 128], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 3
  hpos := by decide
  P := [215, 245, 144, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-667039, -408007, -104460, -696775, 382125]
  a := ![3, -4, 7, -8, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-204583, -112329, 248680, -696775, 382125]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 22665187 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-93, -85, -31, 13, 10]] i)))

def SI283N1: IdealEqSpanCertificate' Table ![![-93, -85, -31, 13, 10]] 
 ![![283, 0, 0, 0, 0], ![40, 1, 0, 0, 0], ![49, 0, 1, 0, 0], ![132, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![-93, -85, -31, 13, 10], ![80, -87, -196, -5, 49], ![196, 67, -82, -22, 17], ![28, 154, 187, -9, -49], ![36, 60, 51, -6, -14]]]
  hmulB := by decide  
  f := ![![![-303, -232, -19, -329, 100]], ![![-40, -31, -2, -43, 11]], ![![-65, -48, -5, -69, 21]], ![![-128, -101, -5, -138, 32]], ![![-72, -49, -7, -71, 17]]]
  g := ![![![10, -85, -31, 13, 10], ![44, -87, -196, -5, 49], ![14, 67, -82, -22, 17], ![-45, 154, 187, -9, -49], ![-13, 60, 51, -6, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N1 : Nat.card (O ⧸ I283N1) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N1)

lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := prime_ideal_of_norm_prime hp283.out _ NI283N1

def I283N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5611, -1415, 3120, 619, -687]] i)))

def SI283N2: IdealEqSpanCertificate' Table ![![-5611, -1415, 3120, 619, -687]] 
 ![![283, 0, 0, 0, 0], ![44, 1, 0, 0, 0], ![164, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![-5611, -1415, 3120, 619, -687], ![-5496, -6545, -4068, 812, 1170], ![4680, -2263, -7357, -379, 1803], ![9960, 6631, 150, -1263, -252], ![3936, 1891, -948, -470, 161]]]
  hmulB := by decide  
  f := ![![![10655, -2035, 6018, 3011, -2427]], ![![1588, -311, 900, 440, -354]], ![![6268, -1159, 3521, 1805, -1437]], ![![1757, -398, 1020, 432, -357]], ![![3266, -491, 1776, 1036, -763]]]
  g := ![![![-1516, -1415, 3120, 619, -687], ![2876, -6545, -4068, 812, 1170], ![4175, -2263, -7357, -379, 1803], ![-791, 6631, 150, -1263, -252], ![304, 1891, -948, -470, 161]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N2 : Nat.card (O ⧸ I283N2) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N2)

lemma isPrimeI283N2 : Ideal.IsPrime I283N2 := prime_ideal_of_norm_prime hp283.out _ NI283N2
def MulI283N0 : IdealMulLeCertificate' Table 
  ![![-1272629, 412856, -803922, -208541, 245869]] ![![-93, -85, -31, 13, 10]]
  ![![-3173599, 1029045, -2004521, -520518, 613323]] where
 M := ![![![-3173599, 1029045, -2004521, -520518, 613323]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI283N1 : IdealMulLeCertificate' Table 
  ![![-3173599, 1029045, -2004521, -520518, 613323]] ![![-5611, -1415, 3120, 619, -687]]
  ![![283, 0, 0, 0, 0]] where
 M := ![![![-45563, 13018, -30847, -7358, 9339]]]
 hmul := by decide  
 g := ![![![![-161, 46, -109, -26, 33]]]]
 hle2 := by decide  


def PBC283 : ContainsPrimesAboveP 283 ![I283N0, I283N1, I283N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI283N0
    exact isPrimeI283N1
    exact isPrimeI283N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 283 (by decide) (𝕀 ⊙ MulI283N0 ⊙ MulI283N1)
instance hp293 : Fact (Nat.Prime 293) := {out := by norm_num}

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1681, 556, -1066, -264, 312]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![-1681, 556, -1066, -264, 312]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![0, 0, 0, 293, 0], ![112, 276, 21, 202, 1]] where
  M :=![![![-1681, 556, -1066, -264, 312], ![2496, -923, 1640, 316, -480], ![-1920, 710, -1239, -198, 234], ![-312, -434, 88, -479, 60], ![-392, 206, -220, 172, -443]]]
  hmulB := by decide  
  f := ![![![43, -8, -50, -4, 12]], ![![96, 57, -8, -12, 0]], ![![0, 50, 69, -2, -18]], ![![-120, -38, 56, 13, -12]], ![![24, 28, 17, -4, -5]]]
  g := ![![![-125, -292, -26, -216, 312], ![192, 449, 40, 332, -480], ![-96, -218, -21, -162, 234], ![-24, -58, -4, -43, 60], ![168, 418, 31, 306, -443]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 4 2 8 [213, 181, 178, 220, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [199, 46, 43, 45], [200, 270, 24, 129], [260, 269, 226, 119], [0, 1]]
 g := ![![[138, 254, 28, 211], [36, 109, 210], [155, 253, 212, 197], [49, 277, 292], [149, 157, 150], [244, 9, 2, 55], [1], []], ![[154, 222, 131, 244, 8, 159], [256, 63, 238], [69, 5, 91, 79, 223, 47], [173, 75, 278], [7, 98, 256], [12, 231, 287, 141, 220, 218], [112, 286, 169], [162, 214, 267]], ![[51, 98, 36, 132, 198, 192], [105, 250, 255], [79, 269, 169, 146, 160, 63], [78, 44, 149], [31, 56, 124], [211, 244, 238, 188, 39, 163], [55, 169, 10], [181, 54, 233]], ![[155, 226, 220, 158, 100, 194], [168, 291, 156], [178, 12, 188, 166, 81, 120], [59, 180, 59], [149, 103, 82], [176, 92, 138, 143, 241, 86], [148, 210, 209], [62, 218, 97]]]
 h' := ![![[199, 46, 43, 45], [289, 284, 92, 176], [94, 102, 93, 260], [42, 31, 153, 37], [215, 85, 169, 138], [182, 167, 268, 210], [80, 112, 115, 73], [0, 0, 1], [0, 1]], ![[200, 270, 24, 129], [114, 81, 271, 259], [281, 95, 115, 112], [279, 11, 178, 189], [33, 215, 268, 211], [135, 200, 60, 16], [274, 96, 85, 168], [114, 246, 269, 13], [199, 46, 43, 45]], ![[260, 269, 226, 119], [123, 70, 241, 39], [147, 247, 59, 264], [61, 200, 181, 220], [45, 133, 46, 102], [74, 159, 282, 36], [36, 0, 189, 96], [275, 156, 255, 204], [200, 270, 24, 129]], ![[0, 1], [46, 151, 275, 112], [233, 142, 26, 243], [181, 51, 74, 140], [191, 153, 103, 135], [172, 60, 269, 31], [95, 85, 197, 249], [189, 184, 61, 76], [260, 269, 226, 119]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [157, 133, 191], []]
 b := ![[], [], [243, 182, 206, 103], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 4
  hpos := by decide
  P := [213, 181, 178, 220, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-293422887, -125510241, -154984857, -440791326, 706318461]
  a := ![1, -4, -4, -5, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-270993483, -665765889, -51152466, -488454336, 706318461]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 7370050801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, -8, -50, -4, 12]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![43, -8, -50, -4, 12]] 
 ![![293, 0, 0, 0, 0], ![272, 1, 0, 0, 0], ![219, 0, 1, 0, 0], ![259, 0, 0, 1, 0], ![85, 0, 0, 0, 1]] where
  M :=![![![43, -8, -50, -4, 12], ![96, 57, -8, -12, 0], ![0, 50, 69, -2, -18], ![-120, -38, 56, 13, -12], ![-40, -6, 28, 4, -7]]]
  hmulB := by decide  
  f := ![![![-1681, 556, -1066, -264, 312]], ![![-1552, 513, -984, -244, 288]], ![![-1263, 418, -801, -198, 234]], ![![-1487, 490, -942, -235, 276]], ![![-489, 162, -310, -76, 89]]]
  g := ![![![45, -8, -50, -4, 12], ![-36, 57, -8, -12, 0], ![-91, 50, 69, -2, -18], ![-15, -38, 56, 13, -12], ![-17, -6, 28, 4, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N1 : Nat.card (O ⧸ I293N1) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N1)

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := prime_ideal_of_norm_prime hp293.out _ NI293N1
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![-1681, 556, -1066, -264, 312]] ![![43, -8, -50, -4, 12]]
  ![![293, 0, 0, 0, 0]] where
 M := ![![![293, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![323, 48, -187, 119, -24]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![323, 48, -187, 119, -24]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![293, 208, 67, 1, 0], ![109, 6, 33, 0, 1]] where
  M :=![![![323, 48, -187, 119, -24], ![-192, -103, -142, -661, 333], ![1332, 996, 558, 1354, -825], ![-3204, -1743, -287, -2676, 1452], ![3628, 2197, 851, 3879, -2147]]]
  hmulB := by decide  
  f := ![![![-1927, 609, -1207, -325, 360]], ![![2880, -1009, 1868, 431, -615]], ![![-2460, 621, -1440, -500, 339]], ![![-425, 32, -200, -128, 0]], ![![-897, 262, -548, -163, 151]]]
  g := ![![![-104, -80, -24, 119, -24], ![512, 441, 108, -661, 333], ![-995, -898, -205, 1354, -825], ![2028, 1779, 427, -2676, 1452], ![-2928, -2579, -613, 3879, -2147]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 3 2 8 [70, 118, 167, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [203, 108, 43], [244, 198, 264], [0, 1]]
 g := ![![[212, 47, 222], [246, 105, 275], [226, 215], [50, 60], [206, 50, 284], [103, 71, 233], [140, 1], []], ![[31, 14, 212, 73], [119, 159, 27, 267], [52, 276], [105, 280], [153, 92, 100, 221], [27, 52, 168, 45], [21, 215], [137, 7]], ![[117, 160, 19, 262], [99, 286, 2, 299], [111, 191], [140, 294], [122, 246, 178, 201], [16, 171, 171, 260], [79, 305], [223, 7]]]
 h' := ![![[203, 108, 43], [279, 213, 23], [66, 172, 182], [265, 108, 109], [9, 226, 260], [158, 30, 208], [24, 295, 141], [0, 0, 1], [0, 1]], ![[244, 198, 264], [185, 36, 205], [234, 260, 145], [174, 148, 131], [238, 172, 105], [306, 245, 108], [69, 188, 79], [305, 176, 198], [203, 108, 43]], ![[0, 1], [22, 58, 79], [227, 182, 287], [177, 51, 67], [253, 216, 249], [91, 32, 298], [7, 131, 87], [25, 131, 108], [244, 198, 264]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 136], []]
 b := ![[], [51, 300, 261], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 3
  hpos := by decide
  P := [70, 118, 167, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![446, 172, -2632, -2437, 9501]
  a := ![4, 1, -1, 2, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1046, 1466, -498, -2437, 9501]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 28934443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3683, 1316, -2385, -490, 663]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![-3683, 1316, -2385, -490, 663]] 
 ![![307, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![299, 0, 0, 1, 0], ![172, 0, 0, 0, 1]] where
  M :=![![![-3683, 1316, -2385, -490, 663], ![5304, -2263, 3612, 361, -807], ![-3228, 2260, -2624, 607, 138], ![-2100, -1753, -153, -2625, 1383], ![2604, 2597, -15, 3650, -1880]]]
  hmulB := by decide  
  f := ![![![29119, 61561, 58677, -5372, -15801]], ![![1011, 3054, 3303, -223, -876]], ![![3473, 7954, 7843, -665, -2103]], ![![28595, 59721, 56610, -5246, -15255]], ![![16336, 34376, 32697, -3007, -8807]]]
  g := ![![![348, 1316, -2385, -490, 663], ![-254, -2263, 3612, 361, -807], ![-439, 2260, -2624, 607, 138], ![1881, -1753, -153, -2625, 1383], ![-2618, 2597, -15, 3650, -1880]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N1 : Nat.card (O ⧸ I307N1) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N1)

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := prime_ideal_of_norm_prime hp307.out _ NI307N1

def I307N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, -83, -176, 2, 48]] i)))

def SI307N2: IdealEqSpanCertificate' Table ![![67, -83, -176, 2, 48]] 
 ![![307, 0, 0, 0, 0], ![158, 1, 0, 0, 0], ![105, 0, 1, 0, 0], ![222, 0, 0, 1, 0], ![273, 0, 0, 0, 1]] where
  M :=![![![67, -83, -176, 2, 48], ![384, 129, -170, -18, 54], ![216, 251, 147, 28, 0], ![-192, 103, 308, 142, 15], ![248, 261, 118, 253, 170]]]
  hmulB := by decide  
  f := ![![![643777, 377111, 124138, 654426, -359304]], ![![321962, 188601, 62082, 327290, -179694]], ![![241083, 141214, 46491, 245064, -134550]], ![![423570, 248135, 81668, 430592, -236409]], ![![631739, 370036, 121828, 642167, -352576]]]
  g := ![![![59, -83, -176, 2, 48], ![-42, 129, -170, -18, 54], ![-199, 251, 147, 28, 0], ![-275, 103, 308, 142, 15], ![-508, 261, 118, 253, 170]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N2 : Nat.card (O ⧸ I307N2) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N2)

lemma isPrimeI307N2 : Ideal.IsPrime I307N2 := prime_ideal_of_norm_prime hp307.out _ NI307N2
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![323, 48, -187, 119, -24]] ![![-3683, 1316, -2385, -490, 663]]
  ![![-643777, -377111, -124138, -654426, 359304]] where
 M := ![![![-643777, -377111, -124138, -654426, 359304]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI307N1 : IdealMulLeCertificate' Table 
  ![![-643777, -377111, -124138, -654426, 359304]] ![![67, -83, -176, 2, 48]]
  ![![307, 0, 0, 0, 0]] where
 M := ![![![-307, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC307 : ContainsPrimesAboveP 307 ![I307N0, I307N1, I307N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI307N0
    exact isPrimeI307N1
    exact isPrimeI307N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 307 (by decide) (𝕀 ⊙ MulI307N0 ⊙ MulI307N1)


lemma PB1072I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB1072I6 : PrimesBelowBoundCertificateInterval O 251 307 1072 where
  m := 9
  g := ![3, 3, 3, 3, 1, 2, 3, 2, 3]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB1072I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1, I257N2]
    · exact ![I263N0, I263N1, I263N2]
    · exact ![I269N0, I269N1, I269N2]
    · exact ![I271N0, I271N1, I271N2]
    · exact ![I277N0]
    · exact ![I281N0, I281N1]
    · exact ![I283N0, I283N1, I283N2]
    · exact ![I293N0, I293N1]
    · exact ![I307N0, I307N1, I307N2]
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
    · exact ![18191447, 263, 263]
    · exact ![19465109, 269, 269]
    · exact ![73441, 73441, 271]
    · exact ![1630793025157]
    · exact ![22188041, 78961]
    · exact ![22665187, 283, 283]
    · exact ![7370050801, 293]
    · exact ![28934443, 307, 307]
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
      exact NI263N1
      exact NI263N2
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
      exact NI269N2
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
      exact NI271N2
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
      exact NI281N1
    · dsimp ; intro j
      fin_cases j
      exact NI283N0
      exact NI283N1
      exact NI283N2
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
      exact NI307N2
  β := ![I257N1, I257N2, I263N1, I263N2, I269N1, I269N2, I271N2, I283N1, I283N2, I293N1, I307N1, I307N2]
  Il := ![[I257N1, I257N2], [I263N1, I263N2], [I269N1, I269N2], [I271N2], [], [], [I283N1, I283N2], [I293N1], [I307N1, I307N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
