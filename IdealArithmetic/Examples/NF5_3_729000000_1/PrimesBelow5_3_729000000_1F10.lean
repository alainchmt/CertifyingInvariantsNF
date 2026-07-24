
import IdealArithmetic.Examples.NF5_3_729000000_1.RI5_3_729000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp467 : Fact (Nat.Prime 467) := {out := by norm_num}

def I467N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![471, 164, 32, 45, -91]] i)))

def SI467N0: IdealEqSpanCertificate' Table ![![471, 164, 32, 45, -91]] 
 ![![467, 0, 0, 0, 0], ![0, 467, 0, 0, 0], ![216, 149, 1, 0, 0], ![144, 137, 0, 1, 0], ![337, 144, 0, 0, 1]] where
  M :=![![![471, 164, 32, 45, -91], ![-910, -325, -62, -89, 179], ![1790, 660, 121, 185, -355], ![100, 30, 6, 5, -14], ![1040, 386, 72, 108, -207]]]
  hmulB := by decide  
  f := ![![![37, 24, 10, 5, -13]], ![![-130, -51, -4, 43, 17]], ![![-24, -5, 3, 16, 0]], ![![-26, -7, 2, 14, 1]], ![![-13, 2, 6, 17, -4]]]
  g := ![![![38, 5, 32, 45, -91], ![-75, -10, -62, -89, 179], ![147, 18, 121, 185, -355], ![6, 1, 6, 5, -14], ![85, 10, 72, 108, -207]]]
  hle1 := by decide   
  hle2 := by decide  


def P467P0 : CertificateIrreducibleZModOfList' 467 2 2 8 [3, 303, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [164, 466], [0, 1]]
 g := ![![[101, 156], [171, 241], [52], [249], [182, 122], [362], [319, 356], [164, 1]], ![[0, 311], [0, 226], [52], [249], [109, 345], [362], [328, 111], [328, 466]]]
 h' := ![![[164, 466], [421, 211], [269, 360], [357, 156], [388, 222], [377, 271], [444, 36], [442, 274], [0, 1]], ![[0, 1], [0, 256], [0, 107], [256, 311], [370, 245], [456, 196], [277, 431], [79, 193], [164, 466]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [235, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI467N0 : CertifiedPrimeIdeal' SI467N0 467 where
  n := 2
  hpos := by decide
  P := [3, 303, 1]
  hirr := P467P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25683, 25933, 2741, 3935, 5019]
  a := ![0, -9, 16, 2, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6048, -3521, 2741, 3935, 5019]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI467N0 : Ideal.IsPrime I467N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI467N0 B_one_repr
lemma NI467N0 : Nat.card (O ⧸ I467N0) = 218089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI467N0

def I467N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-807, -1420, -84, -484, -706]] i)))

def SI467N1: IdealEqSpanCertificate' Table ![![-807, -1420, -84, -484, -706]] 
 ![![467, 0, 0, 0, 0], ![77, 1, 0, 0, 0], ![142, 0, 1, 0, 0], ![129, 0, 0, 1, 0], ![370, 0, 0, 0, 1]] where
  M :=![![![-807, -1420, -84, -484, -706], ![-7060, -9477, -674, -3180, -3610], ![-36100, -53320, -3547, -18000, -22690], ![-19160, -27404, -1864, -9233, -11264], ![-38840, -56584, -3800, -19086, -23731]]]
  hmulB := by decide  
  f := ![![![-9701, -5700, -812, 3232, 398]], ![![-1591, -953, -166, 512, 108]], ![![-2526, -1440, -155, 852, 38]], ![![-2767, -1584, -148, 975, 2]], ![![-7670, -4504, -640, 2554, 313]]]
  g := ![![![951, -1420, -84, -484, -706], ![5491, -9477, -674, -3180, -3610], ![32742, -53320, -3547, -18000, -22690], ![16519, -27404, -1864, -9233, -11264], ![34476, -56584, -3800, -19086, -23731]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI467N1 : Nat.card (O ⧸ I467N1) = 467 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI467N1)

lemma isPrimeI467N1 : Ideal.IsPrime I467N1 := prime_ideal_of_norm_prime hp467.out _ NI467N1

def I467N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1127, -330, -34, -69, 149]] i)))

def SI467N2: IdealEqSpanCertificate' Table ![![-1127, -330, -34, -69, 149]] 
 ![![467, 0, 0, 0, 0], ![353, 1, 0, 0, 0], ![80, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![185, 0, 0, 0, 1]] where
  M :=![![![-1127, -330, -34, -69, 149], ![1490, 273, 26, 325, -265], ![-2650, -970, -967, -1125, 1685], ![940, 856, 396, -343, -374], ![-2040, -644, -170, -206, 419]]]
  hmulB := by decide  
  f := ![![![412659, 603770, 40428, 203707, 254363]], ![![317371, 464127, 31088, 156588, 195432]], ![![102310, 148910, 10007, 50225, 62385]], ![![47015, 68306, 4596, 23036, 28561]], ![![196885, 287166, 19270, 96869, 120578]]]
  g := ![![![199, -330, -34, -69, 149], ![-127, 273, 26, 325, -265], ![310, -970, -967, -1125, 1685], ![-539, 856, 396, -343, -374], ![361, -644, -170, -206, 419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI467N2 : Nat.card (O ⧸ I467N2) = 467 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI467N2)

lemma isPrimeI467N2 : Ideal.IsPrime I467N2 := prime_ideal_of_norm_prime hp467.out _ NI467N2

def I467N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -6, 0, 0, -2]] i)))

def SI467N3: IdealEqSpanCertificate' Table ![![-7, -6, 0, 0, -2]] 
 ![![467, 0, 0, 0, 0], ![355, 1, 0, 0, 0], ![65, 0, 1, 0, 0], ![317, 0, 0, 1, 0], ![106, 0, 0, 0, 1]] where
  M :=![![![-7, -6, 0, 0, -2], ![-20, -29, -8, -8, -2], ![-20, -90, -7, -80, -50], ![-40, -54, 14, -15, -52], ![-100, -142, -10, -50, -57]]]
  hmulB := by decide  
  f := ![![![196539, 60850, 12724, 16172, -34946]], ![![148655, 46025, 9624, 12232, -26432]], ![![28685, 8880, 1857, 2360, -5100]], ![![133549, 41348, 8646, 10989, -23746]], ![![45382, 14050, 2938, 3734, -8069]]]
  g := ![![![5, -6, 0, 0, -2], ![29, -29, -8, -8, -2], ![135, -90, -7, -80, -50], ![61, -54, 14, -15, -52], ![156, -142, -10, -50, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI467N3 : Nat.card (O ⧸ I467N3) = 467 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI467N3)

lemma isPrimeI467N3 : Ideal.IsPrime I467N3 := prime_ideal_of_norm_prime hp467.out _ NI467N3
def MulI467N0 : IdealMulLeCertificate' Table 
  ![![471, 164, 32, 45, -91]] ![![-807, -1420, -84, -484, -706]]
  ![![-20897, -13324, -1684, -4143, 1995]] where
 M := ![![![-20897, -13324, -1684, -4143, 1995]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI467N1 : IdealMulLeCertificate' Table 
  ![![-20897, -13324, -1684, -4143, 1995]] ![![-1127, -330, -34, -69, 149]]
  ![![196539, 60850, 12724, 16172, -34946]] where
 M := ![![![196539, 60850, 12724, 16172, -34946]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI467N2 : IdealMulLeCertificate' Table 
  ![![196539, 60850, 12724, 16172, -34946]] ![![-7, -6, 0, 0, -2]]
  ![![467, 0, 0, 0, 0]] where
 M := ![![![467, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC467 : ContainsPrimesAboveP 467 ![I467N0, I467N1, I467N2, I467N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI467N0
    exact isPrimeI467N1
    exact isPrimeI467N2
    exact isPrimeI467N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 467 (by decide) (𝕀 ⊙ MulI467N0 ⊙ MulI467N1 ⊙ MulI467N2)
instance hp479 : Fact (Nat.Prime 479) := {out := by norm_num}

def I479N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![351, 469, 35, 135, 179]] i)))

def SI479N0: IdealEqSpanCertificate' Table ![![351, 469, 35, 135, 179]] 
 ![![479, 0, 0, 0, 0], ![0, 479, 0, 0, 0], ![0, 0, 479, 0, 0], ![30, 20, 309, 1, 0], ![362, 25, 107, 0, 1]] where
  M :=![![![351, 469, 35, 135, 179], ![1790, 2630, 243, 931, 989], ![9890, 14815, 826, 5455, 6575], ![5680, 7865, 381, 2445, 3436], ![11320, 16251, 1097, 5498, 6713]]]
  hmulB := by decide  
  f := ![![![18409, 5843, 1203, 1565, -3331]], ![![-33310, -10652, -2183, -2859, 6059]], ![![60590, 19565, 3984, 5265, -11095]], ![![38860, 12546, 2555, 3376, -7115]], ![![25782, 8254, 1690, 2216, -4693]]]
  g := ![![![-143, -14, -127, 135, 179], ![-802, -85, -821, 931, 989], ![-5290, -540, -4986, 5455, 6575], ![-2738, -265, -2344, 2445, 3436], ![-5394, -546, -5044, 5498, 6713]]]
  hle1 := by decide   
  hle2 := by decide  


def P479P0 : CertificateIrreducibleZModOfList' 479 3 2 8 [112, 312, 183, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [110, 225, 384], [186, 253, 95], [0, 1]]
 g := ![![[76, 62, 230], [141, 150, 131], [100, 468, 197], [14, 149, 422], [27, 35, 97], [249, 23], [205, 29, 438], [1]], ![[231, 38, 265, 4], [243, 108, 304, 75], [213, 240, 212, 392], [462, 473, 221, 220], [48, 306, 3, 108], [308, 321], [431, 281, 34, 271], [350, 219, 254, 35]], ![[457, 126, 89, 113], [190, 304, 118, 367], [369, 395, 328, 199], [442, 250, 33, 299], [243, 292, 445, 208], [369, 412], [361, 67, 172, 430], [30, 423, 453, 444]]]
 h' := ![![[110, 225, 384], [15, 0, 250], [296, 126, 33], [348, 7, 453], [329, 273, 204], [439, 328, 455], [32, 421, 135], [367, 167, 296], [0, 1]], ![[186, 253, 95], [332, 127, 22], [98, 146, 211], [219, 6, 421], [456, 117, 290], [280, 428, 130], [328, 421, 387], [416, 463, 106], [110, 225, 384]], ![[0, 1], [140, 352, 207], [38, 207, 235], [200, 466, 84], [435, 89, 464], [123, 202, 373], [89, 116, 436], [442, 328, 77], [186, 253, 95]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [413, 475], []]
 b := ![[], [298, 316, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N0 : CertifiedPrimeIdeal' SI479N0 479 where
  n := 3
  hpos := by decide
  P := [112, 312, 183, 1]
  hirr := P479P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15539392018, -21618752862, -666607596, -6784322808, -10129157106]
  a := ![3, -125, 119, -69, -298]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8047484686, 766798812, 6637805742, -6784322808, -10129157106]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI479N0 : Ideal.IsPrime I479N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI479N0 B_one_repr
lemma NI479N0 : Nat.card (O ⧸ I479N0) = 109902239 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI479N0

def I479N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18409, -5843, -1203, -1565, 3331]] i)))

def SI479N1: IdealEqSpanCertificate' Table ![![-18409, -5843, -1203, -1565, 3331]] 
 ![![479, 0, 0, 0, 0], ![0, 479, 0, 0, 0], ![477, 263, 1, 0, 0], ![340, 460, 0, 1, 0], ![209, 60, 0, 0, 1]] where
  M :=![![![-18409, -5843, -1203, -1565, 3331], ![33310, 10652, 2183, 2859, -6059], ![-60590, -19565, -3984, -5265, 11095], ![-5560, -1699, -359, -449, 980], ![-35140, -11345, -2311, -3054, 6435]]]
  hmulB := by decide  
  f := ![![![-351, -469, -35, -135, -179]], ![![-1790, -2630, -243, -931, -989]], ![![-1353, -1942, -170, -657, -735]], ![![-1980, -2875, -259, -995, -1084]], ![![-401, -568, -48, -187, -216]]]
  g := ![![![817, 1734, -1203, -1565, 3331], ![-1490, -3163, 2183, 2859, -6059], ![2737, 5813, -3984, -5265, 11095], ![237, 502, -359, -449, 980], ![1588, 3372, -2311, -3054, 6435]]]
  hle1 := by decide   
  hle2 := by decide  


def P479P1 : CertificateIrreducibleZModOfList' 479 2 2 8 [428, 427, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 478], [0, 1]]
 g := ![![[264, 216], [18, 276], [426, 305], [207, 300], [410, 21], [378], [295, 270], [52, 1]], ![[0, 263], [0, 203], [0, 174], [0, 179], [65, 458], [378], [444, 209], [104, 478]]]
 h' := ![![[52, 478], [439, 185], [171, 227], [19, 451], [313, 169], [214, 220], [196, 317], [257, 360], [0, 1]], ![[0, 1], [0, 294], [0, 252], [0, 28], [0, 310], [158, 259], [394, 162], [296, 119], [52, 478]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [338]]
 b := ![[], [396, 169]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI479N1 : CertifiedPrimeIdeal' SI479N1 479 where
  n := 2
  hpos := by decide
  P := [428, 427, 1]
  hirr := P479P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13636, 12319, 3293, 2513, -1083]
  a := ![1, -9, 11, -3, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4562, -4060, 3293, 2513, -1083]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI479N1 : Ideal.IsPrime I479N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI479N1 B_one_repr
lemma NI479N1 : Nat.card (O ⧸ I479N1) = 229441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI479N1
def MulI479N0 : IdealMulLeCertificate' Table 
  ![![351, 469, 35, 135, 179]] ![![-18409, -5843, -1203, -1565, 3331]]
  ![![479, 0, 0, 0, 0]] where
 M := ![![![-479, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC479 : ContainsPrimesAboveP 479 ![I479N0, I479N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI479N0
    exact isPrimeI479N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 479 (by decide) (𝕀 ⊙ MulI479N0)
instance hp487 : Fact (Nat.Prime 487) := {out := by norm_num}

def I487N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 238, 440, 251, -581]] i)))

def SI487N0: IdealEqSpanCertificate' Table ![![17, 238, 440, 251, -581]] 
 ![![487, 0, 0, 0, 0], ![0, 487, 0, 0, 0], ![0, 0, 487, 0, 0], ![451, 205, 44, 1, 0], ![199, 291, 61, 0, 1]] where
  M :=![![![17, 238, 440, 251, -581], ![-5810, -3923, -1096, 1825, 925], ![9250, 710, -8473, -9085, 11875], ![14780, 10804, 4532, -3727, -4726], ![180, -236, -422, -444, 481]]]
  hmulB := by decide  
  f := ![![![-139209, -66014, -10786, -19453, 33953]], ![![339530, 160891, 26298, 47405, -82765]], ![![-827650, -391990, -64089, -115485, 201665]], ![![-60707, -28793, -4704, -8485, 14808]], ![![41347, 19599, 3203, 5775, -10082]]]
  g := ![![![5, 242, 51, 251, -581], ![-2080, -1329, -283, 1825, 925], ![3580, -3270, -684, -9085, 11875], ![5413, 4415, 938, -3727, -4726], ![215, -101, -21, -444, 481]]]
  hle1 := by decide   
  hle2 := by decide  


def P487P0 : CertificateIrreducibleZModOfList' 487 3 2 8 [413, 164, 327, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 122, 242], [146, 364, 245], [0, 1]]
 g := ![![[66, 381, 430], [261, 95, 8], [331, 33, 461], [415, 334], [319, 313], [102, 166, 214], [213, 446, 276], [1]], ![[327, 357, 134, 91], [235, 102, 263, 89], [107, 409, 296, 259], [143, 142], [263, 408], [406, 231, 298, 264], [246, 383, 117, 235], [397, 458, 40, 301]], ![[327, 483, 124, 88], [318, 227, 341, 246], [283, 220, 256, 227], [316, 41], [356, 69], [341, 415, 359, 436], [270, 309, 298, 344], [388, 401, 75, 186]]]
 h' := ![![[14, 122, 242], [321, 59, 291], [144, 461, 182], [235, 324, 386], [352, 98, 373], [243, 455, 359], [178, 139, 431], [74, 323, 160], [0, 1]], ![[146, 364, 245], [81, 452, 400], [422, 31, 55], [112, 297, 249], [289, 290, 239], [371, 367, 208], [428, 351, 105], [467, 99, 46], [14, 122, 242]], ![[0, 1], [226, 463, 283], [365, 482, 250], [471, 353, 339], [108, 99, 362], [190, 152, 407], [243, 484, 438], [185, 65, 281], [146, 364, 245]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 336], []]
 b := ![[], [211, 253, 224], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI487N0 : CertifiedPrimeIdeal' SI487N0 487 where
  n := 3
  hpos := by decide
  P := [413, 164, 327, 1]
  hirr := P487P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1386746105, 1806237616, 46399056, 474586909, 830594847]
  a := ![1, 45, -57, 10, 141]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-776058161, -692376138, -146820761, 474586909, 830594847]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI487N0 : Ideal.IsPrime I487N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI487N0 B_one_repr
lemma NI487N0 : Nat.card (O ⧸ I487N0) = 115501303 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI487N0

def I487N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139209, 66014, 10786, 19453, -33953]] i)))

def SI487N1: IdealEqSpanCertificate' Table ![![139209, 66014, 10786, 19453, -33953]] 
 ![![487, 0, 0, 0, 0], ![0, 487, 0, 0, 0], ![164, 47, 1, 0, 0], ![398, 283, 0, 1, 0], ![205, 193, 0, 0, 1]] where
  M :=![![![139209, 66014, 10786, 19453, -33953], ![-339530, -160891, -26298, -47405, 82765], ![827650, 391990, 64089, 115485, -201665], ![-31900, -15028, -2464, -4423, 7742], ![478000, 226392, 37014, 66698, -116469]]]
  hmulB := by decide  
  f := ![![![-17, -238, -440, -251, 581]], ![![5810, 3923, 1096, -1825, -925]], ![![536, 297, -25, -242, 82]], ![![3332, 2063, 268, -1258, -53]], ![![2295, 1455, 250, -828, -123]]]
  g := ![![![-4952, 1246, 10786, 19453, -33953], ![12061, -3045, -26298, -47405, 82765], ![-29373, 7431, 64089, 115485, -201665], ![1120, -291, -2464, -4423, 7742], ![-16965, 4291, 37014, 66698, -116469]]]
  hle1 := by decide   
  hle2 := by decide  


def P487P1 : CertificateIrreducibleZModOfList' 487 2 2 8 [171, 353, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [134, 486], [0, 1]]
 g := ![![[22, 356], [405, 444], [89, 162], [31], [475], [243, 477], [174, 212], [134, 1]], ![[0, 131], [0, 43], [369, 325], [31], [475], [364, 10], [336, 275], [268, 486]]]
 h' := ![![[134, 486], [386, 48], [365, 328], [334, 155], [231, 121], [329, 443], [440, 351], [462, 253], [0, 1]], ![[0, 1], [0, 439], [0, 159], [163, 332], [374, 366], [277, 44], [235, 136], [274, 234], [134, 486]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [228, 251]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI487N1 : CertifiedPrimeIdeal' SI487N1 487 where
  n := 2
  hpos := by decide
  P := [171, 353, 1]
  hirr := P487P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41579, 37278, 6662, 1718, -340]
  a := ![-1, -6, 21, 13, -50]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3419, -1430, 6662, 1718, -340]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI487N1 : Ideal.IsPrime I487N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI487N1 B_one_repr
lemma NI487N1 : Nat.card (O ⧸ I487N1) = 237169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI487N1
def MulI487N0 : IdealMulLeCertificate' Table 
  ![![17, 238, 440, 251, -581]] ![![139209, 66014, 10786, 19453, -33953]]
  ![![487, 0, 0, 0, 0]] where
 M := ![![![-487, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC487 : ContainsPrimesAboveP 487 ![I487N0, I487N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI487N0
    exact isPrimeI487N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 487 (by decide) (𝕀 ⊙ MulI487N0)
instance hp491 : Fact (Nat.Prime 491) := {out := by norm_num}

def I491N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1949, -656, -132, -176, 368]] i)))

def SI491N0: IdealEqSpanCertificate' Table ![![-1949, -656, -132, -176, 368]] 
 ![![491, 0, 0, 0, 0], ![0, 491, 0, 0, 0], ![0, 0, 491, 0, 0], ![354, 190, 252, 1, 0], ![152, 452, 371, 0, 1]] where
  M :=![![![-1949, -656, -132, -176, 368], ![3680, 1263, 240, 328, -688], ![-6880, -2360, -409, -680, 1280], ![-560, -184, -24, 7, 64], ![-4040, -1416, -272, -392, 783]]]
  hmulB := by decide  
  f := ![![![-39, -48, -4, -16, -16]], ![![-160, -251, -16, -88, -112]], ![![-1120, -1560, -99, -520, -640]], ![![-666, -934, -60, -313, -384]], ![![-1008, -1428, -91, -480, -593]]]
  g := ![![![9, -272, -188, -176, 368], ![-16, 509, 352, 328, -688], ![80, -920, -619, -680, 1280], ![-26, -62, -52, 7, 64], ![32, -572, -391, -392, 783]]]
  hle1 := by decide   
  hle2 := by decide  


def P491P0 : CertificateIrreducibleZModOfList' 491 3 2 8 [214, 94, 454, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [203, 62, 484], [325, 428, 7], [0, 1]]
 g := ![![[61, 258, 469], [166, 119, 300], [277, 233], [219, 69, 320], [270, 38], [289, 343, 438], [247, 489, 387], [1]], ![[457, 45, 60, 43], [134, 480, 361, 68], [476, 75], [323, 266, 357, 215], [1, 93], [490, 436, 227, 407], [365, 99, 47, 361], [11, 238, 351, 148]], ![[262, 398, 313, 67], [461, 411, 396, 50], [34, 389], [369, 186], [290, 349], [344, 241, 217, 339], [54, 284, 135, 385], [17, 423, 484, 343]]]
 h' := ![![[203, 62, 484], [319, 338, 173], [365, 198, 343], [270, 70, 235], [67, 105, 297], [20, 18, 23], [170, 420, 129], [277, 397, 37], [0, 1]], ![[325, 428, 7], [445, 306, 483], [229, 445, 82], [203, 198, 417], [432, 218, 194], [367, 65, 389], [42, 121, 226], [361, 444, 291], [203, 62, 484]], ![[0, 1], [481, 338, 326], [470, 339, 66], [101, 223, 330], [333, 168], [6, 408, 79], [265, 441, 136], [150, 141, 163], [325, 428, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 467], []]
 b := ![[], [74, 115, 207], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI491N0 : CertifiedPrimeIdeal' SI491N0 491 where
  n := 3
  hpos := by decide
  P := [214, 94, 454, 1]
  hirr := P491P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21352054, 21780860, 8287868, -257996, -4668072]
  a := ![0, -2, -18, -26, 44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1674602, 4441484, 3676492, -257996, -4668072]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI491N0 : Ideal.IsPrime I491N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI491N0 B_one_repr
lemma NI491N0 : Nat.card (O ⧸ I491N0) = 118370771 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI491N0

def I491N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, 48, 4, 16, 16]] i)))

def SI491N1: IdealEqSpanCertificate' Table ![![39, 48, 4, 16, 16]] 
 ![![491, 0, 0, 0, 0], ![0, 491, 0, 0, 0], ![366, 426, 1, 0, 0], ![415, 302, 0, 1, 0], ![79, 331, 0, 0, 1]] where
  M :=![![![39, 48, 4, 16, 16], ![160, 251, 16, 88, 112], ![1120, 1560, 99, 520, 640], ![560, 792, 56, 259, 320], ![1160, 1640, 112, 552, 667]]]
  hmulB := by decide  
  f := ![![![1949, 656, 132, 176, -368]], ![![-3680, -1263, -240, -328, 688]], ![![-1726, -602, -109, -152, 320]], ![![-615, -222, -36, -53, 112]], ![![-2159, -743, -140, -192, 403]]]
  g := ![![![-19, -24, 4, 16, 16], ![-104, -143, 16, 88, 112], ![-614, -834, 99, 520, 640], ![-311, -422, 56, 259, 320], ![-655, -883, 112, 552, 667]]]
  hle1 := by decide   
  hle2 := by decide  


def P491P1 : CertificateIrreducibleZModOfList' 491 2 2 8 [65, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [423, 490], [0, 1]]
 g := ![![[205, 68], [97, 413], [238], [456, 325], [302], [227, 65], [54, 451], [423, 1]], ![[0, 423], [0, 78], [238], [451, 166], [302], [226, 426], [319, 40], [355, 490]]]
 h' := ![![[423, 490], [78, 160], [236, 119], [311, 27], [144, 317], [466, 398], [418, 402], [1, 140], [0, 1]], ![[0, 1], [0, 331], [0, 372], [439, 464], [192, 174], [407, 93], [87, 89], [301, 351], [423, 490]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [153, 250]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI491N1 : CertifiedPrimeIdeal' SI491N1 491 where
  n := 2
  hpos := by decide
  P := [65, 68, 1]
  hirr := P491P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![32158, 30182, 293, 517, 11418]
  a := ![13, -7, 18, 8, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2427, -8208, 293, 517, 11418]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI491N1 : Ideal.IsPrime I491N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI491N1 B_one_repr
lemma NI491N1 : Nat.card (O ⧸ I491N1) = 241081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI491N1
def MulI491N0 : IdealMulLeCertificate' Table 
  ![![-1949, -656, -132, -176, 368]] ![![39, 48, 4, 16, 16]]
  ![![491, 0, 0, 0, 0]] where
 M := ![![![-491, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC491 : ContainsPrimesAboveP 491 ![I491N0, I491N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI491N0
    exact isPrimeI491N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 491 (by decide) (𝕀 ⊙ MulI491N0)
instance hp499 : Fact (Nat.Prime 499) := {out := by norm_num}

def I499N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3509, -173, 195, -161, -1583]] i)))

def SI499N0: IdealEqSpanCertificate' Table ![![3509, -173, 195, -161, -1583]] 
 ![![499, 0, 0, 0, 0], ![0, 499, 0, 0, 0], ![0, 0, 499, 0, 0], ![271, 301, 102, 1, 0], ![299, 158, 358, 0, 1]] where
  M :=![![![3509, -173, 195, -161, -1583], ![-15830, -13090, -1273, -4221, -2549], ![-25490, -54455, -2976, -18705, -27875], ![-19960, -30025, -1985, -10145, -12736], ![-34660, -60071, -3661, -20448, -27903]]]
  hmulB := by decide  
  f := ![![![351, 73, -241, -291, 347]], ![![3470, 2672, 1293, -731, -1399]], ![![-13990, -6185, 3466, 8065, -5785]], ![![-591, 374, 1349, 1051, -1828]], ![![-8729, -3548, 2752, 5381, -4386]]]
  g := ![![![1043, 598, 1169, -161, -1583], ![3788, 3327, 2689, -4221, -2549], ![26810, 20000, 23816, -18705, -27875], ![13101, 10092, 11207, -10145, -12736], ![27755, 21049, 24191, -20448, -27903]]]
  hle1 := by decide   
  hle2 := by decide  


def P499P0 : CertificateIrreducibleZModOfList' 499 3 2 8 [233, 465, 146, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [170, 11, 28], [183, 487, 471], [0, 1]]
 g := ![![[222, 459, 43], [290, 27, 306], [464, 91], [254, 323], [40, 484, 47], [157, 191, 123], [340, 179, 358], [1]], ![[485, 384, 152, 274], [402, 174, 230, 27], [235, 119], [77, 46], [441, 258, 100, 357], [23, 472, 154, 272], [423, 378, 232, 19], [442, 372, 9, 495]], ![[39, 371, 251, 80], [377, 118, 207, 45], [146, 293], [229, 298], [176, 176, 352, 165], [149, 414, 191, 267], [184, 435, 184, 145], [125, 191, 134, 4]]]
 h' := ![![[170, 11, 28], [294, 369, 95], [314, 39, 362], [172, 42, 33], [161, 128, 193], [345, 426, 394], [121, 190, 401], [266, 34, 353], [0, 1]], ![[183, 487, 471], [283, 489, 210], [365, 456, 241], [472, 430, 281], [335, 117, 270], [263, 70, 214], [248, 310, 9], [153, 319, 209], [170, 11, 28]], ![[0, 1], [374, 140, 194], [79, 4, 395], [313, 27, 185], [144, 254, 36], [287, 3, 390], [366, 498, 89], [85, 146, 436], [183, 487, 471]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [187, 471], []]
 b := ![[], [184, 335, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI499N0 : CertifiedPrimeIdeal' SI499N0 499 where
  n := 3
  hpos := by decide
  P := [233, 465, 146, 1]
  hirr := P499P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18053, 67651, 99913, 23036, -117072]
  a := ![-1, -3, -3, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![57675, 23309, 79483, 23036, -117072]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI499N0 : Ideal.IsPrime I499N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI499N0 B_one_repr
lemma NI499N0 : Nat.card (O ⧸ I499N0) = 124251499 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI499N0

def I499N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-351, -73, 241, 291, -347]] i)))

def SI499N1: IdealEqSpanCertificate' Table ![![-351, -73, 241, 291, -347]] 
 ![![499, 0, 0, 0, 0], ![0, 499, 0, 0, 0], ![473, 477, 1, 0, 0], ![342, 199, 0, 1, 0], ![241, 310, 0, 0, 1]] where
  M :=![![![-351, -73, 241, 291, -347], ![-3470, -2672, -1293, 731, 1399], ![13990, 6185, -3466, -8065, 5785], ![7520, 6559, 4263, -711, -4960], ![560, 225, -185, -356, 295]]]
  hmulB := by decide  
  f := ![![![-3509, 173, -195, 161, 1583]], ![![15830, 13090, 1273, 4221, 2549]], ![![11857, 12786, 1038, 4225, 3993]], ![![3948, 5399, 378, 1814, 2127]], ![![8209, 8336, 704, 2741, 2404]]]
  g := ![![![-261, -131, 241, 291, -347], ![42, 70, -1293, 731, 1399], ![6047, 2948, -3466, -8065, 5785], ![-1143, -697, 4263, -711, -4960], ![278, 136, -185, -356, 295]]]
  hle1 := by decide   
  hle2 := by decide  


def P499P1 : CertificateIrreducibleZModOfList' 499 2 2 8 [340, 393, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 498], [0, 1]]
 g := ![![[167, 199], [234, 130], [451], [287], [280, 438], [34, 36], [77, 237], [106, 1]], ![[303, 300], [42, 369], [451], [287], [301, 61], [357, 463], [249, 262], [212, 498]]]
 h' := ![![[106, 498], [280, 295], [27, 396], [129, 381], [109, 423], [416, 278], [267, 6], [387, 417], [0, 1]], ![[0, 1], [113, 204], [87, 103], [96, 118], [37, 76], [443, 221], [404, 493], [178, 82], [106, 498]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [450, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI499N1 : CertifiedPrimeIdeal' SI499N1 499 where
  n := 2
  hpos := by decide
  P := [340, 393, 1]
  hirr := P499P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![82728, 86580, -12572, -5450, 66220]
  a := ![3, 10, -28, -15, 70]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16164, -26774, -12572, -5450, 66220]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI499N1 : Ideal.IsPrime I499N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI499N1 B_one_repr
lemma NI499N1 : Nat.card (O ⧸ I499N1) = 249001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI499N1
def MulI499N0 : IdealMulLeCertificate' Table 
  ![![3509, -173, 195, -161, -1583]] ![![-351, -73, 241, 291, -347]]
  ![![499, 0, 0, 0, 0]] where
 M := ![![![-499, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC499 : ContainsPrimesAboveP 499 ![I499N0, I499N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI499N0
    exact isPrimeI499N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 499 (by decide) (𝕀 ⊙ MulI499N0)
instance hp503 : Fact (Nat.Prime 503) := {out := by norm_num}

def I503N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-861, -248, 544, 695, -821]] i)))

def SI503N0: IdealEqSpanCertificate' Table ![![-861, -248, 544, 695, -821]] 
 ![![503, 0, 0, 0, 0], ![0, 503, 0, 0, 0], ![0, 0, 503, 0, 0], ![0, 0, 0, 503, 0], ![463, 450, 457, 398, 1]] where
  M :=![![![-861, -248, 544, 695, -821], ![-8210, -6477, -3154, 1461, 3349], ![33490, 14320, -7511, -19605, 12115], ![16220, 14198, 10102, -1435, -12226], ![440, -926, -500, -1360, -11]]]
  hmulB := by decide  
  f := ![![![-96523, -45660, -7470, -13449, 23497]], ![![234970, 111145, 18184, 32737, -57197]], ![![-571970, -270540, -44263, -79685, 139225]], ![![21740, 10278, 1682, 3027, -5290]], ![![-381753, -180572, -29543, -53186, 92925]]]
  g := ![![![754, 734, 747, 651, -821], ![-3099, -3009, -3049, -2647, 3349], ![-11085, -10810, -11022, -9625, 12115], ![11286, 10966, 11128, 9671, -12226], ![11, 8, 9, 6, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P503P0 : CertificateIrreducibleZModOfList' 503 4 2 8 [473, 468, 168, 242, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [190, 308, 53, 430], [432, 172, 333, 311], [142, 22, 117, 265], [0, 1]]
 g := ![![[174, 141, 408, 410], [98, 188, 450, 462], [134, 466, 489, 465], [354, 57, 484], [390, 339, 95, 145], [17, 227, 486, 233], [404, 48, 261, 1], []], ![[271, 104, 40, 429, 340, 135], [254, 231, 205, 288, 434, 251], [292, 282, 44, 144, 204, 90], [217, 44, 252], [484, 301, 320, 128, 353, 34], [75, 287, 68, 31, 149, 327], [53, 111, 52, 332, 250, 232], [81, 383, 429, 377, 390, 305]], ![[356, 443, 361, 252, 375, 331], [443, 243, 434, 49, 476, 385], [492, 179, 188, 190, 128, 103], [137, 51, 376], [299, 452, 333, 116, 440, 430], [344, 383, 219, 192, 25, 115], [462, 105, 216, 485, 156, 248], [92, 486, 411, 72, 89, 328]], ![[186, 250, 482, 109, 402, 169], [366, 67, 407, 59, 334, 79], [311, 228, 256, 317, 127, 384], [59, 219, 323], [30, 3, 188, 432, 1, 463], [361, 241, 446, 159, 442, 237], [397, 359, 157, 282, 172, 276], [57, 171, 54, 351, 230, 134]]]
 h' := ![![[190, 308, 53, 430], [425, 32, 120, 172], [499, 437, 204, 105], [116, 398, 164, 67], [131, 228, 114, 22], [7, 152, 313, 192], [48, 490, 489, 412], [0, 0, 0, 1], [0, 1]], ![[432, 172, 333, 311], [445, 385, 432, 371], [288, 128, 267, 391], [351, 260, 224, 405], [287, 289, 126, 330], [151, 454, 313, 174], [337, 409, 211, 72], [7, 196, 239, 195], [190, 308, 53, 430]], ![[142, 22, 117, 265], [144, 426, 497, 442], [16, 474, 372, 297], [262, 149, 194, 361], [284, 230, 0, 89], [207, 408, 448, 271], [422, 319, 446, 141], [470, 338, 418, 406], [432, 172, 333, 311]], ![[0, 1], [339, 163, 460, 21], [122, 470, 163, 213], [208, 199, 424, 173], [343, 259, 263, 62], [126, 495, 435, 369], [180, 291, 363, 381], [413, 472, 349, 404], [142, 22, 117, 265]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [374, 397, 190], []]
 b := ![[], [], [97, 342, 244, 373], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI503N0 : CertifiedPrimeIdeal' SI503N0 503 where
  n := 4
  hpos := by decide
  P := [473, 468, 168, 242, 1]
  hirr := P503P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5925098952, 7501204410, 846495328, 1820390221, 2259015544]
  a := ![1, 5, -13, -6, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2067592640, -2006075130, -2050742760, -1783832597, 2259015544]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI503N0 : Ideal.IsPrime I503N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI503N0 B_one_repr
lemma NI503N0 : Nat.card (O ⧸ I503N0) = 64013554081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI503N0

def I503N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-96523, -45660, -7470, -13449, 23497]] i)))

def SI503N1: IdealEqSpanCertificate' Table ![![-96523, -45660, -7470, -13449, 23497]] 
 ![![503, 0, 0, 0, 0], ![126, 1, 0, 0, 0], ![220, 0, 1, 0, 0], ![183, 0, 0, 1, 0], ![49, 0, 0, 0, 1]] where
  M :=![![![-96523, -45660, -7470, -13449, 23497], ![234970, 111145, 18184, 32737, -57197], ![-571970, -270540, -44263, -79685, 139225], ![21740, 10278, 1682, 3027, -5290], ![-330340, -156250, -25564, -46022, 80409]]]
  hmulB := by decide  
  f := ![![![-861, -248, 544, 695, -821]], ![![-232, -75, 130, 177, -199]], ![![-310, -80, 223, 265, -335]], ![![-281, -62, 218, 250, -323]], ![![-83, -26, 52, 65, -80]]]
  g := ![![![17117, -45660, -7470, -13449, 23497], ![-41666, 111145, 18184, 32737, -57197], ![101420, -270540, -44263, -79685, 139225], ![-3853, 10278, 1682, 3027, -5290], ![58575, -156250, -25564, -46022, 80409]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI503N1 : Nat.card (O ⧸ I503N1) = 503 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI503N1)

lemma isPrimeI503N1 : Ideal.IsPrime I503N1 := prime_ideal_of_norm_prime hp503.out _ NI503N1
def MulI503N0 : IdealMulLeCertificate' Table 
  ![![-861, -248, 544, 695, -821]] ![![-96523, -45660, -7470, -13449, 23497]]
  ![![503, 0, 0, 0, 0]] where
 M := ![![![503, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC503 : ContainsPrimesAboveP 503 ![I503N0, I503N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI503N0
    exact isPrimeI503N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 503 (by decide) (𝕀 ⊙ MulI503N0)
instance hp509 : Fact (Nat.Prime 509) := {out := by norm_num}

def I509N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![509, 0, 0, 0, 0]] i)))

def SI509N0: IdealEqSpanCertificate' Table ![![509, 0, 0, 0, 0]] 
 ![![509, 0, 0, 0, 0], ![0, 509, 0, 0, 0], ![0, 0, 509, 0, 0], ![0, 0, 0, 509, 0], ![0, 0, 0, 0, 509]] where
  M :=![![![509, 0, 0, 0, 0], ![0, 509, 0, 0, 0], ![0, 0, 509, 0, 0], ![0, 0, 0, 509, 0], ![0, 0, 0, 0, 509]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P509P0 : CertificateIrreducibleZModOfList' 509 5 2 8 [96, 143, 287, 380, 290, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [388, 77, 401, 501, 311], [368, 494, 82, 146, 416], [462, 226, 18, 416, 254], [19, 220, 8, 464, 37], [0, 1]]
 g := ![![[102, 131, 226, 157, 355], [439, 51, 187, 152], [20, 6, 370, 384, 56], [323, 455, 428, 289, 454], [403, 478, 218, 276, 383], [241, 153, 219, 222, 73], [244, 219, 1], []], ![[130, 48, 295, 240, 256, 172, 95, 375], [388, 434, 336, 387], [248, 366, 70, 390, 56, 265, 402, 86], [376, 497, 130, 413, 404, 46, 366, 315], [475, 27, 32, 434, 367, 454, 389, 456], [128, 131, 440, 440, 164, 138, 281, 40], [413, 285, 394, 171, 13, 163, 236, 487], [80, 220, 171, 74, 3, 332, 196, 367]], ![[482, 211, 51, 439, 194, 471, 25, 454], [347, 432, 311, 228], [445, 457, 461, 336, 22, 455, 79, 464], [242, 388, 113, 361, 363, 452, 328, 445], [351, 193, 185, 21, 28, 294, 437, 224], [64, 387, 290, 406, 229, 232, 106, 310], [96, 170, 473, 157, 90, 217, 367, 359], [89, 289, 4, 81, 78, 290, 312, 372]], ![[189, 464, 236, 402, 194, 413, 246, 15], [312, 457, 391, 97], [5, 299, 6, 59, 189, 365, 378, 474], [287, 302, 422, 336, 115, 501, 82, 76], [487, 105, 144, 434, 442, 132, 454, 166], [8, 496, 147, 26, 256, 65, 475, 76], [187, 15, 76, 295, 314, 359, 43, 201], [162, 468, 128, 319, 455, 111, 221, 318]], ![[22, 476, 280, 295, 229, 6, 436, 57], [107, 390, 114, 351], [137, 189, 9, 463, 160, 136, 204, 400], [43, 414, 201, 274, 314, 14, 248, 314], [121, 485, 312, 209, 429, 0, 200, 436], [221, 196, 316, 323, 9, 111, 229, 130], [323, 65, 27, 282, 3, 203, 379, 405], [106, 177, 188, 491, 314, 48, 322, 262]]]
 h' := ![![[388, 77, 401, 501, 311], [325, 64, 437, 347, 384], [116, 281, 467, 96, 212], [41, 240, 321, 153, 51], [505, 235, 48, 23, 246], [278, 322, 466, 33, 376], [499, 74, 359, 38, 469], [0, 0, 0, 1], [0, 1]], ![[368, 494, 82, 146, 416], [456, 376, 35, 167, 144], [106, 412, 52, 31, 305], [463, 421, 485, 81, 370], [496, 258, 395, 261, 262], [341, 299, 229, 264, 372], [243, 108, 462, 287, 200], [223, 291, 445, 70, 339], [388, 77, 401, 501, 311]], ![[462, 226, 18, 416, 254], [159, 70, 41, 356, 11], [74, 303, 77, 93, 338], [504, 176, 486, 199, 424], [70, 128, 477, 219, 182], [32, 9, 481, 482, 377], [399, 499, 269, 80, 105], [460, 426, 196, 381, 77], [368, 494, 82, 146, 416]], ![[19, 220, 8, 464, 37], [162, 406, 102, 130, 315], [269, 415, 437, 95, 126], [237, 419, 314, 103, 343], [145, 343, 371, 402, 322], [381, 59, 60, 59, 433], [34, 116, 104, 317, 322], [240, 336, 322, 297, 82], [462, 226, 18, 416, 254]], ![[0, 1], [2, 102, 403, 18, 164], [72, 116, 494, 194, 37], [218, 271, 430, 482, 339], [296, 54, 236, 113, 6], [323, 329, 291, 180, 478], [14, 221, 333, 296, 431], [246, 474, 55, 269, 11], [19, 220, 8, 464, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 490, 270, 147], [], [], []]
 b := ![[], [497, 138, 131, 264, 101], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI509N0 : CertifiedPrimeIdeal' SI509N0 509 where
  n := 5
  hpos := by decide
  P := [96, 143, 287, 380, 290, 1]
  hirr := P509P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3274221904, 4458952489, 1013353848, 1356247297, 549648740]
  a := ![4, -1, 4, 3, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6432656, 8760221, 1990872, 2664533, 1079860]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI509N0 : Ideal.IsPrime I509N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI509N0 B_one_repr
lemma NI509N0 : Nat.card (O ⧸ I509N0) = 34165588961549 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI509N0

def PBC509 : ContainsPrimesAboveP 509 ![I509N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI509N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![509, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 509 (by decide) 𝕀

instance hp521 : Fact (Nat.Prime 521) := {out := by norm_num}

def I521N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![859, 268, 56, 72, -154]] i)))

def SI521N0: IdealEqSpanCertificate' Table ![![859, 268, 56, 72, -154]] 
 ![![521, 0, 0, 0, 0], ![0, 521, 0, 0, 0], ![57, 117, 1, 0, 0], ![323, 44, 0, 1, 0], ![359, 217, 0, 0, 1]] where
  M :=![![![859, 268, 56, 72, -154], ![-1540, -483, -102, -128, 278], ![2780, 880, 179, 220, -490], ![280, 92, 24, 25, -56], ![1600, 504, 104, 134, -285]]]
  hmulB := by decide  
  f := ![![![219, 108, 16, 28, -46]], ![![-460, -179, -22, -52, 122]], ![![-77, -27, -3, -8, 22]], ![![97, 52, 8, 13, -18]], ![![-39, 1, 2, -2, 19]]]
  g := ![![![57, 46, 56, 72, -154], ![-104, -83, -102, -128, 278], ![187, 147, 179, 220, -490], ![21, 16, 24, 25, -56], ![105, 85, 104, 134, -285]]]
  hle1 := by decide   
  hle2 := by decide  


def P521P0 : CertificateIrreducibleZModOfList' 521 2 2 9 [502, 272, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [249, 520], [0, 1]]
 g := ![![[397, 476], [398], [246], [509, 2], [197], [84], [74], [2], [1]], ![[133, 45], [398], [246], [486, 519], [197], [84], [74], [2], [1]]]
 h' := ![![[249, 520], [236, 146], [390, 151], [293, 126], [294, 249], [77, 62], [139, 416], [399, 61], [19, 249], [0, 1]], ![[0, 1], [120, 375], [477, 370], [407, 395], [296, 272], [406, 459], [44, 105], [479, 460], [21, 272], [249, 520]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [374]]
 b := ![[], [424, 187]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI521N0 : CertifiedPrimeIdeal' SI521N0 521 where
  n := 2
  hpos := by decide
  P := [502, 272, 1]
  hirr := P521P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![872815, 939352, -20731, 91873, 449814]
  a := ![7, -44, 91, 25, -228]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-362963, -188651, -20731, 91873, 449814]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI521N0 : Ideal.IsPrime I521N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI521N0 B_one_repr
lemma NI521N0 : Nat.card (O ⧸ I521N0) = 271441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI521N0

def I521N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4119, 5858, 400, 1973, 2393]] i)))

def SI521N1: IdealEqSpanCertificate' Table ![![4119, 5858, 400, 1973, 2393]] 
 ![![521, 0, 0, 0, 0], ![0, 521, 0, 0, 0], ![488, 235, 1, 0, 0], ![515, 362, 0, 1, 0], ![150, 413, 0, 0, 1]] where
  M :=![![![4119, 5858, 400, 1973, 2393], ![23930, 34415, 2332, 11599, 14231], ![142310, 203730, 13849, 68645, 83825], ![71860, 103020, 6996, 34715, 42454], ![149900, 214724, 14590, 72352, 88407]]]
  hmulB := by decide  
  f := ![![![1999, 546, 54, 187, -283]], ![![-2830, -657, -298, -779, 839]], ![![612, 223, -79, -174, 106]], ![![5, 80, -154, -354, 303]], ![![-1660, -361, -220, -563, 582]]]
  g := ![![![-3006, -3437, 400, 1973, 2393], ![-17701, -20326, 2332, 11599, 14231], ![-104687, -120000, 13849, 68645, 83825], ![-52953, -60732, 6996, 34715, 42454], ![-110350, -126521, 14590, 72352, 88407]]]
  hle1 := by decide   
  hle2 := by decide  


def P521P1 : CertificateIrreducibleZModOfList' 521 2 2 9 [240, 417, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 520], [0, 1]]
 g := ![![[399, 129], [383], [189], [179, 405], [336], [144], [53], [396], [1]], ![[269, 392], [383], [189], [98, 116], [336], [144], [53], [396], [1]]]
 h' := ![![[104, 520], [200, 198], [343, 325], [283, 103], [517, 228], [38, 311], [279, 12], [72, 121], [281, 104], [0, 1]], ![[0, 1], [473, 323], [278, 196], [54, 418], [263, 293], [80, 210], [485, 509], [152, 400], [156, 417], [104, 520]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [303]]
 b := ![[], [458, 412]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI521N1 : CertifiedPrimeIdeal' SI521N1 521 where
  n := 2
  hpos := by decide
  P := [240, 417, 1]
  hirr := P521P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![53998, 52261, 7239, 6263, 5145]
  a := ![1, -9, 23, 9, -57]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14349, -11595, 7239, 6263, 5145]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI521N1 : Ideal.IsPrime I521N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI521N1 B_one_repr
lemma NI521N1 : Nat.card (O ⧸ I521N1) = 271441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI521N1

def I521N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -10, 2, 11, -5]] i)))

def SI521N2: IdealEqSpanCertificate' Table ![![-21, -10, 2, 11, -5]] 
 ![![521, 0, 0, 0, 0], ![169, 1, 0, 0, 0], ![94, 0, 1, 0, 0], ![463, 0, 0, 1, 0], ![514, 0, 0, 0, 1]] where
  M :=![![![-21, -10, 2, 11, -5], ![-50, -55, -48, -11, 61], ![610, 370, 39, -225, -5], ![20, 80, 128, 65, -166], ![40, 24, 2, -8, -3]]]
  hmulB := by decide  
  f := ![![![-10141, -14066, -972, -4731, -5705]], ![![-3399, -4721, -326, -1588, -1916]], ![![-2484, -3474, -239, -1169, -1415]], ![![-9343, -12974, -896, -4364, -5265]], ![![-10694, -14864, -1026, -5000, -6035]]]
  g := ![![![-2, -10, 2, 11, -5], ![-24, -55, -48, -11, 61], ![79, 370, 39, -225, -5], ![57, 80, 128, 65, -166], ![2, 24, 2, -8, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI521N2 : Nat.card (O ⧸ I521N2) = 521 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI521N2)

lemma isPrimeI521N2 : Ideal.IsPrime I521N2 := prime_ideal_of_norm_prime hp521.out _ NI521N2
def MulI521N0 : IdealMulLeCertificate' Table 
  ![![859, 268, 56, 72, -154]] ![![4119, 5858, 400, 1973, 2393]]
  ![![10141, 14066, 972, 4731, 5705]] where
 M := ![![![10141, 14066, 972, 4731, 5705]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI521N1 : IdealMulLeCertificate' Table 
  ![![10141, 14066, 972, 4731, 5705]] ![![-21, -10, 2, 11, -5]]
  ![![521, 0, 0, 0, 0]] where
 M := ![![![-521, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC521 : ContainsPrimesAboveP 521 ![I521N0, I521N1, I521N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI521N0
    exact isPrimeI521N1
    exact isPrimeI521N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 521 (by decide) (𝕀 ⊙ MulI521N0 ⊙ MulI521N1)
instance hp523 : Fact (Nat.Prime 523) := {out := by norm_num}

def I523N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4883, -1513, -317, -402, 870]] i)))

def SI523N0: IdealEqSpanCertificate' Table ![![-4883, -1513, -317, -402, 870]] 
 ![![523, 0, 0, 0, 0], ![0, 523, 0, 0, 0], ![0, 0, 523, 0, 0], ![201, 480, 337, 1, 0], ![368, 401, 180, 0, 1]] where
  M :=![![![-4883, -1513, -317, -402, 870], ![8700, 2700, 563, 712, -1542], ![-15420, -4735, -978, -1250, 2730], ![-1620, -503, -107, -117, 294], ![-8940, -2741, -577, -726, 1603]]]
  hmulB := by decide  
  f := ![![![79, 37, 5, 12, -18]], ![![-180, -82, -17, -34, 54]], ![![540, 295, 74, 80, -150]], ![![213, 129, 34, 25, -54]], ![![104, 65, 16, 10, -23]]]
  g := ![![![-467, -301, -41, -402, 870], ![828, 534, 73, 712, -1542], ![-1470, -955, -136, -1250, 2730], ![-165, -119, -26, -117, 294], ![-866, -568, -85, -726, 1603]]]
  hle1 := by decide   
  hle2 := by decide  


def P523P0 : CertificateIrreducibleZModOfList' 523 3 2 9 [70, 275, 336, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [400, 299, 332], [310, 223, 191], [0, 1]]
 g := ![![[69, 252, 252], [406, 350, 190], [396, 488], [102, 149, 345], [24, 502], [464, 301], [181, 119], [187, 1], []], ![[429, 147, 326, 446], [292, 213, 174, 276], [275, 249], [202, 510, 332, 46], [93, 488], [265, 10], [34, 377], [149, 44], [254, 394]], ![[371, 273, 150, 345], [396, 305, 34, 360], [407, 368], [502, 249, 281, 116], [353, 40], [390, 461], [395, 73], [132, 491], [395, 394]]]
 h' := ![![[400, 299, 332], [345, 295, 323], [174, 66, 98], [182, 34, 79], [181, 191, 297], [412, 426, 198], [107, 379, 54], [508, 282, 176], [0, 0, 1], [0, 1]], ![[310, 223, 191], [25, 263, 517], [34, 348, 357], [478, 14, 140], [514, 108, 462], [508, 289, 444], [185, 259, 321], [280, 351, 30], [487, 37, 223], [400, 299, 332]], ![[0, 1], [318, 488, 206], [339, 109, 68], [515, 475, 304], [409, 224, 287], [231, 331, 404], [181, 408, 148], [482, 413, 317], [460, 486, 299], [310, 223, 191]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [435, 71], []]
 b := ![[], [137, 14, 203], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI523N0 : CertifiedPrimeIdeal' SI523N0 523 where
  n := 3
  hpos := by decide
  P := [70, 275, 336, 1]
  hirr := P523P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9563766, 14006191, -225357, 4895902, 7880870]
  a := ![3, 9, -9, 7, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7408552, -10509093, -5867497, 4895902, 7880870]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI523N0 : Ideal.IsPrime I523N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI523N0 B_one_repr
lemma NI523N0 : Nat.card (O ⧸ I523N0) = 143055667 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI523N0

def I523N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, -37, -5, -12, 18]] i)))

def SI523N1: IdealEqSpanCertificate' Table ![![-79, -37, -5, -12, 18]] 
 ![![523, 0, 0, 0, 0], ![0, 523, 0, 0, 0], ![390, 291, 1, 0, 0], ![157, 44, 0, 1, 0], ![412, 50, 0, 0, 1]] where
  M :=![![![-79, -37, -5, -12, 18], ![180, 82, 17, 34, -54], ![-540, -295, -74, -80, 150], ![60, 25, 1, -23, -6], ![-300, -161, -25, -48, 59]]]
  hmulB := by decide  
  f := ![![![4883, 1513, 317, 402, -870]], ![![-8700, -2700, -563, -712, 1542]], ![![-1170, -365, -75, -94, 204]], ![![737, 228, 48, 61, -132]], ![![3032, 939, 197, 250, -541]]]
  g := ![![![-7, 2, -5, -12, 18], ![20, -7, 17, 34, -54], ![-40, 33, -74, -80, 150], ![11, 2, 1, -23, -6], ![-14, 12, -25, -48, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P523P1 : CertificateIrreducibleZModOfList' 523 2 2 9 [249, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [382, 522], [0, 1]]
 g := ![![[177, 502], [518, 497], [29], [161, 371], [410], [444], [369], [7], [1]], ![[0, 21], [0, 26], [29], [150, 152], [410], [444], [369], [7], [1]]]
 h' := ![![[382, 522], [199, 198], [276, 180], [182, 358], [315, 246], [290, 468], [384, 409], [113, 195], [274, 382], [0, 1]], ![[0, 1], [0, 325], [0, 343], [435, 165], [147, 277], [200, 55], [245, 114], [337, 328], [281, 141], [382, 522]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [422]]
 b := ![[], [493, 211]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI523N1 : CertifiedPrimeIdeal' SI523N1 523 where
  n := 2
  hpos := by decide
  P := [249, 141, 1]
  hirr := P523P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![306921, 298104, 936, -3948, 119258]
  a := ![3, -18, 56, 31, -136]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-92873, -11020, 936, -3948, 119258]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI523N1 : Ideal.IsPrime I523N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI523N1 B_one_repr
lemma NI523N1 : Nat.card (O ⧸ I523N1) = 273529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI523N1
def MulI523N0 : IdealMulLeCertificate' Table 
  ![![-4883, -1513, -317, -402, 870]] ![![-79, -37, -5, -12, 18]]
  ![![523, 0, 0, 0, 0]] where
 M := ![![![-523, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC523 : ContainsPrimesAboveP 523 ![I523N0, I523N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI523N0
    exact isPrimeI523N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 523 (by decide) (𝕀 ⊙ MulI523N0)


lemma PB1321I10_primes (p : ℕ) :
  p ∈ Set.range ![467, 479, 487, 491, 499, 503, 509, 521, 523] ↔ Nat.Prime p ∧ 463 < p ∧ p ≤ 523 := by
  rw [← List.mem_ofFn']
  convert primes_range 463 523 (by omega)

def PB1321I10 : PrimesBelowBoundCertificateInterval O 463 523 1321 where
  m := 9
  g := ![4, 2, 2, 2, 2, 2, 1, 3, 2]
  P := ![467, 479, 487, 491, 499, 503, 509, 521, 523]
  hP := PB1321I10_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I467N0, I467N1, I467N2, I467N3]
    · exact ![I479N0, I479N1]
    · exact ![I487N0, I487N1]
    · exact ![I491N0, I491N1]
    · exact ![I499N0, I499N1]
    · exact ![I503N0, I503N1]
    · exact ![I509N0]
    · exact ![I521N0, I521N1, I521N2]
    · exact ![I523N0, I523N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC467
    · exact PBC479
    · exact PBC487
    · exact PBC491
    · exact PBC499
    · exact PBC503
    · exact PBC509
    · exact PBC521
    · exact PBC523
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![218089, 467, 467, 467]
    · exact ![109902239, 229441]
    · exact ![115501303, 237169]
    · exact ![118370771, 241081]
    · exact ![124251499, 249001]
    · exact ![64013554081, 503]
    · exact ![34165588961549]
    · exact ![271441, 271441, 521]
    · exact ![143055667, 273529]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI467N0
      exact NI467N1
      exact NI467N2
      exact NI467N3
    · dsimp ; intro j
      fin_cases j
      exact NI479N0
      exact NI479N1
    · dsimp ; intro j
      fin_cases j
      exact NI487N0
      exact NI487N1
    · dsimp ; intro j
      fin_cases j
      exact NI491N0
      exact NI491N1
    · dsimp ; intro j
      fin_cases j
      exact NI499N0
      exact NI499N1
    · dsimp ; intro j
      fin_cases j
      exact NI503N0
      exact NI503N1
    · dsimp ; intro j
      fin_cases j
      exact NI509N0
    · dsimp ; intro j
      fin_cases j
      exact NI521N0
      exact NI521N1
      exact NI521N2
    · dsimp ; intro j
      fin_cases j
      exact NI523N0
      exact NI523N1
  β := ![I467N1, I467N2, I467N3, I503N1, I521N2]
  Il := ![[I467N1, I467N2, I467N3], [], [], [], [], [I503N1], [], [I521N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
