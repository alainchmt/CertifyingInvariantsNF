
import IdealArithmetic.Examples.NF5_1_405000000_12.RI5_1_405000000_12
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1573, -3135, -2330, -602, -578]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-1573, -3135, -2330, -602, -578]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![55, 22, 14, 59, 1]] where
  M :=![![![-1573, -3135, -2330, -602, -578], ![-3468, -6841, -5066, -1240, -1252], ![-3756, -7385, -5601, -1298, -1228], ![-1950, -4398, -3554, -1367, -742], ![-282, -689, -6, -322, -613]]]
  hmulB := by decide  
  f := ![![![-3451, -1013, 2256, 150, 622]], ![![3732, 971, -2326, -164, -644]], ![![-1932, -427, 1135, 86, 316]], ![![-918, -324, 650, 39, 178]], ![![-2851, -894, 1916, 123, 527]]]
  g := ![![![451, 143, 86, 500, -578], ![976, 309, 186, 1084, -1252], ![952, 293, 173, 1062, -1228], ![580, 178, 102, 633, -742], ![499, 191, 128, 535, -613]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 4 2 6 [64, 45, 65, 64, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 22, 61, 29], [57, 46, 30, 24], [10, 65, 43, 14], [0, 1]]
 g := ![![[1, 59, 15, 37], [5, 14, 36, 9], [7, 66, 54], [3, 39, 9], [1], []], ![[60, 62, 25, 48, 40, 29], [34, 44, 60, 58, 60, 14], [29, 6, 59], [18, 10, 6], [41, 25, 9], [5, 31, 37]], ![[32, 46, 33, 31, 64, 40], [36, 34, 1, 50, 51, 26], [19, 7, 65], [10, 36, 56], [52, 18, 4], [29, 19, 40]], ![[22, 3, 39, 3, 2, 9], [8, 14, 24, 1, 41, 39], [13, 26, 16], [17, 17, 65], [37, 42, 1], [57, 50, 62]]]
 h' := ![![[3, 22, 61, 29], [15, 51, 34, 38], [10, 34, 35, 3], [18, 47, 47, 56], [3, 22, 2, 3], [0, 0, 1], [0, 1]], ![[57, 46, 30, 24], [48, 19, 55, 66], [60, 35, 11, 7], [24, 8, 8, 27], [29, 39, 5, 26], [24, 0, 45, 64], [3, 22, 61, 29]], ![[10, 65, 43, 14], [25, 8, 45, 52], [45, 22, 15, 37], [51, 57, 65, 47], [17, 61, 41, 18], [53, 43, 35, 2], [57, 46, 30, 24]], ![[0, 1], [28, 56, 0, 45], [11, 43, 6, 20], [46, 22, 14, 4], [53, 12, 19, 20], [3, 24, 53, 1], [10, 65, 43, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 63, 50], []]
 b := ![[], [], [66, 37, 16, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 4
  hpos := by decide
  P := [64, 45, 65, 64, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2795577440, -484048975, -2085161416, 5576303898, 3205298003]
  a := ![0, -7, 2, -8, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2672939815, -1059710523, -700885574, -2739347437, 3205298003]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 20151121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3451, 1013, -2256, -150, -622]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![3451, 1013, -2256, -150, -622]] 
 ![![67, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![3451, 1013, -2256, -150, -622], ![-3732, -971, 2326, 164, 644], ![1932, 427, -1135, -86, -316], ![918, 324, -650, -39, -178], ![2106, 451, -1224, -94, -341]]]
  hmulB := by decide  
  f := ![![![1573, 3135, 2330, 602, 578]], ![![850, 1693, 1258, 324, 312]], ![![643, 1280, 953, 244, 234]], ![![663, 1329, 992, 263, 244]], ![![1272, 2537, 1878, 490, 475]]]
  g := ![![![941, 1013, -2256, -150, -622], ![-1016, -971, 2326, 164, 644], ![525, 427, -1135, -86, -316], ![251, 324, -650, -39, -178], ![572, 451, -1224, -94, -341]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-1573, -3135, -2330, -602, -578]] ![![3451, 1013, -2256, -150, -622]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![-67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5667534906313, -11276161562384, -8401414211442, -2143117799298, -2053695684460]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-5667534906313, -11276161562384, -8401414211442, -2143117799298, -2053695684460]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![59, 14, 1, 0, 0], ![26, 47, 0, 1, 0], ![50, 52, 0, 0, 1]] where
  M :=![![![-5667534906313, -11276161562384, -8401414211442, -2143117799298, -2053695684460], ![-12322174106760, -24516271769731, -18266087526172, -4659498545800, -4465079828272], ![-13395239484816, -26651249104674, -19856773223931, -5065266758884, -4853917263328], ![-8400664736604, -16714013123384, -12452938582704, -3176621656603, -3044076340304], ![-902314831182, -1795251019136, -1337569290918, -341200717286, -326964033827]]]
  hmulB := by decide  
  f := ![![![-21551, -28716, 36610, 3722, -50628]], ![![-303768, -129381, -64876, 485688, 116144]], ![![-72899, -42676, 8967, 98246, -7124]], ![![-170702, -79677, -21768, 261993, 44248]], ![![-273344, -148464, 9190, 386686, 7829]]]
  g := ![![![9132700712303, 4420596472630, -8401414211442, -2143117799298, -2053695684460], ![19856027373828, 9611120229851, -18266087526172, -4659498545800, -4465079828272], ![21585171544007, 10448095935084, -19856773223931, -5065266758884, -4853917263328], ![13536882982110, 6552398797051, -12452938582704, -3176621656603, -3044076340304], ![1453995685546, 703792711622, -1337569290918, -341200717286, -326964033827]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [3, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 70], [0, 1]]
 g := ![![[62, 24], [58, 40], [5, 18], [16], [19], [1]], ![[0, 47], [2, 31], [65, 53], [16], [19], [1]]]
 h' := ![![[27, 70], [39, 38], [56, 53], [55, 35], [23, 67], [68, 27], [0, 1]], ![[0, 1], [0, 33], [67, 18], [6, 36], [57, 4], [16, 44], [27, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [14, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [3, 44, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-153552, -27807, -91023, 303647, 155218]
  a := ![3, -62, -1, -63, -58]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-147027, -297130, -91023, 303647, 155218]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![421, 420, -546, -14, -144]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![421, 420, -546, -14, -144]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![24, 54, 1, 0, 0], ![53, 43, 0, 1, 0], ![2, 12, 0, 0, 1]] where
  M :=![![![421, 420, -546, -14, -144], ![-864, -585, 868, 32, 232], ![696, 382, -617, -28, -168], ![-72, 52, -24, 11, -4], ![810, 436, -710, -34, -185]]]
  hmulB := by decide  
  f := ![![![22187, 44144, 32890, 8390, 8040]], ![![48240, 95977, 71508, 18240, 17480]], ![![44928, 89388, 66599, 16988, 16280]], ![![46241, 92001, 68546, 17485, 16756]], ![![8828, 17564, 13086, 3338, 3199]]]
  g := ![![![205, 454, -546, -14, -144], ![-336, -727, 868, 32, 232], ![244, 520, -617, -28, -168], ![-1, 13, -24, 11, -4], ![282, 598, -710, -34, -185]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [41, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 70], [0, 1]]
 g := ![![[28, 40], [4, 40], [34, 27], [20], [2], [1]], ![[45, 31], [21, 31], [65, 44], [20], [2], [1]]]
 h' := ![![[59, 70], [49, 53], [26, 53], [52, 13], [37, 37], [30, 59], [0, 1]], ![[0, 1], [52, 18], [29, 18], [38, 58], [19, 34], [32, 12], [59, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [29, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [41, 12, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2025, -297, -1609, 4255, 2524]
  a := ![1, -6, 1, -7, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2732, -1784, -1609, 4255, 2524]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1739, 3496, -5436, 1544, 7660]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![1739, 3496, -5436, 1544, 7660]] 
 ![![71, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![53, 0, 1, 0, 0], ![51, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![1739, 3496, -5436, 1544, 7660], ![45960, 22371, 3904, -69064, -9144], ![-27432, -57848, 91435, -28584, -128984], ![-409932, -201244, -31216, 613319, 76388], ![282852, 314176, -347908, -148144, 477011]]]
  hmulB := by decide  
  f := ![![![1919684773, 3819415720, 2845692948, 725908168, 695619468]], ![![221011626, 439726011, 327622152, 83573176, 80086064]], ![![1496908087, 2978256848, 2218979327, 566039712, 542421564]], ![![1419005109, 2823260628, 2103497876, 536581535, 514192536]], ![![761363408, 1514812960, 1128626180, 287901392, 275888635]]]
  g := ![![![-343, 3496, -5436, 1544, 7660], ![49058, 22371, 3904, -69064, -9144], ![7647, -57848, 91435, -28584, -128984], ![-436143, -201244, -31216, 613319, 76388], ![155436, 314176, -347908, -148144, 477011]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-5667534906313, -11276161562384, -8401414211442, -2143117799298, -2053695684460]] ![![421, 420, -546, -14, -144]]
  ![![-1919684773, -3819415720, -2845692948, -725908168, -695619468]] where
 M := ![![![-1919684773, -3819415720, -2845692948, -725908168, -695619468]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-1919684773, -3819415720, -2845692948, -725908168, -695619468]] ![![1739, 3496, -5436, 1544, 7660]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![-71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![203161, 429816, 331682, 83002, 81372]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![203161, 429816, 331682, 83002, 81372]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![44, 53, 1, 0, 0], ![4, 24, 0, 1, 0], ![3, 37, 0, 0, 1]] where
  M :=![![![203161, 429816, 331682, 83002, 81372], ![488232, 944963, 693628, 178392, 169264], ![507792, 1023218, 766571, 194964, 187520], ![318444, 640944, 481440, 122259, 117776], ![27222, 68088, 55094, 13454, 13611]]]
  hmulB := by decide  
  f := ![![![70417, 18412, 39410, -130702, -61940]], ![![-371640, -337397, 298228, 312936, -398928]], ![![-243772, -238275, 231367, 178652, -312928]], ![![-73664, -68968, 63520, 58747, -85392]], ![![-139719, -170249, 203584, 49556, -281121]]]
  g := ![![![-205027, -303454, 331682, 83002, 81372], ![-428120, -635089, 693628, 178392, 169264], ![-473476, -701677, 766571, 194964, 187520], ![-297360, -440648, 481440, 122259, 117776], ![-34131, -50389, 55094, 13454, 13611]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [39, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 72], [0, 1]]
 g := ![![[1, 48], [48], [64], [53, 36], [61], [1]], ![[27, 25], [48], [64], [36, 37], [61], [1]]]
 h' := ![![[34, 72], [42, 11], [4, 62], [50, 65], [18, 6], [34, 34], [0, 1]], ![[0, 1], [51, 62], [68, 11], [70, 8], [3, 67], [22, 39], [34, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [25, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [39, 39, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19370, 12185, -41512, 62208, 64287]
  a := ![1, 25, -3, 24, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![18705, -22730, -41512, 62208, 64287]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15973, 31780, 23678, 6040, 5788]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![15973, 31780, 23678, 6040, 5788]] 
 ![![73, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![15973, 31780, 23678, 6040, 5788], ![34728, 69095, 51480, 13132, 12584], ![37752, 75112, 55963, 14276, 13680], ![23676, 47106, 35096, 8953, 8580], ![2544, 5060, 3770, 960, 921]]]
  hmulB := by decide  
  f := ![![![-2267, 1300, -314, 128, -44]], ![![-221, 91, 2, 12, 4]], ![![-348, 240, -85, 20, -16]], ![![-2012, 1138, -264, 113, -36]], ![![-1243, 760, -216, 72, -35]]]
  g := ![![![-15267, 31780, 23678, 6040, 5788], ![-33193, 69095, 51480, 13132, 12584], ![-36084, 75112, 55963, 14276, 13680], ![-22630, 47106, 35096, 8953, 8580], ![-2429, 5060, 3770, 960, 921]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1199483, 448328, 387462, -2015060, -648100]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![1199483, 448328, 387462, -2015060, -648100]] 
 ![![73, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![69, 0, 1, 0, 0], ![50, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![1199483, 448328, 387462, -2015060, -648100], ![-3888600, -4387475, 4926776, 1929604, -6764040], ![-20292120, -7697368, -6317079, 33912540, 10623248], ![33814044, 38736550, -44073296, -15862333, 60583852], ![65766996, 13918688, 43714162, -127212884, -67752541]]]
  hmulB := by decide  
  f := ![![![-3743994692197, -7449074373840, -5550005555706, -1415751609428, -1356679027084]], ![![-573096251949, -1140235752227, -849543774386, -216710227376, -207667940100]], ![![-3660062724825, -7282082826432, -5425586873673, -1384013632312, -1326265324828]], ![![-2640400617254, -5253356960058, -3914064869140, -998439295653, -956779171716]], ![![-110740574318, -220330113208, -164159101010, -41875365548, -40128105677]]]
  g := ![![![992861, 448328, 387462, -2015060, -648100], ![-5305493, -4387475, 4926776, 1929604, -6764040], ![-16876861, -7697368, -6317079, 33912540, 10623248], ![46550568, 38736550, -44073296, -15862333, 60583852], ![46854396, 13918688, 43714162, -127212884, -67752541]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2

def I73N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, 8, 46, 6, 12]] i)))

def SI73N3: IdealEqSpanCertificate' Table ![![-23, 8, 46, 6, 12]] 
 ![![73, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-23, 8, 46, 6, 12], ![72, 71, 4, 8, 0], ![0, 46, 63, 12, 16], ![12, 32, 32, 7, 8], ![-30, -8, 26, 2, 7]]]
  hmulB := by decide  
  f := ![![![1, -4, -10, 22, -4]], ![![0, -1, -4, 8, 0]], ![![4, 2, -1, -4, 0]], ![![1, -4, 6, -3, -12]], ![![-15, -8, -4, 28, 3]]]
  g := ![![![-9, 8, 46, 6, 12], ![-24, 71, 4, 8, 0], ![-24, 46, 63, 12, 16], ![-15, 32, 32, 7, 8], ![-1, -8, 26, 2, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N3 : Nat.card (O ⧸ I73N3) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N3)

lemma isPrimeI73N3 : Ideal.IsPrime I73N3 := prime_ideal_of_norm_prime hp73.out _ NI73N3
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![203161, 429816, 331682, 83002, 81372]] ![![15973, 31780, 23678, 6040, 5788]]
  ![![32865565285, 65389526016, 48719104236, 12427762410, 11909210944]] where
 M := ![![![32865565285, 65389526016, 48719104236, 12427762410, 11909210944]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![32865565285, 65389526016, 48719104236, 12427762410, 11909210944]] ![![1199483, 448328, 387462, -2015060, -648100]]
  ![![-1, 4, 10, -22, 4]] where
 M := ![![![-1, 4, 10, -22, 4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N2 : IdealMulLeCertificate' Table 
  ![![-1, 4, 10, -22, 4]] ![![-23, 8, 46, 6, 12]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![-73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2, I73N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
    exact isPrimeI73N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1 ⊙ MulI73N2)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0, 0, 0]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]] where
  M :=![![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [70, 50, 19, 60, 57, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 12, 12, 34, 26], [11, 46, 69, 42, 38], [38, 27, 13, 65, 23], [64, 72, 64, 17, 71], [0, 1]]
 g := ![![[25, 57, 42, 11, 21], [16, 68, 46, 17, 10], [39, 44, 31], [66, 10, 29, 22, 1], [], []], ![[69, 25, 33, 11, 19, 22, 71, 50], [41, 59, 29, 61, 70, 6, 13, 42], [69, 34, 41, 78, 12, 72, 9, 65], [3, 4, 13, 53, 17, 1, 56, 38], [77, 44, 52, 45], [40, 3, 50, 44]], ![[42, 16, 55, 41, 2, 1, 53, 52], [16, 24, 27, 57, 50, 75, 0, 62], [73, 15, 43, 39, 37, 14, 47, 76], [67, 66, 62, 60, 57, 67, 7, 52], [76, 33, 55, 13], [59, 55, 42, 22]], ![[38, 67, 26, 69, 4, 71, 21, 76], [12, 53, 76, 50, 67, 8, 69, 67], [44, 68, 14, 42, 42, 26, 1, 40], [8, 76, 8, 17, 28, 28, 26, 20], [61, 43, 38, 64], [62, 71, 13, 55]], ![[63, 25, 3, 48, 34, 70, 57, 43], [11, 35, 62, 10, 1, 74, 49, 75], [63, 7, 29, 0, 35, 66, 11, 37], [33, 77, 50, 61, 76, 62, 3, 48], [23, 30, 62, 46], [42, 35, 30, 64]]]
 h' := ![![[67, 12, 12, 34, 26], [65, 10, 70, 66, 69], [35, 48, 32, 10, 57], [41, 29, 8, 49], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[11, 46, 69, 42, 38], [71, 62, 59, 43, 61], [14, 3, 6, 1, 36], [53, 38, 56, 46, 68], [13, 5, 17, 28, 26], [30, 30, 28, 46, 19], [67, 12, 12, 34, 26]], ![[38, 27, 13, 65, 23], [59, 26, 33, 15, 27], [69, 72, 59, 55, 71], [2, 54, 37, 4, 70], [57, 2, 6, 41, 52], [20, 58, 62, 74, 31], [11, 46, 69, 42, 38]], ![[64, 72, 64, 17, 71], [1, 53, 57, 20, 54], [19, 21, 8, 68, 29], [15, 22, 4, 16, 15], [14, 57, 59, 1, 51], [27, 65, 29, 23, 8], [38, 27, 13, 65, 23]], ![[0, 1], [38, 7, 18, 14, 26], [33, 14, 53, 24, 44], [2, 15, 53, 43, 5], [21, 15, 76, 9, 28], [50, 5, 38, 15, 21], [64, 72, 64, 17, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 53, 69, 66], [], [], []]
 b := ![[], [11, 77, 70, 10, 40], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [70, 50, 19, 60, 57, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-28703998631017, -27263137628603, 25570984435831, 22281173692043, -34449259397982]
  a := ![-1, -7, 5, -5, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-363341754823, -345103007957, 323683347289, 282040173317, -436066574658]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 3077056399 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀

instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![118, 13, -220, 246, 57]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![118, 13, -220, 246, 57]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![21, 41, 34, 48, 1]] where
  M :=![![![118, 13, -220, 246, 57], ![342, 561, -466, -404, 870], ![2610, 839, 965, -4350, -1678], ![-5205, -5360, 5422, 3529, -7457], ![-7449, -955, -6440, 15652, 9712]]]
  hmulB := by decide  
  f := ![![![299486, 595861, 443954, 113248, 108523]], ![![651138, 1295505, 965226, 246220, 235946]], ![![707838, 1408321, 1049285, 267662, 256494]], ![![443913, 883212, 658046, 167861, 160857]], ![![944673, 1879527, 1400360, 357218, 342313]]]
  g := ![![![-13, -28, -26, -30, 57], ![-216, -423, -362, -508, 870], ![456, 839, 699, 918, -1678], ![1824, 3619, 3120, 4355, -7457], ![-2547, -4809, -4056, -5428, 9712]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [74, 19, 53, 36, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 32, 12, 65], [65, 82], [19, 51, 71, 18], [0, 1]]
 g := ![![[42, 0, 55, 59], [0, 73, 72, 1], [39, 3, 9], [52, 19, 4], [47, 1], []], ![[59, 9, 80, 12, 27, 30], [82, 28, 39, 29, 81, 1], [44, 76, 16], [26, 62, 40], [65, 79, 56, 68, 79, 10], [35, 22, 75]], ![[47, 76, 23, 24], [80, 53, 18, 82], [79, 72, 9], [10, 42, 4], [29, 82], []], ![[25, 2, 2, 16, 66, 53], [4, 82, 9, 73, 74, 82], [42, 2, 16], [1, 50, 40], [29, 17, 20, 29, 9, 73], [35, 22, 75]]]
 h' := ![![[46, 32, 12, 65], [0, 79, 9, 15], [13, 16, 29, 82], [34, 62, 13, 3], [8, 29, 63, 81], [0, 0, 1], [0, 1]], ![[65, 82], [58, 78, 50, 21], [71, 36, 26, 43], [16, 37, 43, 79], [23, 77, 10, 17], [24, 70, 32, 75], [46, 32, 12, 65]], ![[19, 51, 71, 18], [2, 24, 29, 68], [13, 8, 0, 1], [76, 63, 17, 80], [22, 33, 5, 2], [75, 36, 1], [65, 82]], ![[0, 1], [33, 68, 78, 62], [12, 23, 28, 40], [7, 4, 10, 4], [9, 27, 5, 66], [12, 60, 49, 8], [19, 51, 71, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [22], []]
 b := ![[], [], [12, 68, 48, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [74, 19, 53, 36, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9070228534, -16044006264, 23735584838, -4614517654, -33332438404]
  a := ![0, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8324228650, 16272120100, 13940222778, 19220994286, -33332438404]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![299486, 595861, 443954, 113248, 108523]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![299486, 595861, 443954, 113248, 108523]] 
 ![![83, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![42, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![299486, 595861, 443954, 113248, 108523], ![651138, 1295505, 965226, 246220, 235946], ![707838, 1408321, 1049285, 267662, 256494], ![443913, 883212, 658046, 167861, 160857], ![47679, 94865, 70682, 18030, 17278]]]
  hmulB := by decide  
  f := ![![![118, 13, -220, 246, 57]], ![![88, 16, -162, 170, 51]], ![![94, 17, -105, 78, 10]], ![![-3, -58, -46, 167, -61]], ![![-67, -9, -120, 236, 128]]]
  g := ![![![-733531, 595861, 443954, 113248, 108523], ![-1594819, 1295505, 965226, 246220, 235946], ![-1733703, 1408321, 1049285, 267662, 256494], ![-1087271, 883212, 658046, 167861, 160857], ![-116784, 94865, 70682, 18030, 17278]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![118, 13, -220, 246, 57]] ![![299486, 595861, 443954, 113248, 108523]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65, 206, -362, 176, 514]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![65, 206, -362, 176, 514]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![57, 30, 1, 0, 0], ![70, 19, 0, 1, 0], ![75, 50, 0, 0, 1]] where
  M :=![![![65, 206, -362, 176, 514], ![3084, 1597, 60, -4484, -324], ![-972, -3398, 6081, -3128, -8644], ![-27474, -14338, -300, 39771, 2550], ![15534, 19526, -23894, -4572, 33061]]]
  hmulB := by decide  
  f := ![![![-3227, -9278, -6354, -1712, -1570]], ![![-9420, -17715, -15132, -3572, -3708]], ![![-5367, -12154, -9329, -2344, -2294]], ![![-4612, -11223, -8340, -2137, -2054]], ![![-8031, -17798, -13852, -3452, -3405]]]
  g := ![![![-339, -202, -362, 176, 514], ![3796, 1137, 60, -4484, -324], ![5839, 3436, 6081, -3128, -8644], ![-33546, -9983, -300, 39771, 2550], ![-8787, -9324, -23894, -4572, 33061]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [10, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 88], [0, 1]]
 g := ![![[62, 9], [72], [50], [], [56, 9], [1]], ![[0, 80], [72], [50], [], [83, 80], [1]]]
 h' := ![![[3, 88], [80, 3], [34, 61], [0, 53], [63], [79, 3], [0, 1]], ![[0, 1], [0, 86], [39, 28], [70, 36], [63], [88, 86], [3, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [20, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [10, 86, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3376, 5168, -9634, 3922, 12706]
  a := ![13, -7, 4, -6, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7584, -4670, -9634, 3922, 12706]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![287560486, 572132071, 426272580, 108737926, 104200809]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![287560486, 572132071, 426272580, 108737926, 104200809]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![70, 76, 1, 0, 0], ![20, 0, 0, 1, 0], ![25, 88, 0, 0, 1]] where
  M :=![![![287560486, 572132071, 426272580, 108737926, 104200809], ![625204854, 1243911345, 926788290, 236414540, 226550086], ![679650258, 1352236241, 1007496805, 257002486, 246278994], ![426234555, 848038836, 631839610, 161176045, 154450935], ![45781827, 91087795, 67865848, 17311908, 16589564]]]
  hmulB := by decide  
  f := ![![![578, 385, 102, -1120, 25]], ![![150, -1485, 3010, -2236, -4530]], ![![430, -1049, 2659, -2578, -3848]], ![![131, 236, -290, -21, 455]], ![![907, -1094, 3108, -3462, -4665]]]
  g := ![![![-385744931, -460609609, 426272580, 108737926, 104200809], ![-838674364, -1001442767, 926788290, 236414540, 226550086], ![-911709558, -1088652499, 1007496805, 257002486, 246278994], ![-571767780, -682735436, 631839610, 161176045, 154450935], ![-61413537, -73332565, 67865848, 17311908, 16589564]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [6, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 88], [0, 1]]
 g := ![![[66, 8], [9], [40], [55, 80], [26, 87], [1]], ![[13, 81], [9], [40], [59, 9], [17, 2], [1]]]
 h' := ![![[49, 88], [27, 50], [80, 86], [26, 29], [22, 76], [83, 49], [0, 1]], ![[0, 1], [74, 39], [22, 3], [23, 60], [8, 13], [81, 40], [49, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [70, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [6, 40, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![906, 570, -243, -1268, 364]
  a := ![-1, -1, -1, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![384, -146, -243, -1268, 364]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-155, 54, -286, 436, 422]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![-155, 54, -286, 436, 422]] 
 ![![89, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![70, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-155, 54, -286, 436, 422], ![2532, 1697, -764, -3076, 900], ![2700, -842, 4773, -7440, -7052], ![-22422, -15130, 6980, 27079, -8278], ![-1122, 9766, -21826, 17864, 31381]]]
  hmulB := by decide  
  f := ![![![-101647, 22970, 17906, 5148, 6090]], ![![-62405, 13575, 11466, 3152, 3858]], ![![-51111, 12132, 8463, 2596, 2926]], ![![-80612, 17986, 14408, 4079, 4882]], ![![-23577, 6028, 3512, 1204, 1251]]]
  g := ![![![-333, 54, -286, 436, 422], ![1573, 1697, -764, -3076, 900], ![5653, -842, 4773, -7440, -7052], ![-13776, -15130, 6980, 27079, -8278], ![-16467, 9766, -21826, 17864, 31381]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![65, 206, -362, 176, 514]] ![![287560486, 572132071, 426272580, 108737926, 104200809]]
  ![![-621124, -1235791, -920738, -234870, -225071]] where
 M := ![![![-621124, -1235791, -920738, -234870, -225071]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![-621124, -1235791, -920738, -234870, -225071]] ![![-155, 54, -286, 436, 422]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![43610, 123087, 110360, 60698, 18957]]]
 hmul := by decide  
 g := ![![![![490, 1383, 1240, 682, 213]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![655024966, 1303241617, 970992884, 247690696, 237355741]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![655024966, 1303241617, 970992884, 247690696, 237355741]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![86, 43, 81, 1, 0], ![63, 1, 95, 0, 1]] where
  M :=![![![655024966, 1303241617, 970992884, 247690696, 237355741], ![1424134446, 2833466465, 2111101842, 538521232, 516051302], ![1548153906, 3080216329, 2294945233, 585417866, 560991162], ![970906263, 1931720946, 1439247542, 367137835, 351818919], ![104284977, 207486017, 154589480, 39434250, 37788846]]]
  hmulB := by decide  
  f := ![![![34, 103, -50, -106, 109]], ![![654, 99, 418, -1184, -642]], ![![-1926, -1611, 1283, 1802, -1726]], ![![-1345, -1222, 1175, 995, -1571]], ![![-1755, -1438, 1191, 1564, -1581]]]
  g := ![![![-367008109, -98812516, -429286071, 247690696, 237355741], ![-797937356, -214835029, -933340120, 538521232, 516051302], ![-867425008, -233543743, -1014619199, 585417866, 560991162], ![-543995252, -146464174, -636306334, 367137835, 351818919], ![-58430493, -15731707, -68345620, 39434250, 37788846]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [34, 34, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 86, 15], [59, 10, 82], [0, 1]]
 g := ![![[35, 65, 2], [44, 53], [84, 8], [31, 61], [34, 22], [1]], ![[65, 53, 9, 20], [76, 16], [61, 95], [30, 75], [92, 2], [0, 63, 63, 77]], ![[79, 50, 46, 60], [96, 95], [34, 85], [57, 47], [73, 75], [60, 9, 38, 20]]]
 h' := ![![[71, 86, 15], [24, 52, 83], [29, 31, 21], [13, 73, 28], [0, 20, 62], [63, 63, 33], [0, 1]], ![[59, 10, 82], [43, 36, 58], [28, 8, 93], [29, 18, 17], [46, 39, 47], [78, 91, 14], [71, 86, 15]], ![[0, 1], [37, 9, 53], [87, 58, 80], [51, 6, 52], [90, 38, 85], [27, 40, 50], [59, 10, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 79], []]
 b := ![[], [23, 15, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [34, 34, 64, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13003375, 9135629, -4796296, -15152507, 5892990]
  a := ![3, 3, 0, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9740831, 6750520, 6832193, -15152507, 5892990]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![34, 103, -50, -106, 109]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![34, 103, -50, -106, 109]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![54, 16, 1, 0, 0], ![9, 14, 0, 1, 0], ![81, 13, 0, 0, 1]] where
  M :=![![![34, 103, -50, -106, 109], ![654, 99, 418, -1184, -642], ![-1926, -1611, 1283, 1802, -1726], ![-5505, -1158, -3622, 10581, 5651], ![9939, 6971, -3626, -11620, 4388]]]
  hmulB := by decide  
  f := ![![![655024966, 1303241617, 970992884, 247690696, 237355741]], ![![1424134446, 2833466465, 2111101842, 538521232, 516051302]], ![![615522198, 1224646671, 912434953, 232753146, 223041464]], ![![276330033, 549787897, 409624838, 104491251, 100131328]], ![![738918093, 1470155887, 1095353990, 279413986, 267755369]]]
  g := ![![![-53, 10, -50, -106, 109], ![420, 189, 418, -1184, -642], ![540, -257, 1283, 1802, -1726], ![-3741, -1699, -3622, 10581, 5651], ![-465, 1759, -3626, -11620, 4388]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [72, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 96], [0, 1]]
 g := ![![[21, 31], [8], [81], [88], [91], [40, 1]], ![[0, 66], [8], [81], [88], [91], [80, 96]]]
 h' := ![![[40, 96], [18, 82], [77, 69], [63, 88], [71, 66], [30, 73], [0, 1]], ![[0, 1], [0, 15], [24, 28], [91, 9], [92, 31], [40, 24], [40, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [16, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [72, 57, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1657, 3715, -5618, 2124, 8375]
  a := ![1, 5, -3, 4, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4046, -464, -5618, 2124, 8375]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![655024966, 1303241617, 970992884, 247690696, 237355741]] ![![34, 103, -50, -106, 109]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![97, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0, 0, 0]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]] where
  M :=![![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 5 2 6 [34, 59, 45, 48, 48, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 67, 12, 5, 95], [69, 78, 88, 15, 18], [81, 11, 81, 68, 29], [74, 45, 21, 13, 60], [0, 1]]
 g := ![![[8, 2, 57, 34, 17], [45, 41, 48, 31], [96, 89, 6, 58, 56], [20, 52, 53, 45], [53, 1], []], ![[98, 53, 57, 49, 80, 10, 84, 33], [76, 15, 28, 47], [63, 48, 71, 82, 55, 77, 74, 80], [73, 35, 66, 31], [71, 30, 16, 65], [59, 0, 49, 1, 31, 3, 0, 87]], ![[59, 41, 6, 80, 91, 53, 53, 34], [9, 62, 56, 100], [38, 90, 43, 15, 42, 3, 49, 26], [95, 99, 94, 71], [14, 47, 35, 52], [82, 55, 69, 63, 24, 33, 72, 75]], ![[99, 67, 58, 16, 33, 41, 63, 75], [91, 54, 66, 84], [30, 53, 11, 73, 93, 20, 60, 48], [70, 22, 15, 88], [16, 9, 11, 77], [86, 47, 70, 37, 82, 24, 85, 48]], ![[68, 16, 80, 44, 26, 28, 45, 50], [52, 10, 97, 5], [66, 80, 49, 85, 25, 27, 40, 38], [77, 79, 5, 88], [97, 24, 52, 21], [68, 7, 70, 76, 80, 86, 64, 62]]]
 h' := ![![[31, 67, 12, 5, 95], [100, 99, 28, 11, 57], [69, 93, 95, 39, 43], [81, 31, 45, 83, 64], [16, 71, 81, 37, 34], [0, 0, 0, 1], [0, 1]], ![[69, 78, 88, 15, 18], [96, 97, 25, 18, 34], [16, 36, 93, 69, 59], [23, 37, 66, 80, 85], [9, 83, 26, 58, 43], [10, 2, 19, 21, 41], [31, 67, 12, 5, 95]], ![[81, 11, 81, 68, 29], [11, 65, 30, 53, 82], [69, 84, 56, 40, 91], [7, 93, 95, 76, 22], [45, 85, 44, 94, 24], [97, 2, 90, 39, 70], [69, 78, 88, 15, 18]], ![[74, 45, 21, 13, 60], [38, 29, 32, 89, 90], [100, 19, 48, 2, 65], [67, 10, 93, 11, 29], [15, 35, 40, 87, 47], [85, 64, 16, 33, 73], [81, 11, 81, 68, 29]], ![[0, 1], [93, 13, 87, 31, 40], [12, 71, 11, 52, 45], [55, 31, 4, 53, 2], [59, 29, 11, 27, 54], [23, 33, 77, 7, 18], [74, 45, 21, 13, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 8, 57, 82], [], [], []]
 b := ![[], [22, 24, 85, 26, 81], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 5
  hpos := by decide
  P := [34, 59, 45, 48, 48, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![268128538, 490527710, -735884182, 161919261, 1034428466]
  a := ![4, 0, 0, 1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2654738, 4856710, -7285982, 1603161, 10241866]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10510100501 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1349316703, -2684616638, -2000205676, -510231878, -488943242]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-1349316703, -2684616638, -2000205676, -510231878, -488943242]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![98, 12, 49, 62, 1]] where
  M :=![![![-1349316703, -2684616638, -2000205676, -510231878, -488943242], ![-2933659452, -5836815861, -4348769520, -1109329172, -1063041028], ![-3189123084, -6345105200, -4727486689, -1205934580, -1155617316], ![-2000022222, -3979257510, -2964785860, -756287419, -724731330], ![-214817700, -427410142, -318450700, -81232974, -77844233]]]
  hmulB := by decide  
  f := ![![![-20821, -17866, 14524, 19158, -19218]], ![![-115308, -25635, -74048, 221108, 115068]], ![![345204, 299032, -246743, -313212, 327148]], ![![1039098, 239558, 649268, -1979101, -1011106]], ![![738922, 254014, 285411, -1276128, -466241]]]
  g := ![![![452107971, 30900022, 213184594, 289361642, -488943242], ![982954964, 67181325, 463497484, 629118588, -1063041028], ![1068557028, 73032064, 503861765, 683906204, -1155617316], ![670132506, 45801150, 315990770, 428903447, -724731330], ![71979778, 4919618, 33940939, 46069024, -77844233]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 4 2 6 [26, 37, 19, 95, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 5, 77, 100], [25, 23, 78, 55], [95, 74, 51, 51], [0, 1]]
 g := ![![[36, 41, 28, 29], [82, 45, 8, 72], [17, 89, 75, 98], [13, 5, 92], [45, 8, 1], []], ![[14, 21, 74, 89, 67, 93], [33, 68, 61, 1, 62, 26], [84, 33, 87, 92, 33, 97], [18, 73, 4], [80, 65, 98], [89, 53, 14, 95, 9, 76]], ![[40, 55, 45, 95, 37, 72], [55, 98, 70, 94, 80, 32], [39, 13, 43, 74, 87, 30], [12, 34, 66], [91, 21, 66], [68, 84, 78, 43, 68, 30]], ![[3, 83, 84, 70, 72, 62], [1, 82, 56, 90], [102, 27, 70, 34, 54, 74], [36, 41, 28], [75, 62, 34], [22, 18, 57, 98, 63, 90]]]
 h' := ![![[94, 5, 77, 100], [31, 95, 49, 82], [73, 45, 41, 81], [1, 74, 72, 43], [66, 84, 59, 68], [0, 0, 0, 1], [0, 1]], ![[25, 23, 78, 55], [80, 45, 27, 81], [46, 84, 59, 67], [2, 54, 8, 38], [26, 86, 67, 101], [47, 46, 12, 43], [94, 5, 77, 100]], ![[95, 74, 51, 51], [13, 78, 24, 87], [62, 40, 55, 58], [30, 35, 102, 48], [41, 43, 19, 90], [55, 6, 71, 90], [25, 23, 78, 55]], ![[0, 1], [99, 91, 3, 59], [69, 37, 51], [70, 43, 24, 77], [39, 96, 61, 50], [49, 51, 20, 72], [95, 74, 51, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [75, 39, 24], []]
 b := ![[], [], [58, 24, 62, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 4
  hpos := by decide
  P := [26, 37, 19, 95, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2925173476, 289062301210, -605894085628, 446860697932, 868511785770]
  a := ![7, -21, -1, -21, -44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-826322619728, -98379409010, -419057976586, -518455048736, 868511785770]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 112550881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20821, -17866, 14524, 19158, -19218]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-20821, -17866, 14524, 19158, -19218]] 
 ![![103, 0, 0, 0, 0], ![63, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![88, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![-20821, -17866, 14524, 19158, -19218], ![-115308, -25635, -74048, 221108, 115068], ![345204, 299032, -246743, -313212, 327148], ![1039098, 239558, 649268, -1979101, -1011106], ![-1805952, -1283234, 698348, 2079686, -861955]]]
  hmulB := by decide  
  f := ![![![-1349316703, -2684616638, -2000205676, -510231878, -488943242]], ![![-853792347, -1698715185, -1265647836, -322853762, -309383158]], ![![-345366252, -687144704, -511965271, -130597084, -125148108]], ![![-1172231962, -2332286618, -1737697916, -443268861, -424774142]], ![![-578492744, -1150976138, -857548548, -218751802, -209624727]]]
  g := ![![![-817, -17866, 14524, 19158, -19218], ![-206249, -25635, -74048, 221108, 115068], ![5788, 299032, -246743, -313212, 327148], ![1835088, 239558, 649268, -1979101, -1011106], ![-803970, -1283234, 698348, 2079686, -861955]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-1349316703, -2684616638, -2000205676, -510231878, -488943242]] ![![-20821, -17866, 14524, 19158, -19218]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)


lemma PB1253I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB1253I2 : PrimesBelowBoundCertificateInterval O 61 103 1253 where
  m := 9
  g := ![2, 3, 4, 1, 2, 3, 2, 1, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB1253I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1, I73N2, I73N3]
    · exact ![I79N0]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![20151121, 67]
    · exact ![5041, 5041, 71]
    · exact ![5329, 73, 73, 73]
    · exact ![3077056399]
    · exact ![47458321, 83]
    · exact ![7921, 7921, 89]
    · exact ![912673, 9409]
    · exact ![10510100501]
    · exact ![112550881, 103]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
      exact NI73N3
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I67N1, I71N2, I73N1, I73N2, I73N3, I83N1, I89N2, I103N1]
  Il := ![[I67N1], [I71N2], [I73N1, I73N2, I73N3], [], [I83N1], [I89N2], [], [], [I103N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
