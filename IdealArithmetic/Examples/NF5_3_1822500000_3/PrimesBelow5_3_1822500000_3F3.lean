
import IdealArithmetic.Examples.NF5_3_1822500000_3.RI5_3_1822500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-219, 111, -1, -12, 13]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-219, 111, -1, -12, 13]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![49, 25, 74, 32, 1]] where
  M :=![![![-219, 111, -1, -12, 13], ![-76, -196, 49, -54, -209], ![728, 295, -154, 78, 397], ![-360, -33, 35, -115, -241], ![-44, -136, 34, -20, -121]]]
  hmulB := by decide  
  f := ![![![7, 11, 1, -4, -7]], ![![20, 26, 3, -10, -13]], ![![32, 63, 2, -22, -55]], ![![24, 15, 5, -9, 11]], ![![37, 59, 4, -22, -41]]]
  g := ![![![-8, -2, -9, -4, 13], ![95, 47, 145, 62, -209], ![-175, -90, -276, -118, 397], ![107, 56, 167, 71, -241], ![55, 27, 84, 36, -121]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 4 2 6 [66, 59, 28, 79, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 14, 17, 63], [51, 0, 65, 69], [85, 92, 25, 82], [0, 1]]
 g := ![![[60, 99, 30, 16], [12, 75, 76, 47], [10, 60, 39], [36, 95, 45, 25], [7, 28, 1], []], ![[54, 46, 87, 47, 5, 93], [106, 86, 106, 14, 34, 43], [65, 81, 86], [36, 16, 62, 22, 42, 98], [66, 33, 101], [0, 75, 64, 8, 67, 95]], ![[18, 33, 25, 87, 38, 75], [23, 106, 27, 105, 53, 16], [15, 36, 40], [32, 85, 74, 18, 93, 102], [33, 76, 62], [97, 26, 38, 35, 60, 19]], ![[17, 103, 39, 82, 51, 17], [17, 77, 66, 97, 73, 63], [60, 57, 16], [4, 100, 57, 90, 8, 7], [76, 58, 14], [3, 12, 83, 24, 32, 104]]]
 h' := ![![[106, 14, 17, 63], [64, 66, 28, 4], [38, 91, 100, 58], [85, 38, 36, 57], [73, 93, 12, 102], [0, 0, 0, 1], [0, 1]], ![[51, 0, 65, 69], [68, 29, 15, 46], [31, 50, 66, 93], [24, 92, 83, 73], [32, 106, 82, 75], [106, 14, 16, 23], [106, 14, 17, 63]], ![[85, 92, 25, 82], [25, 17, 17, 52], [93, 89, 44, 57], [86, 68, 6, 88], [83, 47, 100, 35], [96, 51, 105, 94], [51, 0, 65, 69]], ![[0, 1], [85, 102, 47, 5], [48, 91, 4, 6], [7, 16, 89, 103], [36, 75, 20, 2], [68, 42, 93, 96], [85, 92, 25, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [11, 45, 63], []]
 b := ![[], [], [76, 69, 46, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 4
  hpos := by decide
  P := [66, 59, 28, 79, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16614455370115, -65575481390064, 54989153950755, 88611260268293, 175482534495260]
  a := ![-55, 82, -115, -139, -330]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-80205885372875, -41613447138052, -120847835501855, -51652615360561, 175482534495260]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 131079601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -11, -1, 4, 7]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-7, -11, -1, 4, 7]] 
 ![![107, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![-7, -11, -1, 4, 7], ![-20, -26, -3, 10, 13], ![-32, -63, -2, 22, 55], ![-24, -15, -5, 9, -11], ![20, 18, 4, -8, 1]]]
  hmulB := by decide  
  f := ![![![219, -111, 1, 12, -13]], ![![101, -49, 0, 6, -4]], ![![116, -65, 2, 6, -11]], ![![75, -36, 0, 5, -2]], ![![70, -34, 0, 4, -3]]]
  g := ![![![2, -11, -1, 4, 7], ![6, -26, -3, 10, 13], ![5, -63, -2, 22, 55], ![10, -15, -5, 9, -11], ![-8, 18, 4, -8, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-219, 111, -1, -12, 13]] ![![-7, -11, -1, 4, 7]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![-107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1613287, 2693, -481065, 278228, -2431494]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-1613287, 2693, -481065, 278228, -2431494]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![45, 103, 100, 93, 1]] where
  M :=![![![-1613287, 2693, -481065, 278228, -2431494], ![10282432, -16477, 3066034, -1773478, 15496206], ![-65531780, 106660, -19540561, 11302292, -98762766], ![80531238, -130425, 24013099, -13889415, 121367350], ![-44931016, 72698, -13397688, 7749378, -67714705]]]
  hmulB := by decide  
  f := ![![![1533, 2999, -1853, -4450, -4642]], ![![9668, 19525, -12012, -28918, -30190]], ![![62924, 126612, -77969, -187744, -196066]], ![![57642, 115935, -71383, -171841, -179422]], ![![116615, 234637, -144474, -347835, -363211]]]
  g := ![![![989027, 2297675, 2226315, 2077130, -2431494], ![-6303182, -14643355, -14188574, -13237804, 15496206], ![40172410, 93327262, 90428771, 84369170, -98762766], ![-49366968, -114687775, -111125889, -103679385, 121367350], ![27543401, 63987957, 62000668, 57846027, -67714705]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 4 2 6 [24, 20, 102, 70, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 41, 59, 66], [5, 85, 100, 66], [80, 91, 59, 86], [0, 1]]
 g := ![![[11, 36], [108, 57, 74], [53, 30, 58, 87], [84, 7, 81, 16], [2, 39, 1], []], ![[0, 81, 42, 51, 2, 3], [105, 88, 71], [33, 44, 48, 68, 6, 80], [18, 22, 67, 49, 81, 25], [16, 91, 71], [23, 101, 103, 66, 5, 63]], ![[3, 53, 93, 52, 101, 94], [48, 39, 84], [95, 100, 55, 50, 55, 5], [77, 75, 92, 2, 85, 82], [13, 104, 88], [93, 79, 22, 63, 58, 63]], ![[85, 0, 34, 67, 52, 101], [53, 40, 16], [34, 97, 22, 26, 26, 37], [101, 15, 54, 99, 59, 2], [91, 26, 104], [44, 71, 3, 90, 75, 41]]]
 h' := ![![[63, 41, 59, 66], [12, 2, 6], [36, 46, 34, 69], [55, 20, 95, 14], [61, 5, 82, 4], [0, 0, 0, 1], [0, 1]], ![[5, 85, 100, 66], [15, 106, 91, 21], [79, 77, 50, 92], [101, 55, 89, 73], [88, 19, 79, 80], [103, 35, 11, 17], [63, 41, 59, 66]], ![[80, 91, 59, 86], [69, 104, 26, 56], [83, 37, 98, 53], [50, 43, 105, 9], [3, 80, 65, 8], [73, 3, 77, 52], [5, 85, 100, 66]], ![[0, 1], [84, 6, 95, 32], [87, 58, 36, 4], [62, 100, 38, 13], [11, 5, 101, 17], [61, 71, 21, 39], [80, 91, 59, 86]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [74, 53, 50], []]
 b := ![[], [], [81, 29, 95, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 4
  hpos := by decide
  P := [24, 20, 102, 70, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![357771362584994821, -1670925147352249438, 1381702872719723602, 2269359945471699780, 4372870141889879946]
  a := ![-689, 1003, -1441, -1754, -4137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1802031055251922961, -4147491282220274164, -3999131296479525422, -3710161130736579222, 4372870141889879946]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 141158161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1533, 2999, -1853, -4450, -4642]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![1533, 2999, -1853, -4450, -4642]] 
 ![![109, 0, 0, 0, 0], ![88, 1, 0, 0, 0], ![104, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![85, 0, 0, 0, 1]] where
  M :=![![![1533, 2999, -1853, -4450, -4642], ![9668, 19525, -12012, -28918, -30190], ![62924, 126612, -77969, -187744, -196066], ![57642, 115935, -71383, -171841, -179422], ![-6860, -13752, 8474, 20402, 21307]]]
  hmulB := by decide  
  f := ![![![-1613287, 2693, -481065, 278228, -2431494]], ![![-1208136, 2023, -360254, 208354, -1820874]], ![![-2140492, 3548, -638269, 369156, -3226038]], ![![-90026, 187, -26849, 15517, -135746]], ![![-1670279, 2767, -498057, 288062, -2517355]]]
  g := ![![![5267, 2999, -1853, -4450, -4642], ![34186, 19525, -12012, -28918, -30190], ![222102, 126612, -77969, -187744, -196066], ![203240, 115935, -71383, -171841, -179422], ![-24143, -13752, 8474, 20402, 21307]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-1613287, 2693, -481065, 278228, -2431494]] ![![1533, 2999, -1853, -4450, -4642]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22395, 31483, 3295, -11578, -17688]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![22395, 31483, 3295, -11578, -17688]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![107, 61, 11, 31, 1]] where
  M :=![![![22395, 31483, 3295, -11578, -17688], ![47596, 74817, 6154, -26542, -50496], ![148900, 177718, 25299, -69244, -66024], ![-3882, 40823, -5539, -9323, -72464], ![-17572, -51344, 274, 15606, 57357]]]
  hmulB := by decide  
  f := ![![![155, 317, -85, 72, 320]], ![![-1136, -381, 200, -222, -736]], ![![2500, 266, -333, 312, 1016]], ![![-990, 47, 83, -177, -392]], ![![-501, 131, 19, -71, -107]]]
  g := ![![![16947, 9827, 1751, 4750, -17688], ![48236, 27921, 4970, 13618, -50496], ![63836, 37214, 6651, 17500, -66024], ![68582, 39479, 7005, 19797, -72464], ![-54467, -31417, -5581, -15597, 57357]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 4 2 6 [55, 29, 95, 55, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 111, 106, 73], [61, 88, 94, 38], [47, 26, 26, 2], [0, 1]]
 g := ![![[42, 60, 44, 8], [22, 18, 22], [39, 40, 4], [52, 93, 22], [99, 105, 58, 1], []], ![[87, 73, 86, 80, 14, 5], [61, 98, 77], [15, 111, 36], [81], [90, 16, 37, 43, 19, 92], [72, 112, 92, 109, 11, 71]], ![[79, 2, 41, 111, 112, 39], [2, 33, 77], [65, 38, 13], [77, 106, 88], [32, 108, 74, 75, 89, 33], [48, 75, 81, 52, 0, 67]], ![[106, 74, 108, 65, 29, 85], [70, 38, 22], [65, 15, 104], [90, 108, 85], [77, 29, 77, 81, 102, 26], [93, 24, 25, 26, 98, 8]]]
 h' := ![![[63, 111, 106, 73], [83, 111, 91, 102], [84, 46, 45, 94], [67, 107, 65, 2], [92, 55, 67, 19], [0, 0, 0, 1], [0, 1]], ![[61, 88, 94, 38], [26, 45, 14, 50], [68, 43, 77, 23], [21, 111, 33, 6], [71, 3, 9], [86, 30, 4, 3], [63, 111, 106, 73]], ![[47, 26, 26, 2], [33, 85, 83, 2], [16, 40, 89, 90], [75, 23, 85, 37], [4, 22, 74, 38], [36, 55, 20, 72], [61, 88, 94, 38]], ![[0, 1], [10, 98, 38, 72], [73, 97, 15, 19], [91, 98, 43, 68], [42, 33, 76, 56], [59, 28, 89, 37], [47, 26, 26, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [56, 29, 52], []]
 b := ![[], [], [44, 16, 69, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 4
  hpos := by decide
  P := [55, 29, 95, 55, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15197862302665, -61803755042721, 51689452809953, 83595147670660, 164696247908891]
  a := ![-54, 80, -113, -137, -325]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-155816820034944, -89453759977744, -15574949329096, -44442376438097, 164696247908891]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 163047361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-155, -317, 85, -72, -320]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-155, -317, 85, -72, -320]] 
 ![![113, 0, 0, 0, 0], ![85, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![88, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![-155, -317, 85, -72, -320], ![1136, 381, -200, 222, 736], ![-2500, -266, 333, -312, -1016], ![990, -47, -83, 177, 392], ![712, 258, -132, 130, 459]]]
  hmulB := by decide  
  f := ![![![-22395, -31483, -3295, 11578, 17688]], ![![-17267, -24344, -2533, 8944, 13752]], ![![-2705, -3523, -428, 1330, 1680]], ![![-17406, -24879, -2517, 9099, 14416]], ![![-6781, -9297, -1023, 3448, 4971]]]
  g := ![![![387, -317, 85, -72, -320], ![-665, 381, -200, 222, 736], ![715, -266, 333, -312, -1016], ![-210, -47, -83, 177, 392], ![-423, 258, -132, 130, 459]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![22395, 31483, 3295, -11578, -17688]] ![![-155, -317, 85, -72, -320]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![-113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0, 0, 0]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![0, 0, 0, 0, 127]] where
  M :=![![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![0, 0, 0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 5 2 6 [110, 116, 59, 22, 116, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 86, 12, 42, 33], [114, 100, 19, 108, 81], [121, 89, 58, 79, 25], [59, 105, 38, 25, 115], [0, 1]]
 g := ![![[73, 67, 125, 5, 87], [22, 111, 109, 100, 79], [19, 103, 18, 85, 98], [24, 112, 76, 69, 41], [99, 11, 1], []], ![[28, 8, 27, 24, 84, 108, 74, 123], [39, 57, 111, 72, 112, 113, 121, 23], [6, 15, 15, 93, 3, 73, 16, 75], [51, 44, 78, 78, 45, 67, 111, 23], [124, 35, 109, 44, 85, 68, 59, 3], [98, 126, 53, 33, 36, 43, 10, 123]], ![[72, 34, 119, 70, 93, 26, 72, 88], [55, 63, 125, 74, 63, 23, 83, 120], [38, 35, 21, 7, 90, 79, 62, 30], [36, 93, 44, 11, 89, 47, 90, 76], [80, 53, 106, 99, 69, 80, 82, 42], [92, 125, 97, 124, 36, 80, 79, 73]], ![[51, 84, 64, 25, 54, 16, 52, 38], [15, 38, 28, 67, 60, 116, 31, 113], [84, 112, 111, 20, 41, 78, 116, 81], [27, 88, 107, 120, 120, 14, 38, 11], [106, 107, 32, 17, 3, 61, 33, 84], [32, 64, 79, 121, 69, 98, 87, 4]], ![[81, 102, 108, 108, 77, 48, 123, 79], [65, 60, 101, 32, 48, 62, 68, 64], [55, 101, 5, 69, 60, 10, 53, 49], [64, 30, 23, 18, 28, 108, 107, 100], [50, 101, 126, 116, 108, 106, 79, 99], [4, 59, 54, 35, 100, 64, 47, 50]]]
 h' := ![![[98, 86, 12, 42, 33], [120, 32, 113, 40, 77], [69, 22, 93, 59, 29], [27, 17, 95, 122, 112], [32, 6, 12, 105, 26], [0, 0, 0, 1], [0, 1]], ![[114, 100, 19, 108, 81], [41, 87, 38, 95, 94], [57, 109, 122, 37, 45], [40, 64, 114, 14, 21], [97, 61, 2, 28, 82], [10, 107, 41, 34, 55], [98, 86, 12, 42, 33]], ![[121, 89, 58, 79, 25], [121, 20, 20, 85, 22], [125, 107, 29, 0, 122], [1, 68, 58, 34, 61], [38, 86, 40, 125, 75], [2, 116, 7, 29, 55], [114, 100, 19, 108, 81]], ![[59, 105, 38, 25, 115], [80, 91, 41, 4, 63], [32, 54, 66, 12, 110], [104, 118, 116, 88, 78], [61, 5, 101, 33, 6], [74, 3, 116, 81, 67], [121, 89, 58, 79, 25]], ![[0, 1], [68, 24, 42, 30, 125], [89, 89, 71, 19, 75], [51, 114, 125, 123, 109], [38, 96, 99, 90, 65], [88, 28, 90, 109, 77], [59, 105, 38, 25, 115]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 4, 97, 88], [], [], []]
 b := ![[], [20, 95, 72, 126, 82], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 5
  hpos := by decide
  P := [110, 116, 59, 22, 116, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![155446480121223668890, -994391014199476665433, 805204420306103377615, 1360567260260284230494, 2515959178298741649689]
  a := ![246, -359, 514, 624, 1475]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1223988032450580070, -7829850505507690279, 6340192285874829745, 10713128033545545122, 19810702191328674407]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 33038369407 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0, 0, 0]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]] where
  M :=![![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 5 2 7 [60, 97, 105, 73, 78, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 121, 4, 120, 126], [17, 96, 4, 43, 124], [12, 87, 118, 48, 46], [115, 88, 5, 51, 97], [0, 1]]
 g := ![![[43, 101, 128, 60, 64], [5, 33, 38, 113, 113], [111, 130, 42, 112], [79, 62, 122, 28], [78, 116, 53, 1], [], []], ![[14, 7, 79, 66, 99, 18, 46, 70], [5, 28, 54, 122, 88, 77, 98, 26], [45, 108, 99, 62], [70, 130, 64, 60], [62, 22, 94, 113], [98, 27, 29, 101], [20, 34, 125, 25]], ![[129, 71, 25, 84, 82, 89, 74, 51], [96, 43, 43, 10, 7, 42, 120, 98], [6, 2, 128, 52], [41, 11, 55, 102], [0, 86, 33, 11], [30, 12, 43, 25], [116, 68, 30, 49]], ![[73, 94, 75, 8, 86, 42, 116, 77], [79, 116, 68, 70, 111, 118, 80, 13], [4, 19, 107, 61], [2, 56, 98, 39], [5, 10, 127, 25], [114, 49, 110, 129], [14, 104, 105, 20]], ![[120, 121, 84, 34, 88, 103, 108, 24], [85, 51, 38, 98, 87, 13, 55, 103], [71, 30, 52, 94], [47, 74, 2, 74], [49, 122, 27, 9], [47, 49, 106, 89], [49, 106, 29, 108]]]
 h' := ![![[40, 121, 4, 120, 126], [93, 76, 0, 110, 123], [24, 76, 87, 88, 47], [93, 46, 19, 9, 51], [36, 15, 41, 112, 91], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[17, 96, 4, 43, 124], [123, 89, 99, 55, 36], [19, 119, 9, 66, 105], [19, 61, 76, 114, 113], [114, 43, 11, 55, 86], [64, 30, 120, 0, 47], [7, 67, 98, 35, 25], [40, 121, 4, 120, 126]], ![[12, 87, 118, 48, 46], [60, 97, 18, 115, 57], [81, 20, 1, 117, 36], [110, 14, 86, 109, 24], [9, 91, 92, 30, 44], [3, 111, 97, 71, 81], [10, 115, 42, 29, 5], [17, 96, 4, 43, 124]], ![[115, 88, 5, 51, 97], [53, 6, 129, 36, 66], [42, 101, 67, 16, 49], [85, 72, 78, 84, 89], [104, 59, 51, 104, 68], [81, 20, 25, 116, 5], [90, 123, 10, 60, 28], [12, 87, 118, 48, 46]], ![[0, 1], [27, 125, 16, 77, 111], [21, 77, 98, 106, 25], [73, 69, 3, 77, 116], [50, 54, 67, 92, 104], [97, 101, 20, 75, 128], [67, 88, 111, 7, 73], [115, 88, 5, 51, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 128, 83, 15], [], [], []]
 b := ![[], [53, 92, 88, 113, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 5
  hpos := by decide
  P := [60, 97, 105, 73, 78, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8932487310508758, 26720856909572562, -23049211816260072, -35729660044420776, -74756895449626581]
  a := ![-31, 46, -64, -76, -185]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-68186926034418, 203976006943302, -175948181803512, -272745496522296, -570663324042951]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 38579489651 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-675, -443, 243, -220, -393]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-675, -443, 243, -220, -393]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![31, 120, 82, 3, 1]] where
  M :=![![![-675, -443, 243, -220, -393], ![1132, 378, -687, 578, -675], ![3856, 73, 2678, -1810, 10311], ![-8120, -183, -2913, 1773, -13931], ![6756, 246, 1360, -672, 8681]]]
  hmulB := by decide  
  f := ![![![5093, 7371, 727, -2684, -4367]], ![![12100, 17512, 1729, -6374, -10373]], ![![28744, 41595, 4118, -15122, -24623]], ![![6584, 9523, 955, -3443, -5621]], ![![29039, 42024, 4156, -15285, -24883]]]
  g := ![![![84, 341, 237, 7, -393], ![161, 594, 399, 19, -675], ![-2305, -9031, -6152, -239, 10311], ![3093, 12201, 8317, 318, -13931], ![-1915, -7602, -5186, -195, 8681]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 4 2 7 [49, 92, 9, 61, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 33, 109, 124], [123, 85, 65, 61], [62, 18, 100, 89], [0, 1]]
 g := ![![[19, 77, 18, 107], [123, 17, 14], [32, 99, 36], [89, 110, 65, 17], [98, 30, 22], [1], []], ![[41, 90, 50, 110, 70, 40], [89, 65, 78], [51, 126, 129], [14, 87, 0, 28, 85, 90], [100, 116, 93], [18, 37, 129], [48, 9, 32]], ![[87, 82, 87, 73, 112, 118], [133, 0, 36], [134, 15, 36], [33, 108, 38, 131, 43, 128], [136, 56, 63], [67, 52, 19], [102, 12, 22]], ![[113, 82, 48, 61, 89, 125], [86, 106, 133], [65, 2, 118], [56, 128, 81, 24, 121, 57], [63], [51, 89, 36], [63, 8, 112]]]
 h' := ![![[28, 33, 109, 124], [99, 97, 126, 45], [57, 93, 34, 39], [23, 100, 20, 6], [65, 37, 105, 47], [88, 45, 128, 76], [0, 0, 1], [0, 1]], ![[123, 85, 65, 61], [96, 35, 0, 93], [115, 77, 37, 30], [55, 26, 13, 102], [106, 22, 38, 71], [99, 31, 128, 97], [76, 5, 118, 102], [28, 33, 109, 124]], ![[62, 18, 100, 89], [98, 96, 82, 68], [83, 104, 91, 131], [115, 9, 13, 6], [88, 81, 118, 59], [54, 90, 119, 101], [130, 115, 113, 29], [123, 85, 65, 61]], ![[0, 1], [105, 46, 66, 68], [88, 0, 112, 74], [81, 2, 91, 23], [75, 134, 13, 97], [82, 108, 36], [72, 17, 42, 6], [62, 18, 100, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [109, 125, 86], []]
 b := ![[], [], [127, 125, 27, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 4
  hpos := by decide
  P := [49, 92, 9, 61, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1561045680353, -83667371727180, 64329159155792, 116489937085932, 194375203388112]
  a := ![-56, 84, -118, -150, -336]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-43971315761687, -170866363345260, -115871806705616, -3406099803492, 194375203388112]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 352275361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5093, 7371, 727, -2684, -4367]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![5093, 7371, 727, -2684, -4367]] 
 ![![137, 0, 0, 0, 0], ![106, 1, 0, 0, 0], ![135, 0, 1, 0, 0], ![127, 0, 0, 1, 0], ![119, 0, 0, 0, 1]] where
  M :=![![![5093, 7371, 727, -2684, -4367], ![12100, 17512, 1729, -6374, -10373], ![28744, 41595, 4118, -15122, -24623], ![6584, 9523, 955, -3443, -5621], ![-8300, -12012, -1186, 4372, 7115]]]
  hmulB := by decide  
  f := ![![![-675, -443, 243, -220, -393]], ![![-514, -340, 183, -166, -309]], ![![-637, -436, 259, -230, -312]], ![![-685, -412, 204, -191, -466]], ![![-537, -383, 221, -196, -278]]]
  g := ![![![-101, 7371, 727, -2684, -4367], ![-246, 17512, 1729, -6374, -10373], ![-625, 41595, 4118, -15122, -24623], ![-187, 9523, 955, -3443, -5621], ![169, -12012, -1186, 4372, 7115]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-675, -443, 243, -220, -393]] ![![5093, 7371, 727, -2684, -4367]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -40, 24, 60, 64]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-17, -40, 24, 60, 64]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![88, 13, 1, 0, 0], ![119, 77, 0, 1, 0], ![131, 70, 0, 0, 1]] where
  M :=![![![-17, -40, 24, 60, 64], ![-136, -261, 160, 384, 400], ![-832, -1688, 1035, 2496, 2608], ![-768, -1540, 948, 2283, 2384], ![88, 184, -112, -272, -285]]]
  hmulB := by decide  
  f := ![![![-27, -24, 8, -4, 0]], ![![-8, -15, -32, 32, -48]], ![![-16, -17, 3, 0, 0]], ![![-31, -29, -12, 15, -32]], ![![-27, -30, -8, 12, -21]]]
  g := ![![![-127, -68, 24, 60, 64], ![-808, -431, 160, 384, 400], ![-5256, -2805, 1035, 2496, 2608], ![-4807, -2565, 948, 2283, 2384], ![573, 306, -112, -272, -285]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [13, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 138], [0, 1]]
 g := ![![[86, 107], [103, 83], [112], [33, 118], [125], [36], [1]], ![[0, 32], [22, 56], [112], [20, 21], [125], [36], [1]]]
 h' := ![![[133, 138], [51, 78], [78, 19], [127, 116], [67, 102], [118, 79], [126, 133], [0, 1]], ![[0, 1], [0, 61], [103, 120], [126, 23], [11, 37], [61, 60], [23, 6], [133, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [122, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [13, 6, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![209469, -178856, 198742, 213476, 725412]
  a := ![-26, 45, -55, -58, -169]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-990737, -503446, 198742, 213476, 725412]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -4, 2, 0, 13]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![1, -4, 2, 0, 13]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![103, 75, 1, 0, 0], ![39, 17, 0, 1, 0], ![27, 63, 0, 0, 1]] where
  M :=![![![1, -4, 2, 0, 13], ![-52, -12, -15, 12, -65], ![284, -23, 86, -42, 469], ![-374, -6, -110, 65, -553], ![212, 6, 62, -38, 305]]]
  hmulB := by decide  
  f := ![![![-21, 20, -6, -14, -11]], ![![16, 32, -31, -92, -113]], ![![-5, 35, -23, -64, -73]], ![![-3, 12, -7, -19, -21]], ![![3, 18, -15, -44, -53]]]
  g := ![![![-4, -7, 2, 0, 13], ![20, 36, -15, 12, -65], ![-141, -254, 86, -42, 469], ![168, 302, -110, 65, -553], ![-93, -167, 62, -38, 305]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P1 : CertificateIrreducibleZModOfList' 139 2 2 7 [118, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [137, 138], [0, 1]]
 g := ![![[33, 86], [78, 46], [49], [97, 113], [124], [4], [1]], ![[0, 53], [125, 93], [49], [10, 26], [124], [4], [1]]]
 h' := ![![[137, 138], [109, 124], [136, 18], [91, 132], [90, 35], [108, 47], [21, 137], [0, 1]], ![[0, 1], [0, 15], [100, 121], [105, 7], [20, 104], [14, 92], [25, 2], [137, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120]]
 b := ![[], [60, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N1 : CertifiedPrimeIdeal' SI139N1 139 where
  n := 2
  hpos := by decide
  P := [118, 2, 1]
  hirr := P139P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44658, -166072, 140691, 225326, 448714]
  a := ![-22, 31, -46, -58, -131]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-254313, -308039, 140691, 225326, 448714]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N1 B_one_repr
lemma NI139N1 : Nat.card (O ⧸ I139N1) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -4, 2, -2, -7]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![-13, -4, 2, -2, -7]] 
 ![![139, 0, 0, 0, 0], ![51, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-13, -4, 2, -2, -7], ![24, 0, -3, 4, 11], ![-36, 1, 2, -2, -7], ![10, -4, 0, 1, 3], ![16, 2, -2, 2, 5]]]
  hmulB := by decide  
  f := ![![![-7, -20, 2, 20, 25]], ![![-3, -8, 1, 8, 10]], ![![-4, -9, 2, 10, 11]], ![![-2, -6, 2, 7, 9]], ![![-1, -2, 0, 2, 2]]]
  g := ![![![2, -4, 2, -2, -7], ![-1, 0, -3, 4, 11], ![0, 1, 2, -2, -7], ![1, -4, 0, 1, 3], ![-1, 2, -2, 2, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-17, -40, 24, 60, 64]] ![![1, -4, 2, 0, 13]]
  ![![7, 20, -2, -20, -25]] where
 M := ![![![7, 20, -2, -20, -25]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![7, 20, -2, -20, -25]] ![![-13, -4, 2, -2, -7]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![-139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-307, -439, -53, 144, 246]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-307, -439, -53, 144, 246]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![70, 79, 77, 1, 0], ![88, 104, 28, 0, 1]] where
  M :=![![![-307, -439, -53, 144, 246], ![-696, -985, -162, 258, 498], ![-1476, -1968, -613, 60, 606], ![-138, -49, -389, -583, -486], ![480, 674, 112, -174, -337]]]
  hmulB := by decide  
  f := ![![![97, 35, -17, 18, 66]], ![![-228, -23, 24, -30, -114]], ![![396, -24, -5, 24, 210]], ![![128, -8, 2, 5, 78]], ![![-28, 0, 6, -6, -1]]]
  g := ![![![-215, -251, -121, 144, 246], ![-420, -491, -228, 258, 498], ![-396, -468, -149, 60, 606], ![560, 648, 390, -583, -486], ![284, 332, 154, -174, -337]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [98, 46, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 86, 19], [7, 62, 130], [0, 1]]
 g := ![![[134, 135, 19], [3, 102], [70, 28, 121], [20, 63], [109, 78, 80], [136, 1], []], ![[40, 17, 136, 31], [147, 119], [128, 53, 33, 19], [121, 46], [7, 59, 125, 49], [57, 119], [65, 63]], ![[147, 27, 84, 63], [63, 125], [108, 52, 12, 37], [133, 22], [64, 19, 17, 118], [44, 95], [103, 63]]]
 h' := ![![[129, 86, 19], [40, 54, 67], [143, 45, 129], [7, 66, 11], [46, 26, 19], [82, 53, 123], [0, 0, 1], [0, 1]], ![[7, 62, 130], [78, 89, 114], [39, 117, 62], [67, 89, 148], [81, 117, 33], [27, 141, 140], [139, 61, 62], [129, 86, 19]], ![[0, 1], [138, 6, 117], [59, 136, 107], [85, 143, 139], [93, 6, 97], [128, 104, 35], [87, 88, 86], [7, 62, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103, 126], []]
 b := ![[], [80, 47, 111], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [98, 46, 13, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![702112742, -1630863045, 1453522457, 2153547060, 4798740410]
  a := ![33, -48, 69, 80, 195]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3841176762, -4502215325, -2004928407, 2153547060, 4798740410]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-97, -35, 17, -18, -66]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-97, -35, 17, -18, -66]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![124, 135, 1, 0, 0], ![70, 40, 0, 1, 0], ![143, 56, 0, 0, 1]] where
  M :=![![![-97, -35, 17, -18, -66], ![228, 23, -24, 30, 114], ![-396, 24, 5, -24, -210], ![198, -23, 23, -7, 162], ![84, 16, -34, 30, -19]]]
  hmulB := by decide  
  f := ![![![307, 439, 53, -144, -246]], ![![696, 985, 162, -258, -498]], ![![896, 1271, 195, -354, -660]], ![![332, 471, 71, -133, -246]], ![![553, 787, 111, -234, -421]]]
  g := ![![![57, 14, 17, -18, -66], ![-102, -29, -24, 30, 114], ![206, 81, 5, -24, -210], ![-170, -80, 23, -7, 162], ![33, 30, -34, 30, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P1 : CertificateIrreducibleZModOfList' 149 2 2 7 [55, 125, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 148], [0, 1]]
 g := ![![[70, 7], [42], [6, 110], [130], [55, 81], [129], [1]], ![[89, 142], [42], [113, 39], [130], [62, 68], [129], [1]]]
 h' := ![![[24, 148], [55, 56], [117, 108], [90, 40], [104, 117], [102, 9], [94, 24], [0, 1]], ![[0, 1], [58, 93], [27, 41], [7, 109], [81, 32], [20, 140], [74, 125], [24, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [134, 113]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N1 : CertifiedPrimeIdeal' SI149N1 149 where
  n := 2
  hpos := by decide
  P := [55, 125, 1]
  hirr := P149P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![108151, -252467, 227989, 337384, 746627]
  a := ![28, -41, 58, 70, 167]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1064074, -579446, 227989, 337384, 746627]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N1 B_one_repr
lemma NI149N1 : Nat.card (O ⧸ I149N1) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-307, -439, -53, 144, 246]] ![![-97, -35, 17, -18, -66]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![-149, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6347, -10227, -799, 3602, 7106]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-6347, -10227, -799, 3602, 7106]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![33, 122, 79, 115, 1]] where
  M :=![![![-6347, -10227, -799, 3602, 7106], ![-21220, -24259, -3724, 9614, 7694], ![-11548, -57756, 2779, 16112, 76898], ![-43970, -13171, -11701, 10835, -44674], ![30956, 16632, 7438, -9418, 19447]]]
  hmulB := by decide  
  f := ![![![2667, 5353, -3297, -7936, -8286]], ![![17272, 34761, -21402, -51526, -53802]], ![![112156, 225652, -138943, -334516, -349302]], ![![102670, 206559, -127185, -306201, -319730]], ![![151327, 304462, -187467, -451335, -471279]]]
  g := ![![![-1595, -5809, -3723, -5388, 7106], ![-1822, -6377, -4050, -5796, 7694], ![-16882, -62512, -40213, -58458, 76898], ![9472, 36007, 23295, 34095, -44674], ![-4045, -15602, -10125, -14873, 19447]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 4 2 7 [97, 14, 42, 83, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 146, 56, 85], [20, 130, 108, 20], [141, 25, 138, 46], [0, 1]]
 g := ![![[57, 18, 75, 121], [34, 148, 23, 44], [46, 37, 17, 5], [74, 131, 50], [140, 23, 76, 94], [1], []], ![[137, 92, 118, 9, 64, 39], [92, 62, 25, 47, 10, 138], [1, 5, 141, 45, 114, 136], [26, 113, 16], [0, 115, 113, 2, 146, 17], [126, 116, 4], [56, 104, 128]], ![[61, 60, 99, 123, 109, 29], [141, 128, 90, 115, 115, 76], [6, 31, 12, 103, 35, 31], [20, 80, 123], [118, 117, 148, 107, 26, 69], [50, 41, 128], [130, 112, 98]], ![[92, 81, 27, 70, 32, 79], [24, 3, 29, 142, 143, 83], [106, 144, 131, 17, 36, 63], [5, 31, 8], [40, 119, 35, 75, 88, 79], [100, 80, 19], [67, 148, 2]]]
 h' := ![![[58, 146, 56, 85], [24, 60, 103, 11], [68, 54, 20, 73], [19, 17, 111, 55], [10, 84, 14, 72], [54, 137, 109, 68], [0, 0, 1], [0, 1]], ![[20, 130, 108, 20], [123, 38, 72, 41], [138, 91, 81, 68], [95, 63, 117, 106], [72, 142, 103, 147], [11, 64, 103, 140], [46, 24, 112, 2], [58, 146, 56, 85]], ![[141, 25, 138, 46], [4, 77, 33, 3], [65, 75, 129, 100], [120, 49, 46, 30], [61, 122, 142, 24], [121, 58, 46, 39], [21, 66, 5, 85], [20, 130, 108, 20]], ![[0, 1], [136, 127, 94, 96], [56, 82, 72, 61], [12, 22, 28, 111], [73, 105, 43, 59], [42, 43, 44, 55], [94, 61, 33, 64], [141, 25, 138, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [112, 69, 126], []]
 b := ![[], [], [8, 11, 86, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 4
  hpos := by decide
  P := [97, 14, 42, 83, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2119513821, -4462160707, 2776939911, 6597964142, 7055114392]
  a := ![4, -4, 8, 13, 20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1555882707, -5729709381, -3672696007, -5329405238, 7055114392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 519885601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2667, 5353, -3297, -7936, -8286]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![2667, 5353, -3297, -7936, -8286]] 
 ![![151, 0, 0, 0, 0], ![135, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![121, 0, 0, 0, 1]] where
  M :=![![![2667, 5353, -3297, -7936, -8286], ![17272, 34761, -21402, -51526, -53802], ![112156, 225652, -138943, -334516, -349302], ![102670, 206559, -127185, -306201, -319730], ![-12192, -24522, 15100, 36354, 37961]]]
  hmulB := by decide  
  f := ![![![-6347, -10227, -799, 3602, 7106]], ![![-5815, -9304, -739, 3284, 6404]], ![![-2010, -3498, -225, 1204, 2674]], ![![-5125, -7876, -686, 2815, 5116]], ![![-4881, -8085, -591, 2824, 5823]]]
  g := ![![![8920, 5353, -3297, -7936, -8286], ![57911, 34761, -21402, -51526, -53802], ![375996, 225652, -138943, -334516, -349302], ![344160, 206559, -127185, -306201, -319730], ![-40863, -24522, 15100, 36354, 37961]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-6347, -10227, -799, 3602, 7106]] ![![2667, 5353, -3297, -7936, -8286]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)


lemma PB2088I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB2088I3 : PrimesBelowBoundCertificateInterval O 103 151 2088 where
  m := 9
  g := ![2, 2, 2, 1, 1, 2, 3, 2, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB2088I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0]
    · exact ![I137N0, I137N1]
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
    · exact PBC139
    · exact PBC149
    · exact PBC151
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![131079601, 107]
    · exact ![141158161, 109]
    · exact ![163047361, 113]
    · exact ![33038369407]
    · exact ![38579489651]
    · exact ![352275361, 137]
    · exact ![19321, 19321, 139]
    · exact ![3307949, 22201]
    · exact ![519885601, 151]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I107N1, I109N1, I113N1, I137N1, I139N2, I151N1]
  Il := ![[I107N1], [I109N1], [I113N1], [], [], [I137N1], [I139N2], [], [I151N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
