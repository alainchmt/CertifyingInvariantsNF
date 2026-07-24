
import IdealArithmetic.Examples.NF3_1_782987_1.RI3_1_782987_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0]] 
 ![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [143, 161, 113, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 10, 171], [24, 186, 26], [0, 1]]
 g := ![![[23, 68, 188], [11, 4], [19, 104, 1], [84, 92], [128, 178], [69, 161], [1]], ![[45, 15, 76, 142], [190, 90], [81, 47, 22, 55], [132, 76], [186, 134], [42, 83], [14, 75, 120, 154]], ![[105, 108, 115, 136], [196, 182], [28, 150, 88, 63], [33, 85], [148, 34], [138, 9], [178, 184, 19, 43]]]
 h' := ![![[60, 10, 171], [108, 84, 155], [41, 32, 195], [6, 10, 1], [1, 146, 17], [141, 94, 93], [54, 36, 84], [0, 1]], ![[24, 186, 26], [120, 100, 51], [33, 69, 175], [191, 127, 123], [130, 146, 154], [85, 102, 79], [56, 67, 110], [60, 10, 171]], ![[0, 1], [124, 13, 188], [104, 96, 24], [106, 60, 73], [140, 102, 26], [15, 1, 25], [190, 94, 3], [24, 186, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [151, 50], []]
 b := ![[], [21, 162, 108], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [143, 161, 113, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-78209, -46295, -5319]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-397, -235, -27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀

instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-394871, -70534, 42671]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-394871, -70534, 42671]] 
 ![![199, 0, 0], ![0, 199, 0], ![93, 109, 1]] where
  M :=![![![-394871, -70534, 42671], ![-5035178, -2229724, -27863], ![3287834, -3837069, -2257587]]]
  hmulB := by decide  
  f := ![![![-24758209359, 1622955843, -487989154]], ![![57582720172, -3774675737, 1134966689]], ![![19296869141, -1264952811, 380345069]]]
  g := ![![![-21926, -23727, 42671], ![-12281, 4057, -27863], ![1071575, 1217286, -2257587]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [54, 121, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [78, 198], [0, 1]]
 g := ![![[87, 8], [47, 62], [130, 130], [28], [165], [18], [78, 1]], ![[114, 191], [107, 137], [121, 69], [28], [165], [18], [156, 198]]]
 h' := ![![[78, 198], [49, 159], [144, 96], [89, 145], [3, 25], [117, 31], [166, 60], [0, 1]], ![[0, 1], [113, 40], [70, 103], [56, 54], [162, 174], [147, 168], [70, 139], [78, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [128, 160]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [54, 121, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![288, -1171, -29]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15, 10, -29]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24758209359, 1622955843, -487989154]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-24758209359, 1622955843, -487989154]] 
 ![![199, 0, 0], ![89, 1, 0], ![39, 0, 1]] where
  M :=![![![-24758209359, 1622955843, -487989154], ![57582720172, -3774675737, 1134966689], ![-133926069302, 8779152545, -2639709048]]]
  hmulB := by decide  
  f := ![![![-394871, -70534, 42671]], ![![-201903, -42750, 18944]], ![![-60865, -33105, -2982]]]
  g := ![![![-754621620, 1622955843, -487989154], ![1755101306, -3774675737, 1134966689], ![-4082020065, 8779152545, -2639709048]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-394871, -70534, 42671]] ![![-24758209359, 1622955843, -487989154]]
  ![![199, 0, 0]] where
 M := ![![![199, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0]] 
 ![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [2, 57, 106, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [172, 84, 179], [144, 126, 32], [0, 1]]
 g := ![![[125, 51, 189], [147, 17, 11], [13, 51], [202, 49], [114, 127, 80], [136, 53], [1]], ![[134, 203, 71, 82], [156, 55, 100, 143], [190, 209], [39, 209], [62, 23, 112, 126], [129, 54], [37, 123, 132, 148]], ![[160, 72, 139, 75], [202, 63, 19, 41], [113, 64], [102, 83], [72, 129, 109, 108], [21, 34], [194, 65, 172, 63]]]
 h' := ![![[172, 84, 179], [128, 1, 20], [117, 171, 125], [96, 91, 126], [194, 84, 7], [154, 177, 162], [209, 154, 105], [0, 1]], ![[144, 126, 32], [169, 37, 167], [67, 197, 150], [5, 195, 93], [111, 66, 93], [18, 76, 189], [109, 82, 73], [172, 84, 179]], ![[0, 1], [27, 173, 24], [158, 54, 147], [157, 136, 203], [19, 61, 111], [131, 169, 71], [157, 186, 33], [144, 126, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 46], []]
 b := ![[], [145, 24, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [2, 57, 106, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![149388, -2954, 2954]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![708, -14, 14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def PBC211 : ContainsPrimesAboveP 211 ![I211N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![211, 0, 0]]) timesTableT_eq_Table B_one_repr 211 (by decide) 𝕀

instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52933235420643421, -32020867388863174, -3982171094124262]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![-52933235420643421, -32020867388863174, -3982171094124262]] 
 ![![223, 0, 0], ![0, 223, 0], ![210, 111, 1]] where
  M :=![![![-52933235420643421, -32020867388863174, -3982171094124262], ![469896189106662916, 118300121626699845, -36003038482987436], ![4248358540992517448, 2018026843875122664, 82297083143712409]]]
  hmulB := by decide  
  f := ![![![-369465708812383530282911211281283, 24219301251171598981677921083174, -7282241460238147354495555027898]], ![![859304492308101387830475493291964, -56329326022143194039602345081669, 16937059790933451627182366055276]], ![![70835994350980113891317964985722, -4643457418896393651936605935801, 1396191317992791227626708956281]]]
  g := ![![![3512657822176913, 1838565578739596, -3982171094124262], ![36011364441856612, 18451288758916167, -36003038482987436], ![-58448560175726854, -31914571233528945, 82297083143712409]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [168, 132, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 222], [0, 1]]
 g := ![![[176, 18], [58, 32], [111, 110], [164, 169], [157, 202], [89], [91, 1]], ![[30, 205], [71, 191], [86, 113], [156, 54], [30, 21], [89], [182, 222]]]
 h' := ![![[91, 222], [68, 45], [84, 60], [100, 188], [161, 13], [201, 176], [99, 85], [0, 1]], ![[0, 1], [149, 178], [192, 163], [37, 35], [6, 210], [161, 47], [29, 138], [91, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132]]
 b := ![[], [119, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [168, 132, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-53, -1057, -785]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![739, 386, -785]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![236842599295449, 49802786028358, -22370691400444]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![236842599295449, 49802786028358, -22370691400444]] 
 ![![223, 0, 0], ![111, 1, 0], ![167, 0, 1]] where
  M :=![![![236842599295449, 49802786028358, -22370691400444], ![2639741585252392, 1198782329514541, 27432094627914], ![-3236987166093852, 1460161516252090, 1226214424142455]]]
  hmulB := by decide  
  f := ![![![1429908894971957909798003097895, -93733717265332810227703666850, 28183784288938837785814241416]], ![![696834981147051771878261270759, -45679087201364816368910835441, 13734753915227879021450633954]], ![![1105514249110006545669997621299, -72468924714889781846418598912, 21789902304143407277116948915]]]
  g := ![![![-6974713838467, 49802786028358, -22370691400444], ![-605409223290239, 1198782329514541, 27432094627914], ![-1659608629156349, 1460161516252090, 1226214424142455]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![-52933235420643421, -32020867388863174, -3982171094124262]] ![![236842599295449, 49802786028358, -22370691400444]]
  ![![223, 0, 0]] where
 M := ![![![-84173423583507265773838359066013, -46836885581712325091033781753432, -4577242024875226446727501703322]]]
 hmul := by decide  
 g := ![![![![-377459298580750070734701161731, -210030877048037332246788258984, -20525748990471867474114357414]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1148733347, -639744422, -62703575]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-1148733347, -639744422, -62703575]] 
 ![![227, 0, 0], ![0, 227, 0], ![199, 214, 1]] where
  M :=![![![-1148733347, -639744422, -62703575], ![7399021850, 1547520378, -702447997], ![82888863646, 37604285721, 845072381]]]
  hmulB := by decide  
  f := ![![![122126968783324365, -8005695189855259, 2407146466571692]], ![![-284043283055459656, 18619670720741609, -5598548723283567]], ![![-157803379016032409, 10344363451556130, -3110335497521844]]]
  g := ![![![49908714, 56294364, -62703575], ![648397239, 669036968, -702447997], ![-375685199, -631018519, 845072381]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [165, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [216, 226], [0, 1]]
 g := ![![[106, 21], [158, 188], [129], [43], [77], [130, 120], [216, 1]], ![[102, 206], [133, 39], [129], [43], [77], [172, 107], [205, 226]]]
 h' := ![![[216, 226], [35, 34], [51, 142], [212, 122], [66, 161], [115, 109], [226, 183], [0, 1]], ![[0, 1], [115, 193], [78, 85], [5, 105], [111, 66], [51, 118], [29, 44], [216, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [195]]
 b := ![[], [139, 211]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [165, 11, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-189, -258, -50]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![43, 46, -50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![122126968783324365, -8005695189855259, 2407146466571692]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![122126968783324365, -8005695189855259, 2407146466571692]] 
 ![![227, 0, 0], ![12, 1, 0], ![83, 0, 1]] where
  M :=![![![122126968783324365, -8005695189855259, 2407146466571692], ![-284043283055459656, 18619670720741609, -5598548723283567], ![660628749347460906, -43305687954266275, 13021121997458042]]]
  hmulB := by decide  
  f := ![![![-1148733347, -639744422, -62703575]], ![![-28131182, -27001818, -6409211]], ![![-54872265, -68257715, -19204072]]]
  g := ![![![81066759190031, -8005695189855259, 2407146466571692], ![-188545320140189, 18619670720741609, -5598548723283567], ![438519290791360, -43305687954266275, 13021121997458042]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-1148733347, -639744422, -62703575]] ![![122126968783324365, -8005695189855259, 2407146466571692]]
  ![![227, 0, 0]] where
 M := ![![![227, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0]] 
 ![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [226, 61, 63, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [219, 207, 225], [176, 21, 4], [0, 1]]
 g := ![![[73, 120, 147], [61, 148], [172, 118, 224], [119, 135], [29, 196], [20, 150, 76], [1]], ![[21, 7, 142, 26], [117, 129], [181, 228, 154, 132], [208, 71], [7, 4], [134, 48, 86, 209], [92, 198, 228, 165]], ![[46, 61, 216, 196], [89, 97], [139, 126, 184, 99], [41, 5], [81, 144], [35, 67, 211, 36], [133, 202, 182, 64]]]
 h' := ![![[219, 207, 225], [112, 41, 39], [58, 151, 47], [199, 19, 37], [23, 15, 89], [60, 155, 215], [3, 168, 166], [0, 1]], ![[176, 21, 4], [148, 120, 197], [207, 0, 154], [209, 29, 14], [57, 182, 206], [223, 122, 2], [192, 61, 66], [219, 207, 225]], ![[0, 1], [50, 68, 222], [142, 78, 28], [38, 181, 178], [217, 32, 163], [165, 181, 12], [143, 0, 226], [176, 21, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95, 110], []]
 b := ![[], [63, 81, 142], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [226, 61, 63, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-934091, -474259, -24961]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4079, -2071, -109]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 12008989 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def PBC229 : ContainsPrimesAboveP 229 ![I229N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![229, 0, 0]]) timesTableT_eq_Table B_one_repr 229 (by decide) 𝕀

instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0]] 
 ![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [77, 176, 148, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [126, 132, 192], [192, 100, 41], [0, 1]]
 g := ![![[189, 221, 2], [157, 85], [111, 46], [6, 66, 175], [70, 56], [58, 74, 2], [1]], ![[142, 85, 88, 190], [182, 89], [150, 9], [194, 152, 81, 93], [157, 203], [49, 26, 78, 228], [129, 27, 29, 47]], ![[15, 216, 153, 228], [209, 101], [177, 50], [41, 187, 99, 21], [188, 107], [9, 145, 223, 84], [201, 181, 54, 186]]]
 h' := ![![[126, 132, 192], [205, 23, 148], [90, 190, 28], [4, 229, 38], [92, 130, 116], [194, 42, 216], [156, 57, 85], [0, 1]], ![[192, 100, 41], [32, 70, 110], [149, 205, 136], [226, 14, 3], [85, 150, 212], [72, 151, 73], [157, 5, 105], [126, 132, 192]], ![[0, 1], [162, 140, 208], [90, 71, 69], [122, 223, 192], [140, 186, 138], [50, 40, 177], [181, 171, 43], [192, 100, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 197], []]
 b := ![[], [181, 196, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [77, 176, 148, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![106248, 18407, -7689]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![456, 79, -33]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def PBC233 : ContainsPrimesAboveP 233 ![I233N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![233, 0, 0]]) timesTableT_eq_Table B_one_repr 233 (by decide) 𝕀

instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0]] 
 ![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [78, 95, 169, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 14, 111], [14, 224, 128], [0, 1]]
 g := ![![[177, 151, 88], [215, 220, 75], [50, 237, 213], [72, 113, 50], [196, 226], [54, 119, 120], [1]], ![[168, 131, 64, 77], [115, 45, 222, 105], [196, 229, 151, 212], [110, 50, 61, 70], [151, 211], [203, 231, 109, 105], [200, 66, 138, 73]], ![[120, 16, 159, 166], [8, 19, 175, 187], [26, 48, 117, 202], [8, 125, 174, 187], [228, 30], [55, 135, 43, 96], [98, 76, 183, 166]]]
 h' := ![![[56, 14, 111], [199, 217, 142], [163, 7, 187], [120, 205, 149], [221, 48, 17], [90, 37, 86], [161, 144, 70], [0, 1]], ![[14, 224, 128], [85, 124, 208], [85, 199, 123], [197, 186, 205], [20, 138, 54], [200, 66, 188], [125, 14, 116], [56, 14, 111]], ![[0, 1], [66, 137, 128], [69, 33, 168], [139, 87, 124], [202, 53, 168], [135, 136, 204], [119, 81, 53], [14, 224, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [183, 58], []]
 b := ![[], [14, 139, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [78, 95, 169, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![90820, -9082, -18164]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![380, -38, -76]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def PBC239 : ContainsPrimesAboveP 239 ![I239N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![239, 0, 0]]) timesTableT_eq_Table B_one_repr 239 (by decide) 𝕀

instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-314037007180888801, -205975096294380080, -30506475575333063]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![-314037007180888801, -205975096294380080, -30506475575333063]] 
 ![![241, 0, 0], ![0, 241, 0], ![184, 111, 1]] where
  M :=![![![-314037007180888801, -205975096294380080, -30506475575333063], ![3599764117889301434, 997741442558432908, -236481571869713143], ![27904825480626150874, 13768471708286966583, 761259870688719765]]]
  hmulB := by decide  
  f := ![![![16661951673702015497471309614120029, -1092228094225577835272201131359969, 328410329815837916778753917232484]], ![![-38752418918268874179892962233433112, 2540307491620985075984891173123217, -763817764409739918493447214127485]], ![![-4753480895295953825938469160356626, 311601274621464581160013195105774, -93692039154173066838134755345967]]]
  g := ![![![21988192940582551, 13196031919367593, -30506475575333063], ![195487026315006306, 113058904232765941, -236481571869713143], ![-465423198033602846, -293491178166642852, 761259870688719765]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [200, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [197, 240], [0, 1]]
 g := ![![[140, 47], [81], [48], [182], [15, 67], [16, 232], [197, 1]], ![[0, 194], [81], [48], [182], [200, 174], [171, 9], [153, 240]]]
 h' := ![![[197, 240], [193, 218], [138, 232], [87, 224], [133, 69], [174, 84], [124, 49], [0, 1]], ![[0, 1], [0, 23], [52, 9], [112, 17], [230, 172], [93, 157], [137, 192], [197, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [67, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [200, 44, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4540, 596, -12]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![28, 8, -12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16661951673702015497471309614120029, -1092228094225577835272201131359969, 328410329815837916778753917232484]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![16661951673702015497471309614120029, -1092228094225577835272201131359969, 328410329815837916778753917232484]] 
 ![![241, 0, 0], ![129, 1, 0], ![229, 0, 1]] where
  M :=![![![16661951673702015497471309614120029, -1092228094225577835272201131359969, 328410329815837916778753917232484], ![-38752418918268874179892962233433112, 2540307491620985075984891173123217, -763817764409739918493447214127485], ![90130496200349310382226771267043230, -5908255048650057684674732025951257, 1776489727211245157491443958995732]]]
  hmulB := by decide  
  f := ![![![-314037007180888801, -205975096294380080, -30506475575333063]], ![![-153157717047491095, -106112223980981732, -17310443655965470]], ![![-182612652131939355, -138588486900938057, -25828726290715982]]]
  g := ![![![341715395439728934876558541549034, -1092228094225577835272201131359969, 328410329815837916778753917232484], ![-794762727334213724676118305108440, 2540307491620985075984891173123217, -763817764409739918493447214127485], ![1848461618028346932115047867239555, -5908255048650057684674732025951257, 1776489727211245157491443958995732]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![-314037007180888801, -205975096294380080, -30506475575333063]] ![![16661951673702015497471309614120029, -1092228094225577835272201131359969, 328410329815837916778753917232484]]
  ![![241, 0, 0]] where
 M := ![![![241, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0)


lemma PB251I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 250 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 250 (by omega)

def PB251I4 : PrimesBelowBoundCertificateInterval O 193 250 251 where
  m := 9
  g := ![1, 2, 1, 2, 2, 1, 1, 1, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241]
  hP := PB251I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1]
    · exact ![I211N0]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
    · exact ![I229N0]
    · exact ![I233N0]
    · exact ![I239N0]
    · exact ![I241N0, I241N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![7645373]
    · exact ![39601, 199]
    · exact ![9393931]
    · exact ![49729, 223]
    · exact ![51529, 227]
    · exact ![12008989]
    · exact ![12649337]
    · exact ![13651919]
    · exact ![58081, 241]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
  β := ![I199N1, I223N1, I227N1, I241N1]
  Il := ![[], [I199N1], [], [I223N1], [I227N1], [], [], [], [I241N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
