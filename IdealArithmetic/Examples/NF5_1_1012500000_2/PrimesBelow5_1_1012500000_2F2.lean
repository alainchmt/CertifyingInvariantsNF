
import IdealArithmetic.Examples.NF5_1_1012500000_2.RI5_1_1012500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5259, -1082, 1249, 337, -4060]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![5259, -1082, 1249, 337, -4060]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![54, 5, 53, 1, 0], ![27, 34, 20, 0, 1]] where
  M :=![![![5259, -1082, 1249, 337, -4060], ![-18390, 1761, 2063, 1281, -10494], ![-10638, 7824, -20856, -7693, 78642], ![251334, -43100, 34305, 6492, -97386], ![22318, -1826, -3407, -1893, 16149]]]
  hmulB := by decide  
  f := ![![![8059113, 4122334, -1083333, -520423, 6842116]], ![![35267322, 18039663, -4740753, -2277413, 29941650]], ![![154332630, 78943004, -20745912, -9966141, 131027046]], ![![141291492, 72272305, -18992878, -9124000, 119955234]], ![![68774855, 35179170, -9244948, -4441186, 58389249]]]
  g := ![![![1443, 2019, 964, 337, -4060], ![2922, 5256, 2150, 1281, -10494], ![-25650, -39217, -17701, -7693, 78642], ![37764, 48292, 24447, 6492, -97386], ![-4649, -8081, -3374, -1893, 16149]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [4, 57, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 63, 27], [36, 3, 40], [0, 1]]
 g := ![![[7, 53, 54], [33, 53, 54], [29, 39], [49, 49], [8, 1], []], ![[31, 15, 43, 48], [23, 27, 43, 48], [21, 47], [36, 16], [17, 9], [55, 59]], ![[29, 15, 51, 47], [40, 59, 51, 47], [57, 49], [61, 9], [10, 16], [42, 59]]]
 h' := ![![[39, 63, 27], [2, 65, 11], [58, 65, 11], [24, 53, 46], [35, 9, 7], [0, 0, 1], [0, 1]], ![[36, 3, 40], [31, 30, 46], [20, 30, 46], [29, 14, 28], [46, 45, 63], [28, 2, 3], [39, 63, 27]], ![[0, 1], [10, 39, 10], [66, 39, 10], [19, 0, 60], [14, 13, 64], [56, 65, 63], [36, 3, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 17], []]
 b := ![[], [16, 54, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [4, 57, 59, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-844490683, -96337095, -18458862, 17058498, -91863007]
  a := ![-255, -244, 212, 67, -731]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10666442, 43906159, 13652252, 17058498, -91863007]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8059113, 4122334, -1083333, -520423, 6842116]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![8059113, 4122334, -1083333, -520423, 6842116]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![5, 14, 1, 0, 0], ![64, 10, 0, 1, 0], ![26, 4, 0, 0, 1]] where
  M :=![![![8059113, 4122334, -1083333, -520423, 6842116], ![35267322, 18039663, -4740753, -2277413, 29941650], ![154332630, 78943004, -20745912, -9966141, 131027046], ![675371862, 345460872, -90785743, -43612620, 573384726], ![104577686, 53492750, -14057683, -6753179, 88785531]]]
  hmulB := by decide  
  f := ![![![5259, -1082, 1249, 337, -4060]], ![![-18390, 1761, 2063, 1281, -10494]], ![![-3609, 404, 213, 178, -1322]], ![![6030, -1414, 2013, 610, -6898]], ![![1276, -342, 557, 179, -1961]]]
  g := ![![![-1956898, -42914, -1083333, -520423, 6842116], ![-8563543, -187795, -4740753, -2277413, 29941650], ![-37474746, -821806, -20745912, -9966141, 131027046], ![-163992457, -3596290, -90785743, -43612620, 573384726], ![-25393347, -556866, -14057683, -6753179, 88785531]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [27, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 66], [0, 1]]
 g := ![![[26, 17], [31, 14], [25], [26], [19], [1]], ![[18, 50], [52, 53], [25], [26], [19], [1]]]
 h' := ![![[35, 66], [34, 34], [59, 58], [59, 5], [15, 48], [40, 35], [0, 1]], ![[0, 1], [18, 33], [12, 9], [33, 62], [20, 19], [59, 32], [35, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [38, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [27, 32, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38852564, 7087192, -6345352, -3214488, 28431848]
  a := ![-1719, -1664, 1434, 460, -4928]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6909276, 214024, -6345352, -3214488, 28431848]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![5259, -1082, 1249, 337, -4060]] ![![8059113, 4122334, -1083333, -520423, 6842116]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16487, 8424, -2214, -1064, 13986]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![16487, 8424, -2214, -1064, 13986]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![22, 59, 1, 0, 0], ![51, 20, 0, 1, 0], ![34, 59, 0, 0, 1]] where
  M :=![![![16487, 8424, -2214, -1064, 13986], ![72072, 36871, -9678, -4650, 61152], ![315324, 161388, -42443, -20382, 267948], ![1380996, 706056, -185598, -89171, 1172196], ![213768, 109342, -28750, -13810, 181541]]]
  hmulB := by decide  
  f := ![![![-1943, -444, 954, 344, -3330]], ![![-9000, 1001, -2934, -642, 8832]], ![![-7402, 785, -2321, -500, 6960]], ![![-2679, -424, 864, 337, -3102]], ![![-8098, 603, -1924, -360, 5585]]]
  g := ![![![-5015, -9364, -2214, -1064, 13986], ![-21930, -40945, -9678, -4650, 61152], ![-96080, -179377, -42443, -20382, 267948], ![-420321, -784786, -185598, -89171, 1172196], ![-65096, -121537, -28750, -13810, 181541]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [11, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 70], [0, 1]]
 g := ![![[48, 36], [17, 24], [52, 54], [1], [38], [1]], ![[68, 35], [54, 47], [11, 17], [1], [38], [1]]]
 h' := ![![[40, 70], [26, 6], [67, 38], [16, 14], [58, 1], [60, 40], [0, 1]], ![[0, 1], [53, 65], [25, 33], [8, 57], [27, 70], [27, 31], [40, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [17, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [11, 31, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![314701, 61143, -57305, -27840, 250884]
  a := ![-158, -152, 132, 42, -453]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-77955, -152158, -57305, -27840, 250884]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1353, -12, 102, -6, -212]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![1353, -12, 102, -6, -212]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![40, 15, 1, 0, 0], ![39, 28, 0, 1, 0], ![63, 46, 0, 0, 1]] where
  M :=![![![1353, -12, 102, -6, -212], ![-3084, -859, 1922, 670, -6636], ![-19332, 1448, -4657, -886, 13596], ![83412, 13240, -27274, -10585, 97716], ![3548, 1768, -4090, -1342, 13833]]]
  hmulB := by decide  
  f := ![![![3231903, 1653156, -434442, -208702, 2743852]], ![![14143044, 7234347, -1901158, -913298, 12007332]], ![![5680464, 2905627, -763587, -366820, 4822664]], ![![11167467, 5712296, -1501168, -721147, 9481080]], ![![12621523, 6456066, -1696628, -815044, 10715565]]]
  g := ![![![153, 118, 102, -6, -212], ![4394, 3617, 1922, 670, -6636], ![-9226, -7455, -4657, -886, 13596], ![-64351, -53186, -27274, -10585, 97716], ![-9183, -7544, -4090, -1342, 13833]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [29, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 70], [0, 1]]
 g := ![![[66, 49], [36, 3], [3, 37], [25], [9], [1]], ![[0, 22], [45, 68], [43, 34], [25], [9], [1]]]
 h' := ![![[3, 70], [21, 64], [55, 28], [58, 26], [12, 66], [42, 3], [0, 1]], ![[0, 1], [0, 7], [68, 43], [65, 45], [68, 5], [51, 68], [3, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [65, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [29, 68, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10661644, 2105928, -1889896, -923046, 8308514]
  a := ![907, 873, -755, -242, 2600]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5650424, -4590028, -1889896, -923046, 8308514]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, 16, -4, -2, 26]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![33, 16, -4, -2, 26]] 
 ![![71, 0, 0, 0, 0], ![68, 1, 0, 0, 0], ![62, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![33, 16, -4, -2, 26], ![132, 69, -16, -8, 108], ![576, 308, -87, -40, 528], ![2736, 1360, -388, -183, 2352], ![412, 210, -60, -28, 363]]]
  hmulB := by decide  
  f := ![![![303, -44, -4, -10, 62]], ![![288, -43, 0, -8, 44]], ![![222, -28, -15, -12, 92]], ![![348, -48, -12, -15, 104]], ![![245, -34, -8, -10, 69]]]
  g := ![![![-31, 16, -4, -2, 26], ![-132, 69, -16, -8, 108], ![-610, 308, -87, -40, 528], ![-2700, 1360, -388, -183, 2352], ![-417, 210, -60, -28, 363]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![16487, 8424, -2214, -1064, 13986]] ![![1353, -12, 102, -6, -212]]
  ![![303, -44, -4, -10, 62]] where
 M := ![![![303, -44, -4, -10, 62]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![303, -44, -4, -10, 62]] ![![33, 16, -4, -2, 26]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![261, 837, -1997, -614, 6610]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![261, 837, -1997, -614, 6610]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![32, 18, 24, 1, 0], ![36, 18, 21, 0, 1]] where
  M :=![![![261, 837, -1997, -614, 6610], ![24060, 337, 617, -481, 228], ![-40554, -15482, 34816, 11705, -118626], ![-370062, 17068, -62975, -8852, 172866], ![-49372, -2342, 2703, 2193, -13557]]]
  hmulB := by decide  
  f := ![![![1011, 467, -99, -52, 704]], ![![3768, 2171, -561, -259, 3480]], ![![18450, 9334, -2764, -1305, 16698]], ![![8574, 4354, -1223, -582, 7534]], ![![6910, 3536, -1005, -476, 6153]]]
  g := ![![![-2987, -1467, -1727, -614, 6610], ![428, 67, 101, -481, 228], ![52814, 26152, 30754, 11705, -118626], ![-86438, -40208, -47681, -8852, 172866], ![5048, 2770, 3216, 2193, -13557]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [49, 32, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 72, 25], [3, 0, 48], [0, 1]]
 g := ![![[41, 18, 69], [51, 8], [71, 35], [68, 66, 41], [38, 1], []], ![[32, 24, 16, 38], [16, 12], [54, 49], [28, 37, 69, 49], [], [48, 41]], ![[19, 64, 12, 27], [6, 46], [21, 72], [49, 41, 4, 19], [35, 1], [25, 41]]]
 h' := ![![[35, 72, 25], [21, 16, 19], [44, 63, 9], [26, 47, 20], [36, 49, 25], [0, 0, 1], [0, 1]], ![[3, 0, 48], [46, 65, 35], [63, 33, 42], [9, 69, 7], [2, 23, 57], [41, 35], [35, 72, 25]], ![[0, 1], [33, 65, 19], [20, 50, 22], [10, 30, 46], [5, 1, 64], [25, 38, 72], [3, 0, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 31], []]
 b := ![[], [31, 45, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [49, 32, 35, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3455846403, -71220266, -582244146, -86448014, 1374735540]
  a := ![-427, -408, 356, 115, -1224]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-687397115, -318635558, -375026550, -86448014, 1374735540]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71, 0, -16, -2, 42]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-71, 0, -16, -2, 42]] 
 ![![73, 0, 0, 0, 0], ![58, 1, 0, 0, 0], ![67, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![-71, 0, -16, -2, 42], ![324, 93, -144, -52, 492], ![1224, -212, 549, 120, -1608], ![-8496, -1320, 2044, 885, -7632], ![-564, -190, 348, 120, -1181]]]
  hmulB := by decide  
  f := ![![![-5750423, -2941412, 772992, 371338, -4882062]], ![![-4913546, -2513339, 660496, 317296, -4171560]], ![![-6786293, -3471272, 912237, 438230, -5761506]], ![![-11012632, -5633096, 1480356, 711149, -9349632]], ![![-5984877, -3061338, 804508, 386478, -5081111]]]
  g := ![![![-21, 0, -16, -2, 42], ![-322, 93, -144, -52, 492], ![977, -212, 549, 120, -1608], ![4964, -1320, 2044, 885, -7632], ![751, -190, 348, 120, -1181]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2335, -741, 1928, 521, -6140]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![2335, -741, 1928, 521, -6140]] 
 ![![73, 0, 0, 0, 0], ![64, 1, 0, 0, 0], ![65, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![2335, -741, 1928, 521, -6140], ![-26790, -1979, 3164, 1704, -12942], ![-1944, 16218, -39185, -11848, 129024], ![481968, 11320, 1650, -12881, 39792], ![49742, 5494, -10256, -4496, 38485]]]
  hmulB := by decide  
  f := ![![![2438923493, 1247538885, -327848306, -157495243, 2070624634]], ![![2284438730, 1168518059, -307081944, -147519278, 1939468426]], ![![2811446473, 1438088899, -377924099, -181551183, 2386893374]], ![![2833235669, 1449234337, -380853076, -182958236, 2405392210]], ![![500357712, 255939026, -67259768, -32310960, 424799305]]]
  g := ![![![-874, -741, 1928, 521, -6140], ![-1118, -1979, 3164, 1704, -12942], ![17273, 16218, -39185, -11848, 129024], ![-5705, 11320, 1650, -12881, 39792], ![4004, 5494, -10256, -4496, 38485]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![261, 837, -1997, -614, 6610]] ![![-71, 0, -16, -2, 42]]
  ![![-703167, 55785, -175793, -33876, 513580]] where
 M := ![![![-703167, 55785, -175793, -33876, 513580]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![-703167, 55785, -175793, -33876, 513580]] ![![2335, -741, 1928, 521, -6140]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![6424714889, -2230442, 386074589, -61195827, -668907614]]]
 hmul := by decide  
 g := ![![![![88009793, -30554, 5288693, -838299, -9163118]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
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


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [40, 53, 75, 58, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 2, 7, 76, 24], [77, 69, 77, 72, 13], [23, 62, 65, 20, 29], [55, 24, 9, 69, 13], [0, 1]]
 g := ![![[73, 62, 20, 59, 8], [60, 34, 39, 64, 31], [69, 39, 44, 64, 31], [72, 4, 21, 0, 1], [], []], ![[38, 48, 78, 46, 78, 65, 71, 58], [17, 3, 21, 55, 74, 17, 74, 34], [45, 9, 15, 78, 31, 15, 15, 33], [70, 43, 20, 31, 55, 16, 67, 57], [19, 21, 25, 44], [45, 38, 14, 23]], ![[10, 70, 41, 39, 44, 66, 36, 45], [48, 34, 5, 64, 26, 56, 25, 76], [5, 72, 41, 45, 50, 6, 19, 46], [20, 25, 48, 41, 63, 75, 4, 76], [24, 51, 51, 38], [19, 70, 55, 11]], ![[34, 48, 16, 55, 7, 21, 61, 74], [9, 24, 74, 34, 17, 68, 59, 28], [56, 66, 4, 72, 68, 77, 56, 77], [18, 1, 39, 39, 7, 16, 11, 39], [43, 13, 10, 32], [29, 27, 54, 51]], ![[31, 7, 78, 9, 13, 74, 26, 62], [23, 39, 37, 42, 45, 13, 12, 8], [9, 54, 33, 14, 53, 72, 4, 1], [25, 12, 31, 37, 8, 49, 66, 4], [39, 11, 47, 23], [5, 12, 56, 11]]]
 h' := ![![[3, 2, 7, 76, 24], [49, 67, 12, 17, 18], [5, 29, 59, 20, 49], [43, 53, 26, 20, 49], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[77, 69, 77, 72, 13], [43, 7, 67, 72, 3], [77, 73, 77, 12, 18], [40, 57, 72, 6, 30], [74, 11, 65, 39, 36], [26, 57, 22, 77, 53], [3, 2, 7, 76, 24]], ![[23, 62, 65, 20, 29], [67, 48, 25, 73, 21], [51, 15, 25, 71, 27], [25, 56, 46, 15, 35], [38, 47, 30, 47, 27], [34, 25, 41, 78, 14], [77, 69, 77, 72, 13]], ![[55, 24, 9, 69, 13], [57, 3, 55, 43, 61], [74, 52, 35, 24, 34], [78, 26, 5, 32, 16], [19, 41, 38, 39, 71], [1, 77, 41, 55, 36], [23, 62, 65, 20, 29]], ![[0, 1], [78, 33, 78, 32, 55], [53, 68, 41, 31, 30], [63, 45, 9, 6, 28], [65, 59, 25, 33, 23], [60, 78, 53, 27, 55], [55, 24, 9, 69, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 24, 61, 30], [], [], []]
 b := ![[], [62, 34, 62, 8, 58], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [40, 53, 75, 58, 0, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1402829549968450, 490557099844702, -1181926117353636, -397656070218474, 4038944731353282]
  a := ![270, 258, -224, -82, 774]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![17757336075550, 6209583542338, -14961090093084, -5033621142006, 51125882675358]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11819903, -53134, -572676, 154396, 776836]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-11819903, -53134, -572676, 154396, 776836]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![82, 72, 7, 60, 1]] where
  M :=![![![-11819903, -53134, -572676, 154396, 776836], ![23217672, 7672841, -17070686, -5831852, 58478232], ![176872104, -10495744, 35714117, 5937298, -101140248], ![-679326156, -121642252, 252188642, 95499461, -895543068], ![-23732224, -15474396, 35796146, 11535720, -120278171]]]
  hmulB := by decide  
  f := ![![![66931, -9574, 2280, -924, 740]], ![![-74280, -6613, 54546, 22976, -220632]], ![![-579744, 136600, -185389, -55614, 632640]], ![![2586420, -301428, -120830, -115933, 834948]], ![![1823362, -221400, -54307, -69846, 469845]]]
  g := ![![![-909885, -674522, -72416, -559708, 776836], ![-57493944, -50635661, -5137570, -42343684, 58478232], ![102052680, 87609664, 8960191, 73184966, -101140248], ![876568740, 775391068, 78566146, 648531127, -895543068], ![118543106, 104151252, 10575221, 87087060, -120278171]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [63, 63, 56, 23, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 52, 59, 4], [46, 9, 13, 1], [77, 21, 11, 78], [0, 1]]
 g := ![![[1, 63, 55, 48], [41, 78, 51, 30], [73, 76, 25], [43, 71, 44], [60, 1], []], ![[76, 2, 48, 49, 74, 61], [37, 30, 18, 28, 29, 26], [2, 29, 40], [17], [57, 25, 82, 73, 81, 51], [28, 21, 16]], ![[14, 77, 46, 48, 57, 30], [64, 0, 14, 66, 60, 25], [70, 29, 4], [57, 69, 28], [63, 23, 41, 31, 67, 9], [62, 3, 1]], ![[17, 18, 56, 10, 52, 26], [60, 40, 28, 55, 46, 51], [41, 59, 30], [51, 7, 49], [31, 58, 70, 0, 32, 36], [73, 62, 25]]]
 h' := ![![[20, 52, 59, 4], [73, 50, 71, 52], [34, 64, 18, 69], [63, 48, 76, 78], [38, 58, 63, 58], [0, 0, 1], [0, 1]], ![[46, 9, 13, 1], [82, 38, 74, 77], [18, 82, 36, 52], [12, 26, 45, 17], [2, 46, 73], [47, 72, 3, 65], [20, 52, 59, 4]], ![[77, 21, 11, 78], [82, 81, 8, 69], [18, 12, 31, 5], [19, 5, 51, 2], [37, 12, 28, 32], [36, 53, 43, 80], [46, 9, 13, 1]], ![[0, 1], [19, 80, 13, 51], [73, 8, 81, 40], [0, 4, 77, 69], [15, 50, 2, 76], [2, 41, 36, 21], [77, 21, 11, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [20, 78, 49], []]
 b := ![[], [], [43, 64, 13, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [63, 63, 56, 23, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![860433492340, 149631176622, -235141984254, -97075064933, 901695045722]
  a := ![-59, -57, 54, 28, -170]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-880464581408, -780390507414, -78879606076, -652997322991, 901695045722]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![66931, -9574, 2280, -924, 740]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![66931, -9574, 2280, -924, 740]] 
 ![![83, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![43, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![80, 0, 0, 0, 1]] where
  M :=![![![66931, -9574, 2280, -924, 740], ![-74280, -6613, 54546, 22976, -220632], ![-579744, 136600, -185389, -55614, 632640], ![2586420, -301428, -120830, -115933, 834948], ![71872, 14484, -74230, -30444, 296599]]]
  hmulB := by decide  
  f := ![![![-11819903, -53134, -572676, 154396, 776836]], ![![-2141213, 81561, -322966, -38640, 863668]], ![![-3992575, -153982, 133603, 151522, -816100]], ![![-10463188, -1475812, 2928022, 1180359, -10639924]], ![![-11678608, -237652, -120698, 287800, -700377]]]
  g := ![![![1051, -9574, 2280, -924, 740], ![180429, -6613, 54546, 22976, -220632], ![-537971, 136600, -185389, -55614, 632640], ![-626922, -301428, -120830, -115933, 834948], ![-243654, 14484, -74230, -30444, 296599]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-11819903, -53134, -572676, 154396, 776836]] ![![66931, -9574, 2280, -924, 740]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7841, 6558, -17786, -6626, 67432]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-7841, 6558, -17786, -6626, 67432]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![64, 29, 77, 1, 0], ![1, 75, 63, 0, 1]] where
  M :=![![![-7841, 6558, -17786, -6626, 67432], ![212844, -38221, 31484, 6374, -91140], ![-520020, 31888, 121709, 60788, -542868], ![-1043496, 364804, -727136, -251467, 2654472], ![-280708, 48100, -34056, -5538, 91435]]]
  hmulB := by decide  
  f := ![![![-49363721, -25250142, 6635638, 3187698, -41909368]], ![![-216019596, -110496637, 29038084, 13949622, -183398748]], ![![-945318996, -483542088, 127072949, 61044652, -802567476]], ![![-970226968, -496282821, 130421165, 62653103, -823714136]], ![![-858949325, -439362961, 115462853, 55467270, -729240405]]]
  g := ![![![3919, -54592, -42200, -6626, 67432], ![-1168, 74297, 59354, 6374, -91140], ![-43456, 438024, 333053, 60788, -542868], ![139280, -2150877, -1669617, -251467, 2654472], ![-199, -74707, -60315, -5538, 91435]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [45, 15, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 84, 13], [16, 4, 76], [0, 1]]
 g := ![![[25, 83, 16], [24, 16], [19, 78], [27, 19, 49], [64, 48, 1], []], ![[61, 17, 58, 29], [56, 50], [1, 39], [70, 26, 76, 30], [70, 35, 35, 30], [61, 80]], ![[67, 29, 86, 33], [16, 45], [60, 20], [0, 40, 61, 29], [80, 44, 18, 31], [87, 80]]]
 h' := ![![[32, 84, 13], [10, 30, 85], [17, 85, 4], [31, 31, 16], [57, 84, 82], [0, 0, 1], [0, 1]], ![[16, 4, 76], [22, 55, 18], [36, 82, 53], [9, 4, 22], [18, 50, 85], [59, 60, 4], [32, 84, 13]], ![[0, 1], [85, 4, 75], [2, 11, 32], [11, 54, 51], [47, 44, 11], [79, 29, 84], [16, 4, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 27], []]
 b := ![[], [25, 1, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [45, 15, 41, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4736510, -228674, 406034, 268952, -1900764]
  a := ![23, 21, -19, -8, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-225266, 1511562, 1117358, 268952, -1900764]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-206701, -140139, 35014, 15249, -222034]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-206701, -140139, 35014, 15249, -222034]] 
 ![![89, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![49, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![78, 0, 0, 0, 1]] where
  M :=![![![-206701, -140139, 35014, 15249, -222034], ![-1291998, -671559, 270424, 113106, -1394574], ![-6555348, -2721474, 607509, 345028, -4288428], ![-20408616, -11190364, 1420422, 903693, -13905048], ![-3632834, -1768388, 277572, 170574, -2387617]]]
  hmulB := by decide  
  f := ![![![-530689735, 183289711, -362292732, -124973147, 1320833284]], ![![-121208833, 51726826, -114562320, -40773315, 424281934]], ![![-370056335, 99360705, -160868127, -51871963, 567407900]], ![![-411384813, 106238949, -165227402, -52434732, 578340924]], ![![-531492764, 170393312, -320349312, -108828638, 1159082791]]]
  g := ![![![218141, -140139, 35014, 15249, -222034], ![1273819, -671559, 270424, 113106, -1394574], ![4225413, -2721474, 607509, 345028, -4288428], ![14790943, -11190364, 1420422, 903693, -13905048], ![2469346, -1768388, 277572, 170574, -2387617]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22059, -4661, 5574, 1549, -18344]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![22059, -4661, 5574, 1549, -18344]] 
 ![![89, 0, 0, 0, 0], ![72, 1, 0, 0, 0], ![67, 0, 1, 0, 0], ![71, 0, 0, 1, 0], ![83, 0, 0, 0, 1]] where
  M :=![![![22059, -4661, 5574, 1549, -18344], ![-80718, 8521, 7572, 5086, -40614], ![-29628, 31766, -88631, -33264, 337452], ![1055664, -190716, 164402, 34801, -483264], ![98462, -9014, -12684, -7522, 62925]]]
  hmulB := by decide  
  f := ![![![-533487, 294789, -740324, -210119, 2391214]], ![![-321654, 244391, -606608, -175376, 1970178]], ![![-458349, 153833, -396995, -107889, 1266074]], ![![-2308089, 230987, -692094, -146160, 2065258]], ![![-708863, 256355, -658316, -180329, 2104279]]]
  g := ![![![15694, -4661, 5574, 1549, -18344], ![20318, 8521, 7572, 5086, -40614], ![-247475, 31766, -88631, -33264, 337452], ![465307, -190716, 164402, 34801, -483264], ![-34735, -9014, -12684, -7522, 62925]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-7841, 6558, -17786, -6626, 67432]] ![![-206701, -140139, 35014, 15249, -222034]]
  ![![-533487, 294789, -740324, -210119, 2391214]] where
 M := ![![![-533487, 294789, -740324, -210119, 2391214]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![-533487, 294789, -740324, -210119, 2391214]] ![![22059, -4661, 5574, 1549, -18344]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![108575, 1864, 1953, -2423, 3770]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![108575, 1864, 1953, -2423, 3770]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![91, 71, 1, 0, 0], ![38, 94, 0, 1, 0], ![72, 54, 0, 0, 1]] where
  M :=![![![108575, 1864, 1953, -2423, 3770], ![-172830, -69643, 157199, 52565, -534654], ![-1684998, 70528, -269440, -35053, 730074], ![5606118, 1141036, -2411015, -888316, 8478102], ![135862, 137720, -323059, -101933, 1078139]]]
  hmulB := by decide  
  f := ![![![1147899391, 587164420, -154304495, -74126429, 974556482]], ![![5023299174, 2569478353, -675248779, -324383163, 4264736886]], ![![4980365401, 2547517191, -669477474, -321610683, 4228286474]], ![![6309348992, 3227308390, -848123921, -407430756, 5356581874]], ![![3802086886, 1944813466, -511089311, -245522499, 3227938363]]]
  g := ![![![-2562, -1161, 1953, -2423, 3770], ![227007, 130922, 157199, 52565, -534654], ![-292776, -174518, -269440, -35053, 730074], ![-3625349, -2082399, -2411015, -888316, 8478102], ![-455859, -263535, -323059, -101933, 1078139]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [82, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 96], [0, 1]]
 g := ![![[73, 27], [44], [81], [47], [44], [28, 1]], ![[53, 70], [44], [81], [47], [44], [56, 96]]]
 h' := ![![[28, 96], [84, 30], [54, 23], [87, 88], [35, 85], [32, 23], [0, 1]], ![[0, 1], [51, 67], [19, 74], [29, 9], [87, 12], [94, 74], [28, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [86, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [82, 69, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1894384, 308068, -233539, -132363, 1135344]
  a := ![381, 364, -313, -103, 1092]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-552253, -329661, -233539, -132363, 1135344]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![353, 14, 9, -7, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![353, 14, 9, -7, 0]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![68, 18, 1, 0, 0], ![37, 35, 0, 1, 0], ![79, 46, 0, 0, 1]] where
  M :=![![![353, 14, 9, -7, 0], ![-630, -249, 539, 177, -1806], ![-5742, 144, -882, -97, 2322], ![19134, 4492, -8835, -3198, 30702], ![510, 498, -1147, -357, 3791]]]
  hmulB := by decide  
  f := ![![![723257, 369954, -97223, -46705, 614040]], ![![3165030, 1618947, -425451, -204383, 2687070]], ![![1237138, 632810, -166300, -79889, 1050318]], ![![2042753, 1044891, -274593, -131912, 1734276]], ![![2186741, 1118542, -293948, -141210, 1856519]]]
  g := ![![![0, 1, 9, -7, 0], ![1019, 690, 539, 177, -1806], ![-1295, -901, -882, -97, 2322], ![-17394, -11720, -8835, -3198, 30702], ![-2142, -1451, -1147, -357, 3791]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [83, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 96], [0, 1]]
 g := ![![[90, 22], [36], [94], [89], [31], [96, 1]], ![[68, 75], [36], [94], [89], [31], [95, 96]]]
 h' := ![![[96, 96], [13, 64], [24, 91], [58, 71], [48, 34], [83, 15], [0, 1]], ![[0, 1], [46, 33], [30, 6], [84, 26], [14, 63], [68, 82], [96, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [17, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [83, 1, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![987435, 187901, -171983, -84692, 757164]
  a := ![277, 265, -231, -74, 794]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-453609, -294657, -171983, -84692, 757164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![153, 8, -9, -7, 44]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![153, 8, -9, -7, 44]] 
 ![![97, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![77, 0, 0, 0, 1]] where
  M :=![![![153, 8, -9, -7, 44], ![-102, -97, 225, 71, -750], ![-2610, 4, -172, 21, 318], ![5706, 1740, -3797, -1312, 13050], ![-98, 182, -441, -131, 1443]]]
  hmulB := by decide  
  f := ![![![28257, 14448, -3809, -1829, 24028]], ![![3606, 1843, -485, -233, 3062]], ![![15183, 7768, -2045, -982, 12906]], ![![32265, 16504, -4346, -2087, 27426]], ![![26207, 13402, -3532, -1696, 22283]]]
  g := ![![![-29, 8, -9, -7, 44], ![506, -97, 225, 71, -750], ![-227, 4, -172, 21, 318], ![-8787, 1740, -3797, -1312, 13050], ![-975, 182, -441, -131, 1443]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![108575, 1864, 1953, -2423, 3770]] ![![353, 14, 9, -7, 0]]
  ![![-18500453, -7669510, 17342340, 5783326, -58930394]] where
 M := ![![![-18500453, -7669510, 17342340, 5783326, -58930394]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![-18500453, -7669510, 17342340, 5783326, -58930394]] ![![153, 8, -9, -7, 44]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![-8536949921, 2963738, -513003221, 81315003, 888822446]]]
 hmul := by decide  
 g := ![![![![-88009793, 30554, -5288693, 838299, 9163118]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![562115, -65118, -31097, -27081, 199754]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![562115, -65118, -31097, -27081, 199754]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![40, 62, 29, 30, 1]] where
  M :=![![![562115, -65118, -31097, -27081, 199754], ![-40242, -168819, 567679, 219339, -2192802], ![-6573114, 1280496, -1269630, -310853, 3962214], ![19569798, -1608760, -3141027, -1733586, 14893062], ![-185054, 261364, -746007, -281655, 2850275]]]
  hmulB := by decide  
  f := ![![![-214057, 13690, -45597, -7907, 130234]], ![![851178, 147813, -304923, -116297, 1085610]], ![![2560590, -465484, 1270818, 314985, -3949986]], ![![-19051182, -1950588, 3560543, 1611150, -13533534]], ![![-4498732, -620118, 1224261, 496972, -4460403]]]
  g := ![![![-73545, -123266, -57663, -59601, 199754], ![868038, 1344405, 635237, 653499, -2192802], ![-1634274, -2419572, -1150236, -1179973, 3962214], ![-5704482, -9158204, -4307325, -4440846, 14893062], ![-1130654, -1747086, -825782, -849405, 2850275]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 4 2 6 [11, 21, 88, 28, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 74, 15, 22], [15, 24, 75, 84], [29, 2, 11, 96], [0, 1]]
 g := ![![[80, 4, 64, 95], [62, 24, 52], [22, 86, 80, 97], [13, 58, 71], [90, 73, 1], []], ![[54, 73, 6, 18, 13, 81], [79, 48, 64], [65, 8, 74, 56, 17, 81], [18, 22, 77], [7, 78, 96], [80, 43, 77, 17, 73, 43]], ![[50, 1, 34, 25, 98, 21], [83, 14, 30], [87, 43, 37, 99, 57, 68], [23, 34, 4], [60, 44, 13], [71, 38, 70, 2, 84, 36]], ![[17, 57, 73, 92, 59, 81], [78, 10, 71], [6, 57, 25, 73, 11, 78], [97, 95, 4], [44, 70, 43], [34, 79, 21, 42, 83, 77]]]
 h' := ![![[29, 74, 15, 22], [9, 71, 54, 14], [61, 1, 25, 70], [55, 45, 21, 81], [20, 34, 30, 24], [0, 0, 0, 1], [0, 1]], ![[15, 24, 75, 84], [18, 9, 59, 34], [33, 70, 87, 93], [40, 74, 5, 67], [95, 60, 8, 73], [77, 22, 63, 46], [29, 74, 15, 22]], ![[29, 2, 11, 96], [33, 77, 87, 51], [21, 47, 18, 63], [34, 56, 80, 20], [61, 5, 87, 2], [69, 50, 49, 66], [15, 24, 75, 84]], ![[0, 1], [20, 45, 2, 2], [75, 84, 72, 77], [49, 27, 96, 34], [45, 2, 77, 2], [78, 29, 90, 89], [29, 2, 11, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6, 24, 35], []]
 b := ![[], [], [63, 39, 29, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 4
  hpos := by decide
  P := [11, 21, 88, 28, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8787112151, 6724917954, 1527923967, 310468299, 847388736]
  a := ![43, 41, -35, -7, 123]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-248598389, -453595878, -228181677, -248625681, 847388736]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 104060401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-214057, 13690, -45597, -7907, 130234]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-214057, 13690, -45597, -7907, 130234]] 
 ![![101, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![76, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![-214057, 13690, -45597, -7907, 130234], ![851178, 147813, -304923, -116297, 1085610], ![2560590, -465484, 1270818, 314985, -3949986], ![-19051182, -1950588, 3560543, 1611150, -13533534], ![-1304338, -327248, 709455, 251801, -2462269]]]
  hmulB := by decide  
  f := ![![![562115, -65118, -31097, -27081, 199754]], ![![71953, -10053, 1618, -1314, 4000]], ![![118581, -8598, -22731, -11926, 104496]], ![![616738, -64928, -54499, -37542, 297766]], ![![315401, -34162, -24936, -18072, 140953]]]
  g := ![![![-56532, 13690, -45597, -7907, 130234], ![-436130, 147813, -304923, -116297, 1085610], ![1662230, -465484, 1270818, 314985, -3949986], ![5324481, -1950588, 3560543, 1611150, -13533534], ![997528, -327248, 709455, 251801, -2462269]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![562115, -65118, -31097, -27081, 199754]] ![![-214057, 13690, -45597, -7907, 130234]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38264949, 19572979, -5143691, -2470982, 32486558]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![38264949, 19572979, -5143691, -2470982, 32486558]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![85, 12, 1, 0, 0], ![10, 44, 0, 1, 0], ![59, 61, 0, 0, 1]] where
  M :=![![![38264949, 19572979, -5143691, -2470982, 32486558], ![167450316, 85652961, -22509277, -10813239, 142164036], ![732776922, 374824050, -98502366, -47319613, 622121202], ![3206689254, 1640259820, -431053389, -207074058, 2722448694], ![496538596, 253985374, -66746339, -32064321, 421556679]]]
  hmulB := by decide  
  f := ![![![-458643, -25265, 33561, 22940, -153812]], ![![218856, 283701, -669081, -209375, 2227032]], ![![-276483, 12483, -46395, -6415, 126994]], ![![-103200, 69034, -172081, -49418, 557770]], ![![-128599, 148438, -364483, -107172, 1189871]]]
  g := ![![![-13752606, -17394753, -5143691, -2470982, 32486558], ![-60182591, -76120965, -22509277, -10813239, 142164036], ![-263363852, -333111436, -98502366, -47319613, 622121202], ![-1152500049, -1457720498, -431053389, -207074058, 2722448694], ![-178458480, -225720251, -66746339, -32064321, 421556679]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [13, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 102], [0, 1]]
 g := ![![[92, 8], [91, 93], [51, 41], [9], [13], [40, 1]], ![[0, 95], [0, 10], [43, 62], [9], [13], [80, 102]]]
 h' := ![![[40, 102], [53, 27], [58, 14], [19, 91], [62, 100], [98, 42], [0, 1]], ![[0, 1], [0, 76], [0, 89], [54, 12], [45, 3], [27, 61], [40, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [82, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [13, 63, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8873461, 946466, -562123, -462599, 3509396]
  a := ![-821, -784, 674, 225, -2354]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1415286, -1806086, -562123, -462599, 3509396]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-334985, -193654, 445719, 144735, -1501368]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-334985, -193654, 445719, 144735, -1501368]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![94, 51, 1, 0, 0], ![47, 68, 0, 1, 0], ![44, 21, 0, 0, 1]] where
  M :=![![![-334985, -193654, 445719, 144735, -1501368], ![-4990266, 101281, -539203, -25185, 1308798], ![13438926, 3314208, -7171430, -2552359, 24913422], ![69248754, -6756572, 20347179, 4258342, -60586494], ![10796178, 177910, 212035, -235531, 316177]]]
  hmulB := by decide  
  f := ![![![26857, 3242, -29695, -12193, 117504]], ![![312678, -81709, 95189, 27929, -325698]], ![![165790, -36441, 21037, 3442, -59964]], ![![214151, -49770, 36330, 7969, -112698]], ![![70316, -14605, 5716, 224, -13121]]]
  g := ![![![165292, -12025, 445719, 144735, -1501368], ![-103967, 17752, -539203, -25185, 1308798], ![-2802683, 188696, -7171430, -2552359, 24913422], ![6041530, -599161, 20347179, 4258342, -60586494], ![-116281, -12228, 212035, -235531, 316177]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [66, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 102], [0, 1]]
 g := ![![[49, 64], [20, 29], [100, 56], [82], [59], [62, 1]], ![[0, 39], [67, 74], [70, 47], [82], [59], [21, 102]]]
 h' := ![![[62, 102], [19, 8], [95, 21], [35, 46], [83, 59], [28, 70], [0, 1]], ![[0, 1], [0, 95], [58, 82], [3, 57], [33, 44], [42, 33], [62, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [14, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [66, 41, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![744762, 143275, -120401, -60636, 548316]
  a := ![-248, -236, 204, 66, -711]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-89452, -10754, -120401, -60636, 548316]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1257, 485, -1022, -359, 3760]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![-1257, 485, -1022, -359, 3760]] 
 ![![103, 0, 0, 0, 0], ![40, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-1257, 485, -1022, -359, 3760], ![12810, -2051, 1090, 74, -2382], ![-21924, 118, 9073, 4078, -38076], ![-89892, 24176, -39200, -12647, 138300], ![-16546, 2522, -998, 62, 1497]]]
  hmulB := by decide  
  f := ![![![-160149, -81791, 21476, 10327, -135718]], ![![-68982, -35237, 9250, 4448, -58462]], ![![-104328, -53326, 14013, 6734, -88512]], ![![-187779, -95953, 25252, 12130, -159382]], ![![-77681, -39689, 10430, 5013, -65881]]]
  g := ![![![-946, 485, -1022, -359, 3760], ![1242, -2051, 1090, 74, -2382], ![7726, 118, 9073, 4078, -38076], ![-37131, 24176, -39200, -12647, 138300], ![-1235, 2522, -998, 62, 1497]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![38264949, 19572979, -5143691, -2470982, 32486558]] ![![-334985, -193654, 445719, 144735, -1501368]]
  ![![-160149, -81791, 21476, 10327, -135718]] where
 M := ![![![-160149, -81791, 21476, 10327, -135718]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-160149, -81791, 21476, 10327, -135718]] ![![-1257, 485, -1022, -359, 3760]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)


lemma PB1981I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB1981I2 : PrimesBelowBoundCertificateInterval O 61 103 1981 where
  m := 9
  g := ![2, 3, 3, 1, 2, 3, 3, 2, 3]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB1981I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
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
    · exact ![300763, 4489]
    · exact ![5041, 5041, 71]
    · exact ![389017, 73, 73]
    · exact ![3077056399]
    · exact ![47458321, 83]
    · exact ![704969, 89, 89]
    · exact ![9409, 9409, 97]
    · exact ![104060401, 101]
    · exact ![10609, 10609, 103]
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
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
  β := ![I71N2, I73N1, I73N2, I83N1, I89N1, I89N2, I97N2, I101N1, I103N2]
  Il := ![[], [I71N2], [I73N1, I73N2], [], [I83N1], [I89N1, I89N2], [I97N2], [I101N1], [I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
