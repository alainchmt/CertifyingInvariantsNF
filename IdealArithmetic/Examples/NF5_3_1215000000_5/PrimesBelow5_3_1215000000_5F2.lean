
import IdealArithmetic.Examples.NF5_3_1215000000_5.RI5_3_1215000000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22477, -9133, 4937, -3812, -10944]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-22477, -9133, 4937, -3812, -10944]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![48, 65, 65, 23, 1]] where
  M :=![![![-22477, -9133, 4937, -3812, -10944], ![88536, -23320, -54877, 8890, -79192], ![421812, 465997, 83360, 101970, 812972], ![-2789094, -698893, 872257, -428147, -461890], ![413874, -178564, -298092, 34374, -513651]]]
  hmulB := by decide  
  f := ![![![-276763, -91191, 80405, 29416, 120764]], ![![-901080, -297006, 261801, 95778, 393224]], ![![-2934012, -967061, 852330, 311822, 1280220]], ![![-4325586, -1425935, 1256501, 459687, 1887346]], ![![-5381352, -1773768, 1563294, 571925, 2348111]]]
  g := ![![![7505, 10481, 10691, 3700, -10944], ![58056, 76480, 76009, 27318, -79192], ![-576132, -781749, -787460, -277558, 812972], ![289278, 437671, 461121, 152169, -461890], ![374166, 495653, 493869, 176841, -513651]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 4 2 6 [3, 30, 5, 57, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 52, 58, 51], [33, 23, 19, 56], [11, 58, 57, 27], [0, 1]]
 g := ![![[56, 12, 0, 26], [16, 57, 38, 29], [20, 56, 19], [19, 29, 33], [1], []], ![[21, 16, 25, 14, 66, 50], [32, 11, 23, 40, 25, 2], [15, 3, 56], [45, 12, 15], [43, 59, 23], [23, 34, 55]], ![[52, 19, 54, 31, 59, 9], [19, 53, 64, 26, 32, 9], [16, 17, 36], [17, 34, 9], [28, 44, 25], [1, 55, 54]], ![[39, 55, 32, 23, 23, 31], [15, 0, 10, 1, 15, 18], [17, 66, 65], [8, 37, 14], [12, 57, 6], [20, 50, 59]]]
 h' := ![![[33, 52, 58, 51], [19, 36, 39, 19], [33, 0, 36, 30], [19, 59, 0, 32], [64, 37, 62, 10], [0, 0, 1], [0, 1]], ![[33, 23, 19, 56], [64, 33, 59, 42], [45, 66, 14, 62], [36, 38, 62, 49], [29, 13, 61, 45], [15, 27, 6, 36], [33, 52, 58, 51]], ![[11, 58, 57, 27], [66, 44, 2, 56], [42, 8, 15, 11], [31, 53, 44, 6], [45, 26, 13, 3], [14, 50, 33, 5], [33, 23, 19, 56]], ![[0, 1], [13, 21, 34, 17], [56, 60, 2, 31], [43, 51, 28, 47], [0, 58, 65, 9], [61, 57, 27, 26], [11, 58, 57, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [44, 6, 5], []]
 b := ![[], [], [61, 0, 66, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 4
  hpos := by decide
  P := [3, 30, 5, 57, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7256470846143, 84450528762, -3304448524801, 943517711140, -2350928215582]
  a := ![33, -74, -69, -37, -209]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1792552614837, 2282011709576, 2231431126687, 821117412978, -2350928215582]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 20151121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![276763, 91191, -80405, -29416, -120764]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![276763, 91191, -80405, -29416, -120764]] 
 ![![67, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![276763, 91191, -80405, -29416, -120764], ![901080, 297006, -261801, -95778, -393224], ![2934012, 967061, -852330, -311822, -1280220], ![4325586, 1425935, -1256501, -459687, -1887346], ![-1503498, -495572, 436780, 159794, 656053]]]
  hmulB := by decide  
  f := ![![![22477, 9133, -4937, 3812, 10944]], ![![-315, 757, 598, 38, 1672]], ![![13162, 951, -5518, 1778, -2660]], ![![45654, 12067, -13903, 7073, 8854]], ![![12945, 10435, 249, 2730, 16977]]]
  g := ![![![177660, 91191, -80405, -29416, -120764], ![578472, 297006, -261801, -95778, -393224], ![1883319, 967061, -852330, -311822, -1280220], ![2776415, 1425935, -1256501, -459687, -1887346], ![-965113, -495572, 436780, 159794, 656053]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-22477, -9133, 4937, -3812, -10944]] ![![276763, 91191, -80405, -29416, -120764]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1307, -561, 133, 28, 244]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![1307, -561, 133, 28, 244]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![64, 53, 24, 1, 0], ![21, 60, 33, 0, 1]] where
  M :=![![![1307, -561, 133, 28, 244], ![-1632, 828, -225, -54, -400], ![2724, -959, 180, 26, 348], ![-306, 511, -211, -63, -350], ![18, -148, 68, 22, 113]]]
  hmulB := by decide  
  f := ![![![-71, -23, 21, 8, 32]], ![![-240, -74, 73, 26, 112]], ![![-828, -277, 238, 78, 316]], ![![-538, -175, 158, 55, 226]], ![![-603, -196, 177, 60, 249]]]
  g := ![![![-79, -235, -121, 28, 244], ![144, 390, 201, -54, -400], ![-88, -327, -168, 26, 348], ![156, 350, 181, -63, -350], ![-53, -114, -59, 22, 113]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [70, 41, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 41, 8], [47, 29, 63], [0, 1]]
 g := ![![[28, 50, 8], [28, 62, 25], [41, 58, 20], [0, 57], [4, 1], []], ![[36, 37, 42, 45], [10, 5, 3, 8], [30, 15, 44, 10], [55, 48], [49, 60], [60, 64]], ![[50, 23, 50, 68], [63, 57, 52, 67], [66, 31, 63, 52], [21, 25], [14, 48], [5, 64]]]
 h' := ![![[28, 41, 8], [28, 27, 24], [41, 53, 5], [16, 31, 34], [4, 50, 46], [0, 0, 1], [0, 1]], ![[47, 29, 63], [24, 56, 60], [65, 40, 1], [44, 1, 27], [42, 6, 30], [63, 42, 29], [28, 41, 8]], ![[0, 1], [47, 59, 58], [41, 49, 65], [69, 39, 10], [41, 15, 66], [13, 29, 41], [47, 29, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 62], []]
 b := ![[], [21, 23, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [70, 41, 67, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![45540847828, 18297591837, -10137173213, 7623539900, 21568812129]
  a := ![-45, 35, 95, -17, 286]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12610010711, -23660264093, -12744689170, 7623539900, 21568812129]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71, -23, 21, 8, 32]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-71, -23, 21, 8, 32]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![13, 23, 1, 0, 0], ![28, 62, 0, 1, 0], ![0, 53, 0, 0, 1]] where
  M :=![![![-71, -23, 21, 8, 32], ![-240, -74, 73, 26, 112], ![-828, -277, 238, 78, 316], ![-1062, -383, 293, 143, 478], ![402, 148, -108, -42, -141]]]
  hmulB := by decide  
  f := ![![![1307, -561, 133, 28, 244]], ![![-1632, 828, -225, -54, -400]], ![![-251, 152, -46, -12, -80]], ![![-914, 509, -147, -37, -258]], ![![-1218, 616, -167, -40, -297]]]
  g := ![![![-8, -38, 21, 8, 32], ![-27, -131, 73, 26, 112], ![-86, -385, 238, 78, 316], ![-125, -582, 293, 143, 478], ![42, 179, -108, -42, -141]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [20, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 70], [0, 1]]
 g := ![![[40, 32], [68, 19], [57, 49], [49], [6], [1]], ![[0, 39], [62, 52], [49, 22], [49], [6], [1]]]
 h' := ![![[52, 70], [60, 48], [67, 44], [30, 7], [67, 7], [51, 52], [0, 1]], ![[0, 1], [0, 23], [12, 27], [39, 64], [5, 64], [57, 19], [52, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [30, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [20, 19, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1286, 3724, 3208, 2466, 13538]
  a := ![4, -12, -8, -8, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1578, -13246, 3208, 2466, 13538]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![1307, -561, 133, 28, 244]] ![![-71, -23, 21, 8, 32]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1508, -534, 410, 151, 635]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-1508, -534, 410, 151, 635]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![48, 12, 66, 1, 0], ![33, 27, 3, 0, 1]] where
  M :=![![![-1508, -534, 410, 151, 635], ![-4716, -1675, 1278, 456, 1928], ![-14304, -5222, 3797, 1436, 5760], ![-19230, -6602, 5366, 2117, 9040], ![7167, 2588, -1924, -779, -3116]]]
  hmulB := by decide  
  f := ![![![-2348, 910, -186, -33, -355]], ![![2328, -1543, 514, 140, 876]], ![![-6096, 1158, 137, 116, 64]], ![![-6696, 1370, 100, 111, -10]], ![![-441, -105, 107, 40, 159]]]
  g := ![![![-407, -267, -157, 151, 635], ![-1236, -811, -474, 456, 1928], ![-3744, -2438, -1483, 1436, 5760], ![-5742, -3782, -2212, 2117, 9040], ![2019, 1316, 806, -779, -3116]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [48, 24, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 19, 68], [71, 53, 5], [0, 1]]
 g := ![![[49, 6, 65], [58, 4], [36, 50], [27, 28, 64], [55, 1], []], ![[6, 30, 44, 59], [37, 35], [6, 24], [11, 53, 47, 17], [45, 35], [17, 25]], ![[57, 58, 70, 60], [15, 32], [58, 37], [62, 37, 66, 51], [38, 69], [7, 25]]]
 h' := ![![[57, 19, 68], [60, 12, 49], [56, 69, 2], [18, 50, 59], [61, 19, 8], [0, 0, 1], [0, 1]], ![[71, 53, 5], [22, 49, 55], [22, 18, 53], [50, 0, 30], [22, 7, 37], [24, 47, 53], [57, 19, 68]], ![[0, 1], [47, 12, 42], [57, 59, 18], [40, 23, 57], [68, 47, 28], [33, 26, 19], [71, 53, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 7], []]
 b := ![[], [21, 62, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [48, 24, 18, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8714210651, -3650715262, 1874004951, -1273429352, -3918041064]
  a := ![-53, 134, 111, 72, 336]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2489119909, 1608459530, 1338006375, -1273429352, -3918041064]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2348, 910, -186, -33, -355]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-2348, 910, -186, -33, -355]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![42, 14, 1, 0, 0], ![71, 33, 0, 1, 0], ![58, 15, 0, 0, 1]] where
  M :=![![![-2348, 910, -186, -33, -355], ![2328, -1543, 514, 140, 876], ![-6096, 1158, 137, 116, 64], ![-1704, -1582, 1018, 351, 1574], ![723, 492, -340, -119, -522]]]
  hmulB := by decide  
  f := ![![![-1508, -534, 410, 151, 635]], ![![-4716, -1675, 1278, 456, 1928]], ![![-1968, -700, 533, 194, 814]], ![![-3862, -1367, 1050, 382, 1613]], ![![-2069, -733, 562, 203, 858]]]
  g := ![![![389, 136, -186, -33, -355], ![-1096, -363, 514, 140, 876], ![-326, -76, 137, 116, 64], ![-2201, -699, 1018, 351, 1574], ![736, 233, -340, -119, -522]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [39, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 72], [0, 1]]
 g := ![![[18, 35], [54], [32], [52, 6], [54], [1]], ![[49, 38], [54], [32], [1, 67], [54], [1]]]
 h' := ![![[28, 72], [35, 53], [30, 28], [16, 55], [72, 58], [34, 28], [0, 1]], ![[0, 1], [59, 20], [11, 45], [23, 18], [17, 15], [15, 45], [28, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [67, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [39, 45, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2318558, -507208, 776366, -288827, -85617]
  a := ![59, -126, -123, -55, -374]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-129499, -7682, 776366, -288827, -85617]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-1508, -534, 410, 151, 635]] ![![-2348, 910, -186, -33, -355]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3370, 1492, -398, -87, -753]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-3370, 1492, -398, -87, -753]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![8, 73, 10, 1, 0], ![11, 7, 64, 0, 1]] where
  M :=![![![-3370, 1492, -398, -87, -753], ![5040, -1887, 448, 188, 1212], ![-8400, 3084, 369, -400, -128], ![-936, -5416, -1082, -797, -7822], ![1905, 1260, -556, 403, 1180]]]
  hmulB := by decide  
  f := ![![![-3540142, -1260668, 958086, 351551, 1470059]], ![![-10929660, -3892129, 2957944, 1085360, 4538584]], ![![-33743664, -12016372, 9132191, 3350880, 14012176]], ![![-15319586, -5455415, 4146008, 1521297, 6361516]], ![![-28577645, -10176713, 7734090, 2837874, 11866969]]]
  g := ![![![71, 166, 616, -87, -753], ![-124, -305, -1000, 188, 1212], ![-48, 420, 159, -400, -128], ![1158, 1361, 6424, -797, -7822], ![-181, -461, -1014, 403, 1180]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [51, 13, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 67, 59], [60, 11, 20], [0, 1]]
 g := ![![[38, 31, 18], [65, 18, 73], [4, 15, 64], [12, 61, 25], [18, 1], []], ![[34, 38, 51, 56], [58, 53, 1, 68], [39, 33, 32, 41], [47, 1, 12, 71], [57, 42], [17, 5]], ![[59, 22, 38, 51], [47, 64, 36, 18], [3, 74, 38, 8], [72, 37, 59, 23], [34, 65], [56, 5]]]
 h' := ![![[37, 67, 59], [3, 37, 27], [33, 57, 51], [20, 3, 8], [30, 31, 74], [0, 0, 1], [0, 1]], ![[60, 11, 20], [74, 16, 31], [15, 62, 53], [39, 33, 28], [10, 49, 36], [28, 58, 11], [37, 67, 59]], ![[0, 1], [33, 26, 21], [1, 39, 54], [69, 43, 43], [66, 78, 48], [33, 21, 67], [60, 11, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 20], []]
 b := ![[], [42, 39, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [51, 13, 61, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6347243541, -1298187678, -3710885484, 676591104, -4904918970]
  a := ![-42, 82, 88, 24, 266]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![694792701, -207024120, 3840987564, 676591104, -4904918970]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-586, 157, 367, -35, 597]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-586, 157, 367, -35, 597]] 
 ![![79, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![-586, 157, 367, -35, 597], ![-3372, -3062, -263, -670, -4912], ![33492, 7303, -11102, 5278, 4012], ![-26184, 39009, 35451, 1055, 90702], ![-19869, -16336, -584, -4351, -27080]]]
  hmulB := by decide  
  f := ![![![150656786, -68092477, 16924811, 3741371, 30711393]], ![![6918574, -3127703, 777570, 171923, 1410895]], ![![106567008, -48166399, 11972334, 2646644, 21724622]], ![![113267382, -51195747, 12725517, 2813189, 23091240]], ![![46056735, -20815496, 5173640, 1143637, 9388050]]]
  g := ![![![-423, 157, 367, -35, 597], ![2332, -3062, -263, -670, -4912], ![2323, 7303, -11102, 5278, 4012], ![-55389, 39009, 35451, 1055, 90702], ![12713, -16336, -584, -4351, -27080]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26, -14, 4, -1, -9]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-26, -14, 4, -1, -9]] 
 ![![79, 0, 0, 0, 0], ![54, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![-26, -14, 4, -1, -9], ![60, 1, -26, 20, 16], ![-216, 230, 241, 36, 664], ![-2130, -1082, 344, -325, -1316], ![639, 76, -252, 69, -126]]]
  hmulB := by decide  
  f := ![![![-68174, -22494, 17608, 6497, 26947]], ![![-49140, -16311, 12738, 4698, 19498]], ![![-14054, -4804, 3709, 1365, 5683]], ![![-29106, -9904, 7660, 2820, 11735]], ![![-17471, -5654, 4460, 1648, 6821]]]
  g := ![![![12, -14, 4, -1, -9], ![-8, 1, -26, 20, 16], ![-401, 230, 241, 36, 664], ![1185, -1082, 344, -325, -1316], ![0, 76, -252, 69, -126]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-3370, 1492, -398, -87, -753]] ![![-586, 157, 367, -35, 597]]
  ![![853345, 903037, 144925, 202184, 1562796]] where
 M := ![![![853345, 903037, 144925, 202184, 1562796]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![853345, 903037, 144925, 202184, 1562796]] ![![-26, -14, 4, -1, -9]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![568666174, -77701635, -309411953, 64547819, -359987753]]]
 hmul := by decide  
 g := ![![![![7198306, -983565, -3916607, 817061, -4556807]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-141227, -51329, 38813, 14218, 59568]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-141227, -51329, 38813, 14218, 59568]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![11, 13, 1, 0, 0], ![53, 46, 0, 1, 0], ![14, 62, 0, 0, 1]] where
  M :=![![![-141227, -51329, 38813, 14218, 59568], ![-442716, -155852, 119287, 43798, 182876], ![-1360044, -485559, 369724, 135610, 567068], ![-1886676, -669905, 511237, 187587, 783948], ![703140, 249780, -190548, -69916, -292207]]]
  hmulB := by decide  
  f := ![![![-8809, 253, 4225, -1098, 3616]], ![![-15108, -33322, -12923, -5370, -63420]], ![![1439, -3308, -2642, -158, -7328]], ![![-22771, -15074, 1524, -4463, -23092]], ![![-14326, -27182, -9616, -4636, -51031]]]
  g := ![![![-25972, -59074, 38813, 14218, 59568], ![-79957, -181441, 119287, 43798, 182876], ![-247630, -562509, 369724, 135610, 567068], ![-342502, -777708, 511237, 187587, 783948], ![127658, 289878, -190548, -69916, -292207]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [63, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 82], [0, 1]]
 g := ![![[2, 29], [38, 7], [51], [59], [30, 23], [1]], ![[0, 54], [69, 76], [51], [59], [37, 60], [1]]]
 h' := ![![[40, 82], [13, 64], [75, 67], [47, 47], [19, 68], [20, 40], [0, 1]], ![[0, 1], [0, 19], [16, 16], [18, 36], [0, 15], [43, 43], [40, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [2, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [63, 43, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2280811, -29066, 1063136, -107216, 1173472]
  a := ![-65, 150, 140, 80, 416]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-297849, -984014, 1063136, -107216, 1173472]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-103564, -36870, 28018, 10281, 42991]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-103564, -36870, 28018, 10281, 42991]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![64, 7, 1, 0, 0], ![25, 8, 0, 1, 0], ![19, 31, 0, 0, 1]] where
  M :=![![![-103564, -36870, 28018, 10281, 42991], ![-319632, -113857, 86502, 31740, 132732], ![-986832, -351438, 267023, 97980, 409728], ![-1363308, -485562, 368910, 135365, 566070], ![509133, 181332, -137772, -50553, -211402]]]
  hmulB := by decide  
  f := ![![![-260, -102, 58, -45, -125]], ![![1020, -287, -642, 96, -960]], ![![-52, -37, 1, -12, -64]], ![![-370, -152, 80, -64, -187]], ![![377, -157, -268, 30, -461]]]
  g := ![![![-35790, -19855, 28018, 10281, 42991], ![-110496, -61301, 86502, 31740, 132732], ![-341092, -189229, 267023, 97980, 409728], ![-471241, -261434, 368910, 135365, 566070], ![175988, 97634, -137772, -50553, -211402]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [45, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 82], [0, 1]]
 g := ![![[62, 48], [11, 17], [64], [44], [8, 28], [1]], ![[21, 35], [57, 66], [64], [44], [74, 55], [1]]]
 h' := ![![[32, 82], [3, 31], [19, 10], [49, 8], [55, 25], [38, 32], [0, 1]], ![[0, 1], [82, 52], [7, 73], [56, 75], [25, 58], [66, 51], [32, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [26, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [45, 51, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-135077, -54382, 30452, -22052, -61950]
  a := ![-13, 24, 27, 8, 82]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4285, 22040, 30452, -22052, -61950]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-808, 72, 60, 29, 75]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![-808, 72, 60, 29, 75]] 
 ![![83, 0, 0, 0, 0], ![63, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![74, 0, 0, 0, 1]] where
  M :=![![![-808, 72, 60, 29, 75], ![-624, -671, 420, 144, 652], ![-4776, -940, 1057, 400, 1560], ![-5568, -2044, 1720, 625, 2594], ![1965, 700, -596, -217, -898]]]
  hmulB := by decide  
  f := ![![![-560, -176, 164, 39, 223]], ![![-444, -143, 128, 31, 171]], ![![-120, -36, 37, 19, 83]], ![![-674, -172, 220, 36, 305]], ![![-479, -164, 132, 29, 154]]]
  g := ![![![-169, 72, 60, 29, 75], ![-289, -671, 420, 144, 652], ![-1297, -940, 1057, 400, 1560], ![-1719, -2044, 1720, 625, 2594], ![602, 700, -596, -217, -898]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-141227, -51329, 38813, 14218, 59568]] ![![-103564, -36870, 28018, 10281, 42991]]
  ![![3675034940, 1308706409, -994635661, -364961041, -1526128997]] where
 M := ![![![3675034940, 1308706409, -994635661, -364961041, -1526128997]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![3675034940, 1308706409, -994635661, -364961041, -1526128997]] ![![-808, 72, 60, 29, 75]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![-2421516617, -891893515, 668786195, 244813480, 1027466960]]]
 hmul := by decide  
 g := ![![![![-29174899, -10745705, 8057665, 2949560, 12379120]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32812040, 11684300, -8880298, -3258449, -13625567]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![32812040, 11684300, -8880298, -3258449, -13625567]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![17, 57, 45, 34, 1]] where
  M :=![![![32812040, 11684300, -8880298, -3258449, -13625567], ![101304096, 36074173, -27417088, -10060156, -42067660], ![312766896, 111375620, -84647699, -31059792, -129879968], ![432167232, 153893800, -116962398, -42917029, -179462314], ![-161368713, -57463052, 43673068, 16024965, 67010170]]]
  hmulB := by decide  
  f := ![![![-32, 20, 6, -1, 15]], ![![-84, -99, 8, -24, -128]], ![![912, 124, -387, 128, -144]], ![![90, 1432, 826, 153, 2928]], ![![427, 545, 127, 106, 959]]]
  g := ![![![2971311, 8857771, 6789553, 5168661, -13625567], ![9173644, 27347537, 20962108, 15957756, -42067660], ![28322768, 84432964, 64718549, 49268080, -129879968], ![39135130, 116665682, 89425188, 68076423, -179462314], ![-14612827, -43562278, -33390838, -25419335, 67010170]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [45, 2, 57, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 49, 21, 11], [70, 54, 72, 21], [76, 74, 85, 57], [0, 1]]
 g := ![![[35, 25, 40, 18], [82, 40, 81], [6, 16, 39], [50, 35, 86, 45], [84, 1], []], ![[86, 22, 42, 48, 13, 1], [8, 80, 81], [88, 20, 50], [54, 36, 52, 17, 15, 32], [85, 57, 10, 23, 55, 53], [54, 35, 32]], ![[84, 70, 38, 39, 15, 73], [66, 30, 67], [14, 9, 69], [35, 69, 76, 40, 49, 55], [32, 77, 2, 47, 34, 79], [25, 18, 85]], ![[61, 73, 30, 14, 72, 45], [25, 52, 67], [62, 27, 55], [42, 18, 36, 48, 10, 49], [36, 68, 84, 27, 34, 8], [36, 31, 45]]]
 h' := ![![[27, 49, 21, 11], [49, 34, 11, 14], [88, 69, 0, 80], [64, 0, 66, 67], [47, 54, 16, 57], [0, 0, 1], [0, 1]], ![[70, 54, 72, 21], [13, 39, 53, 80], [27, 10, 22, 9], [31, 29, 63, 53], [32, 36, 58, 10], [79, 73, 15, 56], [27, 49, 21, 11]], ![[76, 74, 85, 57], [36, 6, 9, 66], [43, 38, 9, 45], [53, 12, 29, 46], [50, 3, 57, 57], [37, 25, 56, 50], [70, 54, 72, 21]], ![[0, 1], [7, 10, 16, 18], [8, 61, 58, 44], [22, 48, 20, 12], [28, 85, 47, 54], [62, 80, 17, 72], [76, 74, 85, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [27, 38, 50], []]
 b := ![[], [], [3, 45, 78, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 4
  hpos := by decide
  P := [45, 2, 57, 5, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![464101700499924, 96282556286936, -157070348031424, 69452933447905, 36329051242182]
  a := ![-87, 190, 184, 89, 552]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1724631130530, -22185093983342, -20133456785726, -13098143918947, 36329051242182]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32, 20, 6, -1, 15]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-32, 20, 6, -1, 15]] 
 ![![89, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-32, 20, 6, -1, 15], ![-84, -99, 8, -24, -128], ![912, 124, -387, 128, -144], ![90, 1432, 826, 153, 2928], ![-765, -460, 76, -143, -680]]]
  hmulB := by decide  
  f := ![![![32812040, 11684300, -8880298, -3258449, -13625567]], ![![19203304, 6838257, -5197210, -1907013, -7974387]], ![![4251584, 1513980, -1150655, -422210, -1765518]], ![![26976288, 9606200, -7300902, -2678921, -11202206]], ![![-1444457, -514368, 390930, 143444, 599827]]]
  g := ![![![-11, 20, 6, -1, 15], ![71, -99, 8, -24, -128], ![-134, 124, -387, 128, -144], ![-942, 1432, 826, 153, 2928], ![347, -460, 76, -143, -680]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![32812040, 11684300, -8880298, -3258449, -13625567]] ![![-32, 20, 6, -1, 15]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30328, 546, 14352, -3811, 11787]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-30328, 546, 14352, -3811, 11787]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![22, 73, 62, 46, 1]] where
  M :=![![![-30328, 546, 14352, -3811, 11787], ![-47856, -112667, -45186, -17736, -215540], ![1399656, 538550, -325499, 234292, 619272], ![-2536764, 877766, 1697620, -233027, 2701502], ![-419631, -656204, -198020, -121357, -1206094]]]
  hmulB := by decide  
  f := ![![![997256, -451186, 112252, 24837, 203645]], ![![-1370892, 617809, -153142, -33764, -278064]], ![![1870968, -850710, 212641, 47260, 385352]], ![![-612390, 269386, -65224, -14049, -119084]], ![![101525, -54071, 15356, 3803, 27058]]]
  g := ![![![-2986, -8865, -7386, -5629, 11787], ![48392, 161049, 137302, 102032, -215540], ![-126024, -460498, -399179, -291260, 619272], ![-638864, -2024040, -1709232, -1283527, 2701502], ![269221, 900914, 768864, 570711, -1206094]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [32, 70, 70, 77, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 33, 65, 94], [62, 85, 72, 13], [50, 75, 57, 87], [0, 1]]
 g := ![![[15, 15, 44, 65], [29, 38, 94], [18, 32, 22], [96, 88, 24], [39, 20, 1], []], ![[55, 6, 73, 81, 52, 44], [92, 64, 96], [47, 74, 64], [0, 8, 48], [96, 11, 22], [94, 3, 70, 17, 51, 70]], ![[57, 92, 85, 88, 80, 46], [17, 56, 31], [81, 90, 96], [88, 41, 64], [93, 53, 94], [86, 31, 27, 48, 31, 63]], ![[73, 54, 6, 52, 91, 34], [34, 44, 89], [24, 14, 75], [8, 32, 86], [12, 19, 36], [35, 56, 43, 80, 10, 67]]]
 h' := ![![[5, 33, 65, 94], [60, 71, 25, 68], [55, 91, 69, 71], [7, 38, 15, 64], [13, 25, 9, 86], [0, 0, 0, 1], [0, 1]], ![[62, 85, 72, 13], [32, 24, 85, 70], [39, 37, 51, 75], [31, 59, 58, 8], [82, 38, 41, 57], [27, 67, 55, 64], [5, 33, 65, 94]], ![[50, 75, 57, 87], [7, 52, 87, 60], [58, 78, 77, 82], [15, 16, 46, 75], [42, 6, 35, 89], [60, 7, 60, 26], [62, 85, 72, 13]], ![[0, 1], [78, 47, 94, 93], [14, 85, 94, 63], [43, 81, 75, 47], [28, 28, 12, 59], [11, 23, 79, 6], [50, 75, 57, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [63, 66, 92], []]
 b := ![[], [], [16, 64, 27, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [32, 70, 70, 77, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13748544966358, 3700569782452, -4146482959832, 2142365795842, 2818431970242]
  a := ![-35, 76, 73, 34, 222]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-497494416278, -2082937773662, -1844219227988, -1314489740570, 2818431970242]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![997256, -451186, 112252, 24837, 203645]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![997256, -451186, 112252, 24837, 203645]] 
 ![![97, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![81, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![997256, -451186, 112252, 24837, 203645], ![-1370892, 617809, -153142, -33764, -278064], ![1870968, -850710, 212641, 47260, 385352], ![-612390, 269386, -65224, -14049, -119084], ![153333, -66588, 15916, 3383, 29148]]]
  hmulB := by decide  
  f := ![![![-30328, 546, 14352, -3811, 11787]], ![![-1744, -1139, 126, -340, -1736]], ![![-10896, 6008, 8629, -767, 16227]], ![![-35532, 9218, 21940, -3581, 31496]], ![![-23711, -6416, 7132, -3687, -4900]]]
  g := ![![![-202696, -451186, 112252, 24837, 203645], ![276446, 617809, -153142, -33764, -278064], ![-384121, -850710, 212641, 47260, 385352], ![117504, 269386, -65224, -14049, -119084], ![-28641, -66588, 15916, 3383, 29148]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-30328, 546, 14352, -3811, 11787]] ![![997256, -451186, 112252, 24837, 203645]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27001, 9625, -7301, -2672, -11166]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![27001, 9625, -7301, -2672, -11166]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![3, 68, 42, 91, 1]] where
  M :=![![![27001, 9625, -7301, -2672, -11166], ![83028, 29628, -22439, -8302, -34540], ![257052, 90823, -69996, -25610, -108236], ![360024, 128721, -97029, -34439, -144612], ![-133890, -47260, 36460, 13010, 55461]]]
  hmulB := by decide  
  f := ![![![-16759, 7645, -1919, -428, -3474]], ![![23412, -10346, 2509, 542, 4580]], ![![-30732, 14647, -3842, -890, -6884]], ![![11616, -4131, 729, 101, 1452]], ![![12921, -4360, 690, 73, 1423]]]
  g := ![![![599, 7613, 4571, 10034, -11166], ![1848, 23548, 14141, 31038, -34540], ![5760, 73771, 44316, 97266, -108236], ![7860, 98637, 59175, 129953, -144612], ![-2973, -37808, -22702, -49841, 55461]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 4 2 6 [55, 73, 4, 16, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 84, 47, 53], [54, 16, 84, 56], [74, 0, 71, 93], [0, 1]]
 g := ![![[32, 68, 40, 52], [64, 18, 64], [45, 91, 70, 64], [78, 77, 1], [50, 85, 1], []], ![[45, 60, 12, 26, 1, 11], [90, 92, 33], [73, 56, 6, 84, 15, 8], [27, 21, 92], [84, 84, 68], [4, 6, 23, 1, 0, 3]], ![[46, 28, 70, 54, 8, 24], [80, 64, 47], [74, 88, 83, 36, 29, 78], [41, 38, 16], [76, 94, 9], [35, 58, 7, 10, 12, 78]], ![[84, 23, 16, 82, 56, 12], [20, 24, 25], [0, 26, 74, 50, 95, 93], [32, 22, 13], [69, 96, 87], [91, 8, 72, 15, 8, 94]]]
 h' := ![![[58, 84, 47, 53], [91, 32, 89, 31], [50, 63, 2, 8], [77, 28, 20, 93], [78, 58, 4, 100], [0, 0, 0, 1], [0, 1]], ![[54, 16, 84, 56], [32, 86, 84, 60], [72, 0, 49, 29], [35, 78, 52, 65], [56, 25, 98, 71], [63, 19, 14, 13], [58, 84, 47, 53]], ![[74, 0, 71, 93], [21, 98, 84, 17], [52, 89, 48, 59], [98, 68, 86, 45], [63, 0, 39, 97], [100, 95, 6, 3], [54, 16, 84, 56]], ![[0, 1], [17, 87, 46, 94], [62, 50, 2, 5], [22, 28, 44, 100], [60, 18, 61, 35], [57, 88, 81, 84], [74, 0, 71, 93]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [72, 41, 30], []]
 b := ![[], [], [52, 84, 42, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 4
  hpos := by decide
  P := [55, 73, 4, 16, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1143409000583, -320532128511, -719844533451, 117029770502, -1051411499618]
  a := ![-23, 53, 49, 28, 147]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![42550925737, 704707424213, 430093450005, 948470061740, -1051411499618]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 104060401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16759, 7645, -1919, -428, -3474]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-16759, 7645, -1919, -428, -3474]] 
 ![![101, 0, 0, 0, 0], ![83, 1, 0, 0, 0], ![80, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![94, 0, 0, 0, 1]] where
  M :=![![![-16759, 7645, -1919, -428, -3474], ![23412, -10346, 2509, 542, 4580], ![-30732, 14647, -3842, -890, -6884], ![11616, -4131, 729, 101, 1452], ![-3030, 980, -140, -10, -299]]]
  hmulB := by decide  
  f := ![![![27001, 9625, -7301, -2672, -11166]], ![![23011, 8203, -6222, -2278, -9518]], ![![23932, 8523, -6476, -2370, -9916]], ![![9446, 3371, -2551, -923, -3864]], ![![23804, 8490, -6434, -2358, -9843]]]
  g := ![![![-1602, 7645, -1919, -428, -3474], ![2366, -10346, 2509, 542, 4580], ![-2697, 14647, -3842, -890, -6884], ![1559, -4131, 729, 101, 1452], ![-444, 980, -140, -10, -299]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![27001, 9625, -7301, -2672, -11166]] ![![-16759, 7645, -1919, -428, -3474]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![883, 197, -291, 128, 82]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![883, 197, -291, 128, 82]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![13, 37, 39, 1, 0], ![47, 69, 75, 0, 1]] where
  M :=![![![883, 197, -291, 128, 82], ![-1260, 1928, 1733, 22, 4372], ![-26364, -16729, 2192, -5146, -25396], ![92256, 4293, -40107, 12139, -23772], ![-3834, 12004, 8948, 778, 26183]]]
  hmulB := by decide  
  f := ![![![-251831, -89861, 68241, 25036, 104714]], ![![-778500, -276978, 210571, 77270, 323084]], ![![-2402124, -855755, 650262, 238594, 997756]], ![![-1253213, -446339, 339193, 124459, 520450]], ![![-2373517, -845390, 642436, 235726, 985741]]]
  g := ![![![-45, -99, -111, 128, 82], ![-2010, -2918, -3175, 22, 4372], ![11982, 18699, 20462, -5146, -25396], ![10211, 11606, 12324, 12139, -23772], ![-12083, -17703, -19273, 778, 26183]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [75, 53, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 50, 47], [1, 52, 56], [0, 1]]
 g := ![![[77, 60, 52], [72, 70, 2], [29, 61, 83], [19, 4], [8, 36], [1]], ![[8, 26, 60, 24], [73, 32, 69, 39], [7, 43, 23, 39], [76, 83], [18, 72], [46, 18, 5, 102]], ![[86, 38, 28, 18], [89, 50, 50, 18], [55, 13, 58, 23], [14, 52], [54, 63], [24, 58, 63, 1]]]
 h' := ![![[96, 50, 47], [59, 39, 84], [91, 58, 38], [89, 74, 17], [81, 88, 2], [28, 50, 97], [0, 1]], ![[1, 52, 56], [73, 60, 21], [38, 88, 67], [84, 73, 36], [4, 29, 17], [18, 60, 81], [96, 50, 47]], ![[0, 1], [8, 4, 101], [20, 60, 101], [5, 59, 50], [5, 89, 84], [55, 96, 28], [1, 52, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80, 87], []]
 b := ![[], [33, 62, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [75, 53, 6, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![121126739613, 127192450016, 19743098884, 26513437054, 214389661124]
  a := ![157, -346, -331, -173, -992]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-99998660339, -151909624646, -165956364374, 26513437054, 214389661124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-251831, -89861, 68241, 25036, 104714]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-251831, -89861, 68241, 25036, 104714]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![52, 25, 1, 0, 0], ![71, 23, 0, 1, 0], ![60, 65, 0, 0, 1]] where
  M :=![![![-251831, -89861, 68241, 25036, 104714], ![-778500, -276978, 210571, 77270, 323084], ![-2402124, -855755, 650262, 238594, 997756], ![-3319800, -1182093, 898401, 329653, 1378476], ![1239606, 441404, -335468, -123094, -514731]]]
  hmulB := by decide  
  f := ![![![883, 197, -291, 128, 82]], ![![-1260, 1928, 1733, 22, 4372]], ![![-116, 405, 295, 20, 856]], ![![1223, 608, -203, 211, 802]], ![![-318, 1448, 1011, 96, 3061]]]
  g := ![![![-115153, -89108, 68241, 25036, 104714], ![-355334, -274941, 210571, 77270, 323084], ![-1097294, -849069, 650262, 238594, 997756], ![-1516025, -1173059, 898401, 329653, 1378476], ![566092, 438027, -335468, -123094, -514731]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [32, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 102], [0, 1]]
 g := ![![[95, 29], [38, 19], [66, 25], [16], [16], [50, 1]], ![[0, 74], [61, 84], [80, 78], [16], [16], [100, 102]]]
 h' := ![![[50, 102], [20, 82], [51, 88], [36, 98], [41, 4], [48, 99], [0, 1]], ![[0, 1], [0, 21], [22, 15], [95, 5], [35, 99], [54, 4], [50, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [51, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [32, 53, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1995952, -252566, 783590, -189488, 400342]
  a := ![58, -126, -122, -62, -367]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-517568, -402974, 783590, -189488, 400342]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![883, 197, -291, 128, 82]] ![![-251831, -89861, 68241, 25036, 104714]]
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


lemma PB1705I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB1705I2 : PrimesBelowBoundCertificateInterval O 61 103 1705 where
  m := 9
  g := ![2, 2, 2, 3, 3, 2, 2, 2, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB1705I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
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
    · exact ![357911, 5041]
    · exact ![389017, 5329]
    · exact ![493039, 79, 79]
    · exact ![6889, 6889, 83]
    · exact ![62742241, 89]
    · exact ![88529281, 97]
    · exact ![104060401, 101]
    · exact ![1092727, 10609]
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I67N1, I79N1, I79N2, I83N2, I89N1, I97N1, I101N1]
  Il := ![[I67N1], [], [], [I79N1, I79N2], [I83N2], [I89N1], [I97N1], [I101N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
