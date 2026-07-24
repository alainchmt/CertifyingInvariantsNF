
import IdealArithmetic.Examples.NF5_1_364500000_3.RI5_1_364500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![48265763, -14919089, 183527, -1027186, 2874541]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![48265763, -14919089, 183527, -1027186, 2874541]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![40, 91, 102, 1, 0], ![79, 89, 24, 0, 1]] where
  M :=![![![48265763, -14919089, 183527, -1027186, 2874541], ![-17247246, 5331175, -65582, 367054, -1027186], ![3081558, -952519, 11718, -65582, 183527], ![8073042, -2495402, 30698, -171809, 480802], ![196746, -60809, 743, -4186, 11718]]]
  hmulB := by decide  
  f := ![![![43, 199, 167, 104, 13]], ![![-78, 15, 424, 334, 104]], ![![-312, -607, 368, 424, 167]], ![![-352, -503, 772, 729, 254]], ![![-115, -11, 552, 450, 137]]]
  g := ![![![-1287248, -1656816, 336145, -1027186, 2874541], ![459984, 592045, -120118, 367054, -1027186], ![-82185, -105780, 21462, -65582, 183527], ![-215308, -277123, 56224, -171809, 480802], ![-5248, -6755, 1369, -4186, 11718]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [55, 25, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 87, 47], [0, 19, 60], [0, 1]]
 g := ![![[75, 98, 69], [63, 89, 16], [58, 16], [55, 98, 100], [15, 57], [1]], ![[58, 78, 40, 9], [68, 20, 40, 76], [72, 33], [69, 81, 7, 90], [19, 47], [94, 68, 12, 33]], ![[0, 85, 44, 50], [31, 44, 40, 6], [16, 29], [60, 84, 41, 22], [72, 1], [61, 81, 102, 74]]]
 h' := ![![[48, 87, 47], [66, 82, 60], [5, 89, 4], [78, 45, 4], [60, 96, 97], [52, 82, 48], [0, 1]], ![[0, 19, 60], [94, 25, 72], [86, 43, 86], [80, 67, 51], [5, 103, 42], [27, 13, 58], [48, 87, 47]], ![[0, 1], [7, 0, 82], [51, 82, 17], [17, 102, 52], [52, 15, 75], [69, 12, 1], [0, 19, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 54], []]
 b := ![[], [87, 98, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [55, 25, 59, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12917, -38425, 11900, -9121, 2889]
  a := ![0, -2, -1, -3, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1156, 4995, 8158, -9121, 2889]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, -199, -167, -104, -13]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-43, -199, -167, -104, -13]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![83, 5, 1, 0, 0], ![13, 17, 0, 1, 0], ![43, 62, 0, 0, 1]] where
  M :=![![![-43, -199, -167, -104, -13], ![78, -15, -424, -334, -104], ![312, 607, -368, -424, -167], ![462, 1232, 196, -201, -160], ![1272, 3665, 697, -32, -368]]]
  hmulB := by decide  
  f := ![![![-48265763, 14919089, -183527, 1027186, -2874541]], ![![17247246, -5331175, 65582, -367054, 1027186]], ![![-36662651, 11332533, -139407, 780250, -2183500]], ![![-3199297, 988912, -12165, 68087, -190539]], ![![-9404629, 2906998, -35760, 200148, -560107]]]
  g := ![![![147, 30, -167, -104, -13], ![412, 133, -424, -334, -104], ![407, 187, -368, -424, -167], ![-59, 127, 196, -201, -160], ![-377, 220, 697, -32, -368]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P1 : CertificateIrreducibleZModOfList' 107 2 2 6 [14, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 106], [0, 1]]
 g := ![![[6, 23], [87, 34], [90], [57, 53], [79], [23, 1]], ![[0, 84], [13, 73], [90], [99, 54], [79], [46, 106]]]
 h' := ![![[23, 106], [66, 39], [71, 26], [58, 82], [72, 38], [106, 87], [0, 1]], ![[0, 1], [0, 68], [27, 81], [18, 25], [90, 69], [74, 20], [23, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [98, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N1 : CertifiedPrimeIdeal' SI107N1 107 where
  n := 2
  hpos := by decide
  P := [14, 84, 1]
  hirr := P107P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1025, 1308, -31416, 17706, 3640]
  a := ![3, -65, 1, -66, 1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![20765, -3442, -31416, 17706, 3640]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N1 B_one_repr
lemma NI107N1 : Nat.card (O ⧸ I107N1) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![48265763, -14919089, 183527, -1027186, 2874541]] ![![-43, -199, -167, -104, -13]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -24, -41, -6, 11]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-5, -24, -41, -6, 11]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![61, 39, 108, 1, 0], ![13, 29, 75, 0, 1]] where
  M :=![![![-5, -24, -41, -6, 11], ![-66, -211, 68, -82, -6], ![18, 46, -200, 68, -41], ![156, 322, -227, -159, 37], ![-204, -580, 973, -386, -200]]]
  hmulB := by decide  
  f := ![![![-369515, 114218, -1405, 7864, -22007]], ![![132042, -40815, 502, -2810, 7864]], ![![-23592, 7292, -90, 502, -1405]], ![![-183491, 56717, -698, 3905, -10928]], ![![-25187, 7785, -96, 536, -1500]]]
  g := ![![![2, -1, -2, -6, 11], ![46, 29, 86, -82, -6], ![-33, -13, -41, 68, -41], ![86, 50, 130, -159, 37], ![238, 186, 529, -386, -200]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [97, 42, 87, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 27, 13], [93, 81, 96], [0, 1]]
 g := ![![[94, 83, 102], [100, 48], [14, 43, 48], [37, 52, 26], [80, 48], [1]], ![[9, 6, 5, 24], [55, 108], [66, 62, 34, 65], [72, 59, 0, 33], [28, 61], [62, 48, 2, 17]], ![[35, 35, 83, 44], [51, 82], [30, 0, 1, 96], [7, 79, 27, 53], [27, 102], [71, 96, 36, 92]]]
 h' := ![![[38, 27, 13], [103, 10, 50], [59, 101, 87], [8, 29, 22], [14, 23, 74], [12, 67, 22], [0, 1]], ![[93, 81, 96], [10, 8, 38], [107, 17, 76], [104, 5, 88], [31, 85, 80], [26, 50, 37], [38, 27, 13]], ![[0, 1], [33, 91, 21], [82, 100, 55], [85, 75, 108], [19, 1, 64], [26, 101, 50], [93, 81, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 93], []]
 b := ![[], [78, 43, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [97, 42, 87, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5083, -16316, -12348, 2444, 4818]
  a := ![1, -4, 0, -5, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1989, -2306, -5850, 2444, 4818]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-369515, 114218, -1405, 7864, -22007]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-369515, 114218, -1405, 7864, -22007]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![34, 1, 1, 0, 0], ![75, 71, 0, 1, 0], ![2, 43, 0, 0, 1]] where
  M :=![![![-369515, 114218, -1405, 7864, -22007], ![132042, -40815, 502, -2810, 7864], ![-23592, 7292, -90, 502, -1405], ![-61806, 19104, -235, 1315, -3681], ![-1506, 466, -7, 32, -90]]]
  hmulB := by decide  
  f := ![![![-5, -24, -41, -6, 11]], ![![-66, -211, 68, -82, -6]], ![![-2, -9, -14, -2, 3]], ![![-45, -151, 14, -59, 4]], ![![-28, -89, 35, -36, -4]]]
  g := ![![![-7959, 4620, -1405, 7864, -22007], ![2844, -1651, 502, -2810, 7864], ![-508, 295, -90, 502, -1405], ![-1331, 773, -235, 1315, -3681], ![-32, 19, -7, 32, -90]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [66, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 108], [0, 1]]
 g := ![![[56, 38], [106], [97, 5], [1, 66], [66], [10, 1]], ![[0, 71], [106], [38, 104], [7, 43], [66], [20, 108]]]
 h' := ![![[10, 108], [58, 16], [29, 91], [43, 88], [40, 34], [103, 34], [0, 1]], ![[0, 1], [0, 93], [67, 18], [51, 21], [53, 75], [7, 75], [10, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [89, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where
  n := 2
  hpos := by decide
  P := [66, 99, 1]
  hirr := P109P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-548, -439, -1092, 1676, 1002]
  a := ![1, 18, 1, 17, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-836, -1481, -1092, 1676, 1002]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-5, -24, -41, -6, 11]] ![![-369515, 114218, -1405, 7864, -22007]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1061, 2863, 351, -352, -361]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![1061, 2863, 351, -352, -361]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![36, 66, 1, 0, 0], ![110, 13, 0, 1, 0], ![4, 42, 0, 0, 1]] where
  M :=![![![1061, 2863, 351, -352, -361], ![2166, 6827, 2468, 702, -352], ![1056, 4957, 4716, 2468, 351], ![-2136, -3160, 4244, 4365, 1410], ![-7404, -14085, 8131, 10956, 4716]]]
  hmulB := by decide  
  f := ![![![-157129852157, 48569297981, -597474283, 3344018146, -9358107687]], ![![56148646122, -17355711135, 213500946, -1194948566, 3344018146]], ![![-17353062726, 5363882565, -65983698, 369305742, -1033488083]], ![![-146731267592, 45355065005, -557934458, 3122716751, -8738804144]], ![![15301621466, -4729776057, 58183249, -325647222, 911311374]]]
  g := ![![![253, -5, 351, -352, -361], ![-1438, -1331, 2468, 702, -352], ![-3908, -3125, 4716, 2468, 351], ![-5670, -3533, 4244, 4365, 1410], ![-13488, -7887, 8131, 10956, 4716]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [30, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 112], [0, 1]]
 g := ![![[90, 49], [100], [104], [2], [83, 1], [12, 1]], ![[0, 64], [100], [104], [2], [95, 112], [24, 112]]]
 h' := ![![[12, 112], [29, 7], [59, 10], [69, 68], [109, 51], [92, 1], [0, 1]], ![[0, 1], [0, 106], [66, 103], [94, 45], [43, 62], [104, 112], [12, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [57, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [30, 101, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-844, -1516, 1539, 826, -1069]
  a := ![-1, 2, 1, 4, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1264, -610, 1539, 826, -1069]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43669267, 105905370, -8708050, -31061100, -18107724]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![43669267, 105905370, -8708050, -31061100, -18107724]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![83, 4, 1, 0, 0], ![7, 26, 0, 1, 0], ![61, 29, 0, 0, 1]] where
  M :=![![![43669267, 105905370, -8708050, -31061100, -18107724], ![108646344, 306577077, 61794600, -17416100, -31061100], ![93183300, 318178722, 159979627, 61794600, -8708050], ![-28199022, 38603300, 212843872, 168687677, 46427850], ![-185383800, -193594178, 532777050, 487482344, 159979627]]]
  hmulB := by decide  
  f := ![![![-12453157, -30786298, 31287922, -3146852, -4770584]], ![![28623504, 90393525, -106131584, 62575844, -3146852]], ![![-8050243, -19547268, 19608341, -1035548, -3338566]], ![![4857199, 16648472, -20291922, 14309977, -1475262]], ![![3441007, 14512601, -19113176, 17800416, -2999053]]]
  g := ![![![18481737, 13039382, -8708050, -31061100, -18107724], ![-26581112, 12504329, 61794600, -17416100, -31061100], ![-115809707, -14830672, 159979627, 61794600, -8708050], ![-192098699, -57920880, 212843872, 168687677, 46427850], ![-509531085, -173793385, 532777050, 487482344, 159979627]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [4, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 112], [0, 1]]
 g := ![![[58, 85], [28], [50], [91], [25, 7], [107, 1]], ![[0, 28], [28], [50], [91], [96, 106], [101, 112]]]
 h' := ![![[107, 112], [110, 56], [83, 49], [31, 84], [13, 59], [24, 32], [0, 1]], ![[0, 1], [0, 57], [15, 64], [92, 29], [111, 54], [58, 81], [107, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [11, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [4, 6, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![124, 1244, -3068, 3136, -444]
  a := ![0, -10, 2, -20, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2300, -488, -3068, 3136, -444]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10471, 35666, 17807, 6822, -1007]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![10471, 35666, 17807, 6822, -1007]] 
 ![![113, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![93, 0, 0, 1, 0], ![56, 0, 0, 0, 1]] where
  M :=![![![10471, 35666, 17807, 6822, -1007], ![6042, 43383, 54440, 35614, 6822], ![-20466, -20924, 59686, 54440, 17807], ![-56442, -135634, 13671, 41879, 23809], ![-163320, -420830, -15371, 81782, 59686]]]
  hmulB := by decide  
  f := ![![![-41612239, 12862180, -157965, 885544, -2478309]], ![![-31537900, 9748247, -119728, 671158, -1878310]], ![![-11439257, 3535830, -43423, 243430, -681288]], ![![-34308843, 10604708, -130222, 730121, -2043342]], ![![-20623474, 6374704, -78359, 438916, -1228276]]]
  g := ![![![-37052, 35666, 17807, 6822, -1007], ![-80590, 43383, 54440, 35614, 6822], ![-54260, -20924, 59686, 54440, 17807], ![52710, -135634, 13671, 41879, 23809], ![226163, -420830, -15371, 81782, 59686]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![1061, 2863, 351, -352, -361]] ![![43669267, 105905370, -8708050, -31061100, -18107724]]
  ![![466944521003, 1158075637101, -43422010167, -296487405288, -185291998561]] where
 M := ![![![466944521003, 1158075637101, -43422010167, -296487405288, -185291998561]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![466944521003, 1158075637101, -43422010167, -296487405288, -185291998561]] ![![10471, 35666, 17807, 6822, -1007]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![59771375273112293, 185993605274438211, 67563676662640182, 14495160756134146, -11461443730004606]]]
 hmul := by decide  
 g := ![![![![528950223655861, 1645961108623347, 597908643032214, 128275758903842, -101428705575262]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
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


def P127P0 : CertificateIrreducibleZModOfList' 127 5 2 6 [88, 91, 5, 95, 61, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [124, 6, 123, 6, 102], [111, 111, 35, 39, 73], [86, 75, 115, 112, 59], [126, 61, 108, 97, 20], [0, 1]]
 g := ![![[39, 1, 49, 49, 121], [112, 54, 1, 76, 64], [32, 38, 32, 83, 104], [123, 67, 66, 93, 16], [70, 66, 1], []], ![[26, 66, 11, 108, 89, 54, 18, 90], [58, 120, 46, 107, 56, 13, 126, 40], [125, 98, 15, 6, 26, 83, 72, 93], [70, 45, 34, 21, 18, 3, 70, 14], [72, 89, 2, 121, 90, 86, 93, 95], [114, 55, 37, 71, 96, 119, 64, 123]], ![[73, 54, 124, 68, 91, 19, 84, 22], [121, 11, 75, 85, 113, 126, 22, 34], [80, 118, 27, 125, 101, 15, 57, 73], [20, 45, 70, 27, 42, 65, 78, 30], [14, 5, 51, 67, 25, 55, 11, 2], [36, 63, 40, 76, 50, 63, 90, 16]], ![[33, 88, 101, 103, 95, 40, 113, 33], [39, 88, 26, 67, 4, 118, 42, 45], [82, 101, 66, 38, 76, 44, 122, 63], [93, 66, 59, 115, 118, 114, 89, 123], [39, 112, 49, 33, 125, 39, 121, 78], [99, 68, 68, 126, 63, 102, 123, 20]], ![[110, 35, 113, 64, 47, 19, 66, 85], [124, 18, 3, 63, 90, 12, 42, 56], [81, 21, 40, 116, 1, 98, 93, 40], [12, 54, 82, 120, 120, 6, 87, 28], [52, 55, 56, 14, 122, 26, 110, 119], [30, 12, 31, 51, 6, 58, 2, 126]]]
 h' := ![![[124, 6, 123, 6, 102], [50, 18, 34, 101, 116], [105, 46, 19, 37, 119], [98, 88, 39, 115, 55], [63, 14, 33, 41, 123], [0, 0, 0, 1], [0, 1]], ![[111, 111, 35, 39, 73], [38, 88, 96, 98, 112], [119, 1, 23, 87, 10], [107, 62, 13, 91, 13], [18, 77, 100, 116, 17], [101, 61, 8, 29, 38], [124, 6, 123, 6, 102]], ![[86, 75, 115, 112, 59], [25, 70, 22, 30, 3], [50, 22, 97, 81, 52], [7, 23, 63, 115, 1], [71, 125, 59, 109, 18], [102, 101, 79, 21, 89], [111, 111, 35, 39, 73]], ![[126, 61, 108, 97, 20], [80, 120, 113, 69, 17], [100, 47, 107, 93, 102], [91, 126, 96, 24, 42], [74, 93, 81, 51, 74], [91, 12, 117, 97, 122], [86, 75, 115, 112, 59]], ![[0, 1], [90, 85, 116, 83, 6], [38, 11, 8, 83, 98], [94, 82, 43, 36, 16], [82, 72, 108, 64, 22], [26, 80, 50, 106, 5], [126, 61, 108, 97, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 42, 68, 39], [], [], []]
 b := ![[], [50, 69, 27, 44, 93], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 5
  hpos := by decide
  P := [88, 91, 5, 95, 61, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1417982305, -4579133082, 5247330755, -3298976257, 230282750]
  a := ![13, 0, 1, 1, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11165215, -36056166, 41317565, -25976191, 1813250]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1372481, -2415800, 1740791, 2421916, -1232503]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-1372481, -2415800, 1740791, 2421916, -1232503]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![38, 122, 6, 55, 1]] where
  M :=![![![-1372481, -2415800, 1740791, 2421916, -1232503], ![7395018, 18855855, -19578546, 3481582, 2421916], ![-7265748, -24256134, 29224644, -19578546, 1740791], ![-8919882, -11504412, 4026367, 27483853, -11000231], ![58735638, 135853816, -131270343, -11525812, 29224644]]]
  hmulB := by decide  
  f := ![![![-254929, 746706, 2694489, 2077502, 548845]], ![![-3293070, -5793115, 4904360, 5388978, 2077502]], ![![-6232506, -14775620, 1899906, 4904360, 2694489]], ![![-6436932, -19478410, -6207535, -794583, 1413429]], ![![-6241078, -14404374, 2660912, 5455067, 2825319]]]
  g := ![![![347043, 1129386, 69739, 535951, -1232503], ![-646090, -2111587, -260382, -990258, 2421916], ![-560426, -1806356, 143358, -880321, 1740791], ![3122816, 10156670, 534563, 4828218, -11000231], ![-8029014, -26179792, -2340597, -12357872, 29224644]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 4 2 7 [55, 24, 89, 125, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 40, 104, 7], [115, 33, 89, 27], [125, 57, 69, 97], [0, 1]]
 g := ![![[90, 5, 39, 80], [97, 116, 43, 3], [104, 7, 125], [92, 78, 53], [103, 65, 36], [1], []], ![[61, 129, 115, 56, 8, 55], [90, 50, 86, 64, 51, 117], [18, 100, 58], [21, 84, 62], [21, 61, 121], [23, 51, 101], [92, 47, 49]], ![[40, 104, 24, 74, 120, 7], [129, 51, 110, 4, 97, 44], [22, 69, 1], [122, 108, 27], [41, 72, 9], [91, 47, 58], [33, 10, 74]], ![[43, 89, 51, 10, 100, 79], [30, 72, 47, 104, 1, 31], [84, 58, 3], [68, 72, 46], [78, 110, 64], [32, 77, 129], [21, 17, 108]]]
 h' := ![![[28, 40, 104, 7], [36, 55, 80, 39], [36, 87, 71, 38], [56, 92, 101, 115], [111, 130, 17, 70], [76, 107, 42, 6], [0, 0, 1], [0, 1]], ![[115, 33, 89, 27], [26, 19, 57, 8], [91, 100, 81, 103], [65, 125, 99, 53], [98, 113, 8, 113], [27, 59, 60, 120], [47, 67, 129, 106], [28, 40, 104, 7]], ![[125, 57, 69, 97], [82, 46, 11, 99], [121, 75, 14, 29], [105, 122, 97, 1], [93, 92, 17, 114], [11, 86, 128, 128], [13, 91, 33, 53], [115, 33, 89, 27]], ![[0, 1], [97, 11, 114, 116], [39, 0, 96, 92], [104, 54, 96, 93], [69, 58, 89, 96], [6, 10, 32, 8], [60, 104, 99, 103], [125, 57, 69, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 118, 127], []]
 b := ![[], [], [43, 54, 85, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 4
  hpos := by decide
  P := [55, 24, 89, 125, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-80098, -568068, 916860, -1089675, 216214]
  a := ![-1, -4, 1, -5, 1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-63330, -205696, -2904, -99095, 216214]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 294499921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![254929, -746706, -2694489, -2077502, -548845]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![254929, -746706, -2694489, -2077502, -548845]] 
 ![![131, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![125, 0, 1, 0, 0], ![59, 0, 0, 1, 0], ![95, 0, 0, 0, 1]] where
  M :=![![![254929, -746706, -2694489, -2077502, -548845], ![3293070, 5793115, -4904360, -5388978, -2077502], ![6232506, 14775620, -1899906, -4904360, -2694489], ![6436932, 19478410, 6207535, 794583, -1413429], ![14713080, 48621522, 22128041, 7510710, -1899906]]]
  hmulB := by decide  
  f := ![![![1372481, 2415800, -1740791, -2421916, 1232503]], ![![739798, 1257595, -860470, -1431658, 696552]], ![![1365083, 2490314, -1884149, -2161534, 1162764]], ![![686231, 1175852, -814756, -1300587, 639068]], ![![546947, 714864, -260342, -1668368, 670711]]]
  g := ![![![4339913, -746706, -2694489, -2077502, -548845], ![5277662, 5793115, -4904360, -5388978, -2077502], ![-2548799, 14775620, -1899906, -4904360, -2694489], ![-16507395, 19478410, 6207535, 794583, -1413429], ![-51215027, 48621522, 22128041, 7510710, -1899906]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-1372481, -2415800, 1740791, 2421916, -1232503]] ![![254929, -746706, -2694489, -2077502, -548845]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![-131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0, 0, 0]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![0, 0, 0, 0, 137]] where
  M :=![![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![0, 0, 0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 5 2 7 [93, 130, 49, 107, 105, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 135, 24, 21, 120], [39, 105, 86, 57, 135], [70, 50, 78, 119, 81], [12, 120, 86, 77, 75], [0, 1]]
 g := ![![[26, 22, 134, 5, 78], [126, 76, 120, 59], [64, 68, 57, 25], [23, 102, 14, 89, 136], [115, 95, 32, 1], [], []], ![[25, 56, 88, 5, 38, 54, 89, 119], [22, 135, 18, 118], [19, 36], [121, 65, 15, 61, 102, 11, 81, 2], [55, 81, 13, 34], [39, 4, 63, 18], [102, 122, 40, 15]], ![[102, 95, 131, 39, 126, 97, 16, 7], [5, 71, 93, 122], [55, 71, 22, 50], [92, 113, 23, 37, 49, 104, 133, 101], [57, 25, 59, 16], [114, 130, 1, 19], [40, 99, 37, 4]], ![[122, 50, 119, 70, 110, 135, 8, 8], [68, 112, 14, 87], [27, 115, 93, 34], [94, 130, 12, 24, 31, 20, 58, 118], [125, 110, 88, 120], [123, 57, 65, 99], [20, 12, 29, 122]], ![[42, 23, 45, 25, 34, 59, 95, 48], [50, 110, 67, 133], [103, 35, 63, 123], [38, 53, 44, 35, 81, 15, 32, 86], [15, 1, 73, 121], [39, 45, 128, 32], [125, 109, 24, 8]]]
 h' := ![![[48, 135, 24, 21, 120], [128, 127, 75, 11, 30], [8, 112, 91, 24, 123], [53, 72, 71, 49, 5], [128, 53, 0, 22, 37], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[39, 105, 86, 57, 135], [17, 26, 127, 105, 104], [75, 18, 29, 40, 114], [91, 14, 54, 6], [75, 76, 52, 92, 4], [11, 17, 116, 45, 87], [79, 136, 61, 79, 93], [48, 135, 24, 21, 120]], ![[70, 50, 78, 119, 81], [85, 97, 81, 98, 32], [31, 39, 110, 1, 81], [25, 95, 134, 116, 18], [58, 112, 33, 32, 44], [133, 122, 124, 108, 133], [130, 85, 10, 110, 29], [39, 105, 86, 57, 135]], ![[12, 120, 86, 77, 75], [41, 9, 3, 128, 54], [101, 54, 65, 129, 19], [3, 116, 118, 38, 50], [58, 65, 19, 43, 33], [60, 10, 119, 1, 42], [26, 133, 100, 40, 28], [70, 50, 78, 119, 81]], ![[0, 1], [42, 15, 125, 69, 54], [50, 51, 116, 80, 74], [54, 114, 34, 65, 64], [5, 105, 33, 85, 19], [116, 125, 52, 120, 11], [27, 57, 102, 45, 124], [12, 120, 86, 77, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 136, 10, 100], [], [], []]
 b := ![[], [127, 16, 112, 41, 22], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 5
  hpos := by decide
  P := [93, 130, 49, 107, 105, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![195832047, 490999506, -512158608, 72082002, 70333334]
  a := ![3, -4, 7, -8, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1429431, 3583938, -3738384, 526146, 513382]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 48261724457 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀

instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2066903, -639554, 7790, -43916, 123184]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![2066903, -639554, 7790, -43916, 123184]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![129, 102, 17, 1, 0], ![62, 14, 42, 0, 1]] where
  M :=![![![2066903, -639554, 7790, -43916, 123184], ![-739104, 226933, -3352, 15580, -43916], ![131748, -41858, -437, -3352, 7790], ![346182, -106236, 444, -8227, 20282], ![10056, 538, -1862, -2464, -437]]]
  hmulB := by decide  
  f := ![![![10781, 26806, -27354, 3156, 4020]], ![![-24120, -76873, 90656, -54708, 3156]], ![![-9468, 9598, -33739, 90656, -27354]], ![![-8175, -28762, 35445, -26175, 3016]], ![![-2438, 1572, -7120, 20808, -6397]]]
  g := ![![![681, 15218, -31794, -43916, 123184], ![-188, -5377, 11340, 15580, -43916], ![584, 1374, -1947, -3352, 7790], ![1079, 3230, -5119, -8227, 20282], ![2554, 1856, 420, -2464, -437]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [131, 101, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 127, 48], [104, 11, 91], [0, 1]]
 g := ![![[126, 45, 77], [72, 86, 78], [72, 106], [117, 10, 127], [52, 54], [0, 1], []], ![[137, 1, 1, 3], [0, 82, 54, 59], [50, 99], [119, 107, 26, 48], [2, 51], [107, 121], [99, 80]], ![[119, 27, 128, 71], [67, 47, 99, 79], [53, 16], [66, 57, 7, 29], [113, 36], [3, 5], [56, 80]]]
 h' := ![![[35, 127, 48], [20, 89, 76], [138, 101, 83], [102, 79, 55], [138, 45, 31], [0, 8, 38], [0, 0, 1], [0, 1]], ![[104, 11, 91], [52, 123, 104], [114, 32, 62], [100, 84, 88], [22, 72, 138], [59, 13, 107], [71, 87, 11], [35, 127, 48]], ![[0, 1], [65, 66, 98], [76, 6, 133], [114, 115, 135], [108, 22, 109], [49, 118, 133], [5, 52, 127], [104, 11, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [109, 4], []]
 b := ![[], [17, 66, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [131, 101, 0, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29339, 78414, -78269, 23080, 6987]
  a := ![1, 0, -1, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24325, -17076, -5497, 23080, 6987]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10781, -26806, 27354, -3156, -4020]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-10781, -26806, 27354, -3156, -4020]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![97, 122, 1, 0, 0], ![120, 38, 0, 1, 0], ![92, 5, 0, 0, 1]] where
  M :=![![![-10781, -26806, 27354, -3156, -4020], ![24120, 76873, -90656, 54708, -3156], ![9468, -9598, 33739, -90656, 27354], ![-94122, -221988, 217828, 6385, -43750], ![271968, 770358, -854122, 345000, 33739]]]
  hmulB := by decide  
  f := ![![![-2066903, 639554, -7790, 43916, -123184]], ![![739104, -226933, 3352, -15580, 43916]], ![![-794609, 247430, -2491, 16996, -47474]], ![![-1584810, 490858, -5812, 33713, -94486]], ![![-1341508, 415135, -5022, 28524, -79949]]]
  g := ![![![-13781, -23194, 27354, -3156, -4020], ![18296, 65279, -90656, 54708, -3156], ![36683, -5882, 33739, -90656, 27354], ![-129242, -192956, 217828, 6385, -43750], ![277826, 659673, -854122, 345000, 33739]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P1 : CertificateIrreducibleZModOfList' 139 2 2 7 [9, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 138], [0, 1]]
 g := ![![[85, 31], [18, 36], [100], [80, 118], [107], [35], [1]], ![[0, 108], [0, 103], [100], [21, 21], [107], [35], [1]]]
 h' := ![![[69, 138], [116, 93], [3, 6], [114, 10], [0, 102], [44, 61], [130, 69], [0, 1]], ![[0, 1], [0, 46], [0, 133], [109, 129], [88, 37], [83, 78], [26, 70], [69, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [70, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N1 : CertifiedPrimeIdeal' SI139N1 139 where
  n := 2
  hpos := by decide
  P := [9, 70, 1]
  hirr := P139P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![317, 112, -128, 176, 1]
  a := ![4, 1, -1, 2, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-61, 65, -128, 176, 1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N1 B_one_repr
lemma NI139N1 : Nat.card (O ⧸ I139N1) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![2066903, -639554, 7790, -43916, 123184]] ![![-10781, -26806, 27354, -3156, -4020]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![-139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![710653289, 1834937583, 74210703, -350602952, -258483257]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![710653289, 1834937583, 74210703, -350602952, -258483257]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![44, 23, 39, 1, 0], ![144, 77, 132, 0, 1]] where
  M :=![![![710653289, 1834937583, 74210703, -350602952, -258483257], ![1550899542, 4662112847, 1435645548, 148421406, -350602952], ![1051808856, 4122794685, 2834887384, 1435645548, 74210703], ![-998081880, -944288576, 3058202652, 2760676681, 893124250], ![-4306936644, -7213948293, 7116876051, 7552050852, 2834887384]]]
  hmulB := by decide  
  f := ![![![5586835, 12169793, -11171319, -3228790, 3324157]], ![![-19944942, -55446839, 60809946, -22342638, -3228790]], ![![9686370, 44648427, -60419470, 60809946, -11171319]], ![![1398268, 7299490, -10209978, 11183841, -2225915]], ![![2449092, 19546726, -29666901, 38646696, -8758200]]]
  g := ![![![358112565, 200013532, 321258495, -350602952, -258483257], ![305417334, 189562737, 281387922, 148421406, -350602952], ![-488610312, -232290450, -422490616, 1435645548, 74210703], ![-1685085556, -894029661, -1493292543, 2760676681, 893124250], ![-4998798372, -2679177493, -4440390885, 7552050852, 2834887384]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [87, 137, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 102, 99], [39, 46, 50], [0, 1]]
 g := ![![[69, 22, 102], [78, 5], [7, 122, 31], [73, 127], [58, 32, 39], [145, 1], []], ![[74, 50, 136, 66], [84, 45], [89, 133, 136, 141], [36, 120], [119, 43, 52, 78], [123, 30], [64, 116]], ![[2, 76, 83, 2], [126, 80], [126, 127, 75, 147], [100, 16], [85, 129, 11, 34], [64, 123], [113, 116]]]
 h' := ![![[106, 102, 99], [88, 101, 129], [136, 130, 68], [9, 49, 39], [20, 114, 96], [50, 14, 28], [0, 0, 1], [0, 1]], ![[39, 46, 50], [95, 20, 139], [20, 62, 55], [73, 1, 89], [15, 130, 57], [63, 148, 141], [6, 82, 46], [106, 102, 99]], ![[0, 1], [69, 28, 30], [68, 106, 26], [117, 99, 21], [131, 54, 145], [58, 136, 129], [34, 67, 102], [39, 46, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 62], []]
 b := ![[], [100, 60, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [87, 137, 4, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-69653, -239818, 364482, -229138, 3980]
  a := ![7, 2, -25, 2, 1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![63351, 31704, 58896, -229138, 3980]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5586835, -12169793, 11171319, 3228790, -3324157]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-5586835, -12169793, 11171319, 3228790, -3324157]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![17, 110, 1, 0, 0], ![67, 127, 0, 1, 0], ![20, 100, 0, 0, 1]] where
  M :=![![![-5586835, -12169793, 11171319, 3228790, -3324157], ![19944942, 55446839, -60809946, 22342638, 3228790], ![-9686370, -44648427, 60419470, -60809946, 11171319], ![-43486428, -86141762, 72018114, 49248151, -32019368], ![182429838, 464173779, -481305885, 83226282, 60419470]]]
  hmulB := by decide  
  f := ![![![-710653289, -1834937583, -74210703, 350602952, 258483257]], ![![-1550899542, -4662112847, -1435645548, -148421406, 350602952]], ![![-1233099761, -3678853334, -1087365635, -79206376, 287827714]], ![![-1634764633, -4792515846, -1277565801, 12618809, 409072677]], ![![-1107356264, -3326819383, -1021245939, -103235788, 250973644]]]
  g := ![![![-2317752, -8850037, 11171319, 3228790, -3324157], ![-3408178, 24054677, -60809946, 22342638, 3228790], ![18886058, -570865, 60419470, -60809946, 11171319], ![-26355927, -74232971, 72018114, 49248151, -32019368], ![10604561, 246953935, -481305885, 83226282, 60419470]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P1 : CertificateIrreducibleZModOfList' 149 2 2 7 [63, 124, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 148], [0, 1]]
 g := ![![[54, 123], [30], [27, 144], [1], [34, 42], [29], [1]], ![[0, 26], [30], [51, 5], [1], [41, 107], [29], [1]]]
 h' := ![![[25, 148], [17, 47], [87, 103], [93, 137], [93, 148], [56, 108], [86, 25], [0, 1]], ![[0, 1], [0, 102], [129, 46], [91, 12], [68, 1], [74, 41], [115, 124], [25, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [141]]
 b := ![[], [50, 145]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N1 : CertifiedPrimeIdeal' SI149N1 149 where
  n := 2
  hpos := by decide
  P := [63, 124, 1]
  hirr := P149P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![212, 331, -973, 239, -112]
  a := ![1, 2, -6, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![20, 592, -973, 239, -112]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N1 B_one_repr
lemma NI149N1 : Nat.card (O ⧸ I149N1) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![710653289, 1834937583, 74210703, -350602952, -258483257]] ![![-5586835, -12169793, 11171319, 3228790, -3324157]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49519, 139744, -154609, 61350, 6517]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![49519, 139744, -154609, 61350, 6517]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![40, 43, 1, 0, 0], ![92, 59, 0, 1, 0], ![1, 44, 0, 0, 1]] where
  M :=![![![49519, 139744, -154609, 61350, 6517], ![-39102, -202845, 283308, -309218, 61350], ![-184050, -338022, 258514, 283308, -154609], ![483378, 1298222, -1394375, 413123, 110979], ![-849924, -2913704, 3551625, -2505442, 258514]]]
  hmulB := by decide  
  f := ![![![-45545, 24618, -6991, -6616, -6035]], ![![36210, 37989, -4498, -13982, -6616]], ![![-1622, 17773, -3054, -5764, -3529]], ![![-13582, 30169, -5785, -9369, -6255]], ![![10339, 11812, -680, -3684, -1889]]]
  g := ![![![3862, 19083, -154609, 61350, 6517], ![112684, 20923, 283308, -309218, 61350], ![-241287, -141500, 258514, 283308, -154609], ![120133, 211914, -1394375, 413123, 110979], ![578326, -127067, 3551625, -2505442, 258514]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [125, 145, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 150], [0, 1]]
 g := ![![[128, 29], [40, 94], [54, 2], [94], [126, 38], [36], [1]], ![[0, 122], [0, 57], [66, 149], [94], [52, 113], [36], [1]]]
 h' := ![![[6, 150], [134, 28], [45, 68], [30, 46], [105, 68], [102, 75], [26, 6], [0, 1]], ![[0, 1], [0, 123], [0, 83], [4, 105], [60, 83], [99, 76], [62, 145], [6, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [123, 110]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [125, 145, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![479, 481, -539, 1724, 237]
  a := ![3, 5, 1, 10, 1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-906, -586, -539, 1724, 237]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49939, -253453, -246364, -148328, -22258]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-49939, -253453, -246364, -148328, -22258]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![125, 19, 1, 0, 0], ![41, 4, 0, 1, 0], ![31, 59, 0, 0, 1]] where
  M :=![![![-49939, -253453, -246364, -148328, -22258], ![133548, 37567, -581158, -492728, -148328], ![444984, 888655, -457709, -581158, -246364], ![672318, 1822584, 237993, -211345, -216415], ![1743474, 5045191, 1234654, -105172, -457709]]]
  hmulB := by decide  
  f := ![![![408803, -127947, 2526, -7356, 23702]], ![![-142212, 55799, -11518, 5052, -7356]], ![![320665, -99039, 751, -5530, 18712]], ![![107653, -33445, 397, -1771, 6227]], ![![28589, -3965, -4468, 420, 2101]]]
  g := ![![![248457, 41947, -246364, -148328, -22258], ![646214, 144383, -581158, -492728, -148328], ![590221, 175134, -457709, -581158, -246364], ![-90747, 72282, 237993, -211345, -216415], ![-887995, 59684, 1234654, -105172, -457709]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [64, 145, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 150], [0, 1]]
 g := ![![[99, 59], [69, 64], [37, 19], [97], [101, 137], [36], [1]], ![[0, 92], [0, 87], [0, 132], [97], [17, 14], [36], [1]]]
 h' := ![![[6, 150], [114, 132], [48, 143], [69, 64], [29, 90], [131, 52], [87, 6], [0, 1]], ![[0, 1], [0, 19], [0, 8], [0, 87], [116, 61], [141, 99], [123, 145], [6, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [59, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [64, 145, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1016, -1646, 317, 4806, -2923]
  a := ![3, 6, -5, 10, -8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-974, 964, 317, 4806, -2923]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151675627, -46883381, 576735, -3227942, 9033273]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151675627, -46883381, 576735, -3227942, 9033273]] 
 ![![151, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![113, 0, 0, 1, 0], ![133, 0, 0, 0, 1]] where
  M :=![![![151675627, -46883381, 576735, -3227942, 9033273], ![-54199638, 16753267, -206090, 1153470, -3227942], ![9683826, -2993299, 36822, -206090, 576735], ![25369614, -7841822, 96466, -539913, 1510926], ![618270, -191109, 2351, -13158, 36822]]]
  hmulB := by decide  
  f := ![![![-473, -993, 1019, 316, 61]], ![![-87, -180, 171, 70, 13]], ![![-47, -108, 89, 16, 12]], ![![-373, -795, 785, 231, 39]], ![![-383, -794, 734, 312, 55]]]
  g := ![![![3797096, -46883381, 576735, -3227942, 9033273], ![-1356851, 16753267, -206090, 1153470, -3227942], ![242428, -2993299, 36822, -206090, 576735], ![635111, -7841822, 96466, -539913, 1510926], ![15478, -191109, 2351, -13158, 36822]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![49519, 139744, -154609, 61350, 6517]] ![![-49939, -253453, -246364, -148328, -22258]]
  ![![473, 993, -1019, -316, -61]] where
 M := ![![![473, 993, -1019, -316, -61]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![473, 993, -1019, -316, -61]] ![![151675627, -46883381, 576735, -3227942, 9033273]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)


lemma PB1189I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB1189I3 : PrimesBelowBoundCertificateInterval O 103 151 1189 where
  m := 9
  g := ![2, 2, 3, 1, 2, 1, 2, 2, 3]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB1189I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0]
    · exact ![I131N0, I131N1]
    · exact ![I137N0]
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
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
    · exact ![1225043, 11449]
    · exact ![1295029, 11881]
    · exact ![12769, 12769, 113]
    · exact ![33038369407]
    · exact ![294499921, 131]
    · exact ![48261724457]
    · exact ![2685619, 19321]
    · exact ![3307949, 22201]
    · exact ![22801, 22801, 151]
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
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
  β := ![I113N2, I131N1, I151N2]
  Il := ![[], [], [I113N2], [], [I131N1], [], [], [], [I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
