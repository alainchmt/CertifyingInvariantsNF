
import IdealArithmetic.Examples.NF5_3_1125000000_3.RI5_3_1125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38, 232, 223, -259, -412]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![38, 232, 223, -259, -412]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![30, 6, 94, 1, 0], ![60, 18, 71, 0, 1]] where
  M :=![![![38, 232, 223, -259, -412], ![-522, -295, 444, -1138, -1248], ![-4384, -4102, 1761, -6932, -6608], ![-2333, -2486, 571, -3196, -2794], ![-3235, -3280, 993, -4705, -4273]]]
  hmulB := by decide  
  f := ![![![386, -132, -117, 31, 162]], ![![-254, 87, 68, -46, -76]], ![![72, -174, 119, 116, -216]], ![![157, -184, 75, 108, -148]], ![![221, -176, 26, 87, -67]]]
  g := ![![![304, 86, 503, -259, -412], ![1014, 271, 1832, -1138, -1248], ![5608, 1462, 10491, -6932, -6608], ![2441, 626, 4667, -3196, -2794], ![3685, 952, 6978, -4705, -4273]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [16, 39, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 79, 92], [80, 27, 15], [0, 1]]
 g := ![![[77, 84, 75], [37, 74, 101], [91, 29], [60, 28, 9], [86, 90], [1]], ![[28, 18, 77, 61], [66, 23, 15, 92], [59, 27], [0, 19, 70, 49], [78, 41], [11, 84, 87, 49]], ![[60, 69, 78, 88], [16, 60, 12, 91], [72, 4], [36, 75, 1, 20], [89, 1], [101, 9, 94, 58]]]
 h' := ![![[52, 79, 92], [50, 81, 90], [51, 37, 84], [3, 33, 52], [57, 92, 3], [91, 68, 25], [0, 1]], ![[80, 27, 15], [66, 27, 38], [106, 36, 1], [27, 81, 53], [93, 15, 92], [48, 71, 83], [52, 79, 92]], ![[0, 1], [36, 106, 86], [3, 34, 22], [37, 100, 2], [3, 0, 12], [101, 75, 106], [80, 27, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 102], []]
 b := ![[], [54, 97, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [16, 39, 82, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6280102350, -6306087568, 2359975442, -8851387064, -8896297554]
  a := ![-176, -194, 145, -109, -324]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7411582830, 1933977484, 13701191456, -8851387064, -8896297554]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-578, -220, 31, -1267, 900]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-578, -220, 31, -1267, 900]] 
 ![![107, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![-578, -220, 31, -1267, 900], ![-3082, -4591, 6648, 5038, -11936], ![36168, 38374, -48615, -5636, 64176], ![-13917, -11750, 12987, -8236, -9930], ![26533, 25548, -30727, 4847, 34335]]]
  hmulB := by decide  
  f := ![![![-8390, -24936, -15381, 10255, 23266]], ![![-1142, -3459, -2194, 1548, 3376]], ![![-1012, -3990, -2945, 2614, 4900]], ![![-3189, -10026, -6436, 4627, 9966]], ![![-5321, -16568, -10572, 7520, 16315]]]
  g := ![![![-63, -220, 31, -1267, 900], ![5478, -4591, 6648, 5038, -11936], ![-37918, 38374, -48615, -5636, 64176], ![9461, -11750, 12987, -8236, -9930], ![-23389, 25548, -30727, 4847, 34335]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4657, 1716, 1384, -338, -1966]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![-4657, 1716, 1384, -338, -1966]] 
 ![![107, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![59, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![100, 0, 0, 0, 1]] where
  M :=![![![-4657, 1716, 1384, -338, -1966], ![3020, -1055, -864, 204, 1228], ![-1912, 744, 585, -136, -824], ![1180, -448, -362, 97, 518], ![-526, 188, 148, -26, -205]]]
  hmulB := by decide  
  f := ![![![-1383, -1404, 1740, -2, -2146]], ![![-395, -411, 516, 34, -662]], ![![-863, -804, 949, -250, -986]], ![![-202, -224, 290, 65, -406]], ![![-1270, -1244, 1512, -158, -1749]]]
  g := ![![![501, 1716, 1384, -338, -1966], ![-317, -1055, -864, 204, 1228], ![199, 744, 585, -136, -824], ![-136, -448, -362, 97, 518], ![46, 188, 148, -26, -205]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![38, 232, 223, -259, -412]] ![![-578, -220, 31, -1267, 900]]
  ![![1383, 1404, -1740, 2, 2146]] where
 M := ![![![1383, 1404, -1740, 2, 2146]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![1383, 1404, -1740, 2, 2146]] ![![-4657, 1716, 1384, -338, -1966]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![-107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![317, -113, -93, 22, 132]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![317, -113, -93, 22, 132]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![4, 59, 1, 0, 0], ![108, 74, 0, 1, 0], ![102, 106, 0, 0, 1]] where
  M :=![![![317, -113, -93, 22, 132], ![-206, 72, 63, -16, -88], ![138, -43, -40, 20, 48], ![-78, 32, 18, -9, -24], ![36, -15, -7, 10, 5]]]
  hmulB := by decide  
  f := ![![![-3, 7, 13, -22, -28]], ![![-66, -54, 39, -112, -120]], ![![-40, -33, 23, -68, -72]], ![![-50, -32, 40, -101, -112]], ![![-70, -49, 51, -134, -147]]]
  g := ![![![-139, -94, -93, 22, 132], ![94, 63, 63, -16, -88], ![-62, -39, -40, 20, 48], ![30, 20, 18, -9, -24], ![-14, -8, -7, 10, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [63, 107, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 108], [0, 1]]
 g := ![![[19, 45], [106], [59, 82], [38, 28], [102], [2, 1]], ![[0, 64], [106], [5, 27], [94, 81], [102], [4, 108]]]
 h' := ![![[2, 108], [92, 63], [98, 91], [4, 55], [76, 30], [92, 50], [0, 1]], ![[0, 1], [0, 46], [62, 18], [5, 54], [27, 79], [83, 59], [2, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [29, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [63, 107, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![153401821, 148211544, -22742186, 274253518, 186576326]
  a := ![-2547, -2778, 1994, -1752, -4457]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-444089859, -353961930, -22742186, 274253518, 186576326]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20365, -22577, 29213, 6520, -40884]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-20365, -22577, 29213, 6520, -40884]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![39, 66, 1, 0, 0], ![4, 4, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![-20365, -22577, 29213, 6520, -40884], ![119590, 110896, -130425, 36524, 133928], ![-368598, -252511, 232656, -420628, 24336], ![-59472, -106876, 162960, 160297, -319836], ![-96634, -9111, -47273, -307232, 285861]]]
  hmulB := by decide  
  f := ![![![-18929, -38841, -19173, 6880, 24820]], ![![-37878, -62454, -16721, -17756, 5400]], ![![-31181, -53430, -16807, -10060, 10748]], ![![-2588, -4056, -952, -1415, 28]], ![![-10232, -20029, -9141, 2040, 10981]]]
  g := ![![![9376, -18135, 29213, 6520, -40884], ![-19927, 78650, -130425, 36524, 133928], ![-83246, -127755, 232656, -420628, 24336], ![93716, -105536, 162960, 160297, -319836], ![-114317, 39815, -47273, -307232, 285861]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [108, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 108], [0, 1]]
 g := ![![[74, 108], [64], [108, 83], [33, 45], [75], [74, 1]], ![[0, 1], [64], [37, 26], [93, 64], [75], [39, 108]]]
 h' := ![![[74, 108], [65, 33], [108, 8], [33, 44], [101, 63], [74, 27], [0, 1]], ![[0, 1], [0, 76], [46, 101], [19, 65], [76, 46], [1, 82], [74, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [17, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where
  n := 2
  hpos := by decide
  P := [108, 35, 1]
  hirr := P109P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![457103, 443291, -70842, 811479, 564904]
  a := ![-139, -151, 107, -99, -239]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-280099, 17183, -70842, 811479, 564904]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-58, -32, 43, -33, -30]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-58, -32, 43, -33, -30]] 
 ![![109, 0, 0, 0, 0], ![93, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![-58, -32, 43, -33, -30], ![66, -5, 40, 210, -204], ![672, 902, -1253, -732, 2088], ![-521, -518, 629, -54, -736], ![723, 808, -1047, -247, 1475]]]
  hmulB := by decide  
  f := ![![![-3346, -5612, -1671, -1245, 900]], ![![-2976, -4933, -1415, -1203, 660]], ![![-2894, -4394, -886, -1827, -324]], ![![-661, -870, -40, -635, -394]], ![![-1585, -2324, -385, -1135, -375]]]
  g := ![![![12, -32, 43, -33, -30], ![25, -5, 40, 210, -204], ![-563, 902, -1253, -732, 2088], ![276, -518, 629, -54, -736], ![-463, 808, -1047, -247, 1475]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![317, -113, -93, 22, 132]] ![![-20365, -22577, 29213, 6520, -40884]]
  ![![246167, 241442, -293378, 29942, 339920]] where
 M := ![![![246167, 241442, -293378, 29942, 339920]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![246167, 241442, -293378, 29942, 339920]] ![![-58, -32, 43, -33, -30]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![34669848, -14566106, 50782773, 171754897, -189867754]]]
 hmul := by decide  
 g := ![![![![318072, -133634, 465897, 1575733, -1741906]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, -16, -18, 4, 24]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![53, -16, -18, 4, 24]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![108, 26, 11, 1, 0], ![36, 108, 101, 0, 1]] where
  M :=![![![53, -16, -18, 4, 24], ![-44, 3, 16, -16, -16], ![0, -44, 35, 32, -96], ![4, 24, -28, -19, 32], ![-28, -44, 46, 12, -87]]]
  hmulB := by decide  
  f := ![![![-35, -88, -50, 28, 72]], ![![-44, -101, -56, 32, 80]], ![![-48, -116, -69, 32, 96]], ![![-48, -118, -67, 37, 96]], ![![-96, -228, -131, 68, 185]]]
  g := ![![![-11, -24, -22, 4, 24], ![20, 19, 16, -16, -16], ![0, 84, 83, 32, -96], ![8, -26, -27, -19, 32], ![16, 80, 77, 12, -87]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [62, 85, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 20, 49], [96, 92, 64], [0, 1]]
 g := ![![[20, 41, 57], [62, 97], [62, 105], [109, 16], [109, 88, 83], [1]], ![[98, 87, 28, 52], [65, 102], [14, 26], [82, 53], [99, 106, 93, 77], [76, 18, 100, 16]], ![[17, 50, 5, 4], [102, 52], [95, 51], [17, 7], [105, 39, 79, 25], [38, 57, 42, 97]]]
 h' := ![![[3, 20, 49], [9, 19, 31], [89, 7, 53], [54, 106, 52], [22, 84, 4], [51, 28, 99], [0, 1]], ![[96, 92, 64], [20, 56, 54], [35, 49, 21], [98, 82, 34], [53, 89, 77], [61, 83, 84], [3, 20, 49]], ![[0, 1], [86, 38, 28], [67, 57, 39], [104, 38, 27], [49, 53, 32], [76, 2, 43], [96, 92, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 27], []]
 b := ![[], [18, 77, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [62, 85, 14, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1279823664605, 1282957366681, -474646765238, 1814773411939, 1802190597162]
  a := ![1030, 1133, -838, 655, 1873]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2297297047103, -2128652529533, -1791667297433, 1814773411939, 1802190597162]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, -88, -50, 28, 72]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-35, -88, -50, 28, 72]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![29, 94, 1, 0, 0], ![37, 1, 0, 1, 0], ![101, 26, 0, 0, 1]] where
  M :=![![![-35, -88, -50, 28, 72], ![-44, -101, -56, 32, 80], ![-48, -116, -69, 32, 96], ![28, 72, 44, -27, -64], ![12, 28, 14, -12, -23]]]
  hmulB := by decide  
  f := ![![![53, -16, -18, 4, 24]], ![![-44, 3, 16, -16, -16]], ![![-23, -2, 9, -12, -8]], ![![17, -5, -6, 1, 8]], ![![37, -14, -12, 0, 17]]]
  g := ![![![-61, 24, -50, 28, 72], ![-68, 27, -56, 32, 80], ![-79, 34, -69, 32, 96], ![55, -21, 44, -27, -64], ![21, -6, 14, -12, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [3, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 112], [0, 1]]
 g := ![![[104, 41], [22], [62], [111], [79, 44], [27, 1]], ![[81, 72], [22], [62], [111], [24, 69], [54, 112]]]
 h' := ![![[27, 112], [34, 70], [10, 19], [14, 66], [102, 87], [32, 48], [0, 1]], ![[0, 1], [3, 43], [71, 94], [101, 47], [78, 26], [85, 65], [27, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110]]
 b := ![[], [105, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [3, 86, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1260160, 1116648, 9221, 2609102, 1038539]
  a := ![-241, -275, 228, -100, -509]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1773774, -259834, 9221, 2609102, 1038539]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![53, -16, -18, 4, 24]] ![![-35, -88, -50, 28, 72]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 5 2 6 [62, 97, 124, 83, 80, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 83, 0, 46, 21], [24, 85, 100, 20, 8], [118, 124, 72, 67, 26], [26, 88, 82, 121, 72], [0, 1]]
 g := ![![[4, 48, 92, 123, 100], [32, 58, 47, 74, 34], [21, 12, 99, 4, 64], [10, 43, 110, 27, 17], [94, 47, 1], []], ![[12, 70, 72, 104, 50, 32, 6, 26], [76, 13, 62, 126, 57, 120, 23, 82], [119, 79, 62, 52, 5, 56, 78, 98], [97, 103, 64, 91, 10, 108, 39, 47], [107, 117, 104, 59, 17, 5, 24, 60], [4, 47, 76, 17, 10, 66, 63, 117]], ![[126, 60, 48, 65, 59, 24, 8, 79], [92, 52, 48, 27, 9, 81, 122, 52], [89, 20, 18, 66, 37, 22, 81, 8], [108, 83, 29, 113, 19, 75, 97, 2], [98, 81, 71, 11, 5, 62, 107, 41], [7, 97, 113, 14, 32, 106, 91, 4]], ![[31, 56, 105, 25, 78, 43, 18, 38], [73, 32, 111, 112, 43, 102, 36, 69], [40, 8, 25, 61, 25, 7, 22, 11], [9, 47, 87, 37, 121, 40, 48, 9], [98, 123, 2, 35, 116, 63, 73, 38], [117, 46, 30, 65, 94, 74, 50, 50]], ![[98, 89, 0, 96, 63, 87, 90, 107], [97, 65, 89, 10, 50, 8, 78, 52], [61, 51, 40, 63, 38, 77, 126, 64], [80, 118, 2, 85, 107, 102, 41, 82], [52, 97, 89, 49, 122, 14, 117, 115], [60, 105, 108, 76, 88, 24, 52, 122]]]
 h' := ![![[6, 83, 0, 46, 21], [48, 39, 73, 95, 10], [95, 111, 51, 0, 65], [15, 116, 123, 29, 119], [14, 33, 106, 116, 12], [0, 0, 0, 1], [0, 1]], ![[24, 85, 100, 20, 8], [1, 99, 113, 49, 112], [77, 110, 24, 99, 123], [121, 18, 92, 87, 38], [18, 81, 58, 123, 37], [95, 74, 62, 67, 104], [6, 83, 0, 46, 21]], ![[118, 124, 72, 67, 26], [50, 95, 14, 2, 11], [118, 7, 14, 102, 109], [16, 52, 17, 20, 1], [103, 86, 74, 32, 63], [55, 106, 77, 16, 23], [24, 85, 100, 20, 8]], ![[26, 88, 82, 121, 72], [100, 87, 92, 0, 104], [11, 86, 11, 94, 78], [40, 27, 106, 97, 22], [25, 74, 101, 43, 53], [18, 56, 106, 102, 104], [118, 124, 72, 67, 26]], ![[0, 1], [124, 61, 89, 108, 17], [18, 67, 27, 86, 6], [24, 41, 43, 21, 74], [27, 107, 42, 67, 89], [13, 18, 9, 68, 23], [26, 88, 82, 121, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92, 80, 53, 41], [], [], []]
 b := ![[], [2, 114, 76, 10, 119], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 5
  hpos := by decide
  P := [62, 97, 124, 83, 80, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![915823078063160, 1519318670845278, 6524934799620176, 11959998839285952, 3493924885869552]
  a := ![98, 126, -136, -32, 304]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7211205339080, 11963139140514, 51377439367088, 94173219206976, 27511219573776]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5895, 2133, 1729, -416, -2456]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-5895, 2133, 1729, -416, -2456]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![19, 38, 95, 1, 0], ![45, 107, 67, 0, 1]] where
  M :=![![![-5895, 2133, 1729, -416, -2456], ![3798, -1370, -1115, 268, 1584], ![-2450, 879, 726, -172, -1024], ![1500, -540, -440, 111, 624], ![-670, 239, 199, -48, -277]]]
  hmulB := by decide  
  f := ![![![11, 27, 17, -8, -24]], ![![22, 40, 11, -4, -16]], ![![18, 45, 24, -4, 0]], ![![21, 48, 23, -5, -8]], ![![31, 65, 27, -8, -21]]]
  g := ![![![859, 2143, 1571, -416, -2456], ![-554, -1382, -1013, 268, 1584], ![358, 893, 654, -172, -1024], ![-219, -546, -403, 111, 624], ![97, 242, 178, -48, -277]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [1, 113, 87, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 50, 106], [93, 80, 25], [0, 1]]
 g := ![![[49, 66, 65], [85, 56, 36], [85, 53], [13, 45], [105, 121], [44, 1], []], ![[104, 87, 93, 70], [24, 22, 36, 96], [11, 64], [85, 44], [122, 15], [111, 112], [110, 101]], ![[87, 26, 91, 99], [130, 112, 113, 59], [85, 58], [78, 3], [67, 107], [105, 11], [60, 101]]]
 h' := ![![[82, 50, 106], [46, 78, 14], [62, 91, 6], [127, 75, 61], [128, 19, 62], [87, 5, 120], [0, 0, 1], [0, 1]], ![[93, 80, 25], [2, 120, 87], [48, 48, 39], [94, 118, 123], [21, 61, 31], [55, 76, 43], [64, 123, 80], [82, 50, 106]], ![[0, 1], [83, 64, 30], [61, 123, 86], [88, 69, 78], [64, 51, 38], [0, 50, 99], [74, 8, 50], [93, 80, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 102], []]
 b := ![[], [11, 58, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [1, 113, 87, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![59936440821, 60286079610, -22524571560, 84430325493, 85384788085]
  a := ![374, 413, -313, 219, 701]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-41118742041, -93772813849, -105070124390, 84430325493, 85384788085]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -27, -17, 8, 24]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-11, -27, -17, 8, 24]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![128, 39, 1, 0, 0], ![43, 59, 0, 1, 0], ![125, 116, 0, 0, 1]] where
  M :=![![![-11, -27, -17, 8, 24], ![-22, -40, -11, 4, 16], ![-18, -45, -24, 4, 0], ![4, 20, 8, -29, -16], ![-6, -5, 13, -8, -41]]]
  hmulB := by decide  
  f := ![![![5895, -2133, -1729, 416, 2456]], ![![-3798, 1370, 1115, -268, -1584]], ![![4648, -1683, -1363, 328, 1936]], ![![213, -79, -62, 15, 88]], ![![2267, -824, -664, 160, 943]]]
  g := ![![![-9, -20, -17, 8, 24], ![-6, -13, -11, 4, 16], ![22, 5, -24, 4, 0], ![17, 25, 8, -29, -16], ![29, 36, 13, -8, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [122, 124, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 130], [0, 1]]
 g := ![![[59, 46], [110, 117], [100], [61], [12], [49], [1]], ![[119, 85], [12, 14], [100], [61], [12], [49], [1]]]
 h' := ![![[7, 130], [73, 96], [32, 36], [124, 10], [112, 42], [129, 76], [9, 7], [0, 1]], ![[0, 1], [90, 35], [22, 95], [63, 121], [13, 89], [6, 55], [58, 124], [7, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114]]
 b := ![[], [128, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [122, 124, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![234997, 230294, -41404, 408486, 303931]
  a := ![-100, -107, 72, -79, -161]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-381844, -439020, -41404, 408486, 303931]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-5895, 2133, 1729, -416, -2456]] ![![-11, -27, -17, 8, 24]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2640, 1293, 742, 215, -806]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-2640, 1293, 742, 215, -806]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![109, 38, 132, 22, 1]] where
  M :=![![![-2640, 1293, 742, 215, -806], ![3700, 1124, -1179, 2886, 3332], ![11134, 12681, -3756, 18280, 16424], ![6731, 5710, -2179, 8930, 8464], ![8301, 8707, -2750, 12785, 11647]]]
  hmulB := by decide  
  f := ![![![-8, -15, 22, 23, -44]], ![![136, 150, -195, -42, 272]], ![![-794, -735, 862, -248, -880]], ![![149, 82, -55, 240, -110]], ![![-713, -668, 788, -196, -827]]]
  g := ![![![622, 233, 782, 131, -806], ![-2624, -916, -3219, -514, 3332], ![-12986, -4463, -15852, -2504, 16424], ![-6685, -2306, -8171, -1294, 8464], ![-9206, -3167, -11242, -1777, 11647]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 4 2 7 [31, 4, 29, 40, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 88, 125, 88], [57, 62, 70, 39], [97, 123, 79, 10], [0, 1]]
 g := ![![[130, 39, 98, 126], [51, 66, 8], [100, 32, 65], [63, 70, 118, 123], [75, 107, 93], [1], []], ![[79, 17, 52, 61, 68, 56], [102, 56, 56], [57, 120, 38], [57, 81, 112, 1, 15, 123], [72, 11, 109], [2, 93, 2], [52, 77, 72]], ![[4, 87, 29, 87, 54, 130], [64, 30, 103], [101, 19, 50], [94, 119, 121, 68, 89, 44], [101, 132, 32], [26, 18, 34], [61, 105, 14]], ![[99, 118, 42, 2, 93, 67], [26, 47, 115], [61, 106, 100], [3, 28, 107, 91, 65, 48], [10, 79, 18], [118, 81, 87], [125, 46, 100]]]
 h' := ![![[80, 88, 125, 88], [131, 60, 12, 20], [43, 132, 23, 62], [102, 80, 113, 105], [6, 56, 27, 73], [106, 133, 108, 97], [0, 0, 1], [0, 1]], ![[57, 62, 70, 39], [53, 7, 85, 77], [129, 131, 92, 78], [65, 24, 105, 60], [129, 131, 124, 14], [124, 34, 107, 71], [130, 114, 132, 106], [80, 88, 125, 88]], ![[97, 123, 79, 10], [15, 89, 47, 7], [9, 48, 40, 69], [20, 50, 1, 119], [1, 68, 126, 69], [23, 129, 107, 13], [125, 7, 22, 50], [57, 62, 70, 39]], ![[0, 1], [18, 118, 130, 33], [31, 100, 119, 65], [135, 120, 55, 127], [62, 19, 134, 118], [80, 115, 89, 93], [54, 16, 119, 118], [97, 123, 79, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [37, 114, 97], []]
 b := ![[], [], [52, 48, 84, 131], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 4
  hpos := by decide
  P := [31, 4, 29, 40, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![506072084279757, 500243666351488, -160348861626590, 764156044161076, 676742143437994]
  a := ![325, 365, -289, 164, 647]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-534735923725997, -184058086016732, -653213954711254, -103096139499816, 676742143437994]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 352275361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 15, -22, -23, 44]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![8, 15, -22, -23, 44]] 
 ![![137, 0, 0, 0, 0], ![100, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![8, 15, -22, -23, 44], ![-136, -150, 195, 42, -272], ![794, 735, -862, 248, 880], ![-149, -82, 55, -240, 110], ![447, 365, -394, 307, 259]]]
  hmulB := by decide  
  f := ![![![2640, -1293, -742, -215, 806]], ![![1900, -952, -533, -178, 564]], ![![-62, -102, 22, -135, -114]], ![![317, -221, -87, -95, 50]], ![![267, -224, -72, -120, 15]]]
  g := ![![![-13, 15, -22, -23, 44], ![135, -150, 195, 42, -272], ![-668, 735, -862, 248, 880], ![78, -82, 55, -240, 110], ![-335, 365, -394, 307, 259]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-2640, 1293, 742, 215, -806]] ![![8, 15, -22, -23, 44]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1218, 529, 316, -31, -506]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-1218, 529, 316, -31, -506]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![9, 119, 23, 80, 1]] where
  M :=![![![-1218, 529, 316, -31, -506], ![760, -268, -359, -318, 764], ![-1898, -1543, 2532, 1168, -4072], ![1269, 794, -1205, 160, 1392], ![-1513, -1441, 1956, 343, -2701]]]
  hmulB := by decide  
  f := ![![![3810, 9087, 5156, -2925, -7424]], ![![4388, 10466, 5939, -3370, -8552]], ![![5050, 12051, 6842, -3888, -9856]], ![![-3251, -7750, -4395, 2490, 6326]], ![![2959, 7061, 4009, -2278, -5775]]]
  g := ![![![24, 437, 86, 291, -506], ![-44, -656, -129, -442, 764], ![250, 3475, 692, 2352, -4072], ![-81, -1186, -239, -800, 1392], ![164, 2302, 461, 1557, -2701]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 4 2 7 [20, 24, 100, 93, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 77, 107, 59], [105, 79, 62, 62], [53, 121, 109, 18], [0, 1]]
 g := ![![[89, 134, 56, 6], [128, 135, 81, 16], [94, 79, 81], [128, 89, 26, 54], [9, 10, 31], [1], []], ![[19, 62, 7, 121, 63, 135], [135, 34, 0, 88, 6, 40], [10, 32, 83], [85, 134, 42, 110, 25, 82], [95, 76, 112], [7, 21, 25], [20, 114, 6]], ![[0, 28, 138, 42, 113, 48], [135, 80, 42, 75, 137, 32], [126, 32, 117], [41, 111, 111, 38, 0, 59], [81, 57, 9], [123, 108, 52], [26, 59, 91]], ![[12, 29, 14, 138, 16, 3], [11, 104, 33, 46, 102, 3], [70, 57, 36], [2, 86, 33, 120, 107, 90], [12, 14, 41], [1, 79, 63], [79, 63, 46]]]
 h' := ![![[27, 77, 107, 59], [81, 6, 16, 80], [94, 26, 5, 4], [81, 41, 114, 9], [81, 127, 36, 101], [119, 115, 39, 46], [0, 0, 1], [0, 1]], ![[105, 79, 62, 62], [38, 68, 117, 29], [20, 56, 109, 114], [130, 87, 85, 120], [59, 22, 136, 64], [98, 89, 77, 23], [51, 8, 40, 5], [27, 77, 107, 59]], ![[53, 121, 109, 18], [123, 44, 127, 63], [17, 13, 126, 127], [70, 63, 50, 16], [128, 57, 51, 125], [48, 11, 10, 3], [80, 52, 81, 82], [105, 79, 62, 62]], ![[0, 1], [133, 21, 18, 106], [18, 44, 38, 33], [58, 87, 29, 133], [23, 72, 55, 127], [47, 63, 13, 67], [117, 79, 17, 52], [53, 121, 109, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [122, 50, 64], []]
 b := ![[], [], [84, 112, 106, 129], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 4
  hpos := by decide
  P := [20, 24, 100, 93, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![63551655581836, 62759748834594, -20110816059696, 96027945021126, 84698599413150]
  a := ![194, 219, -176, 93, 393]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5026875821126, -72060241592304, -14159558291814, -48056546820366, 84698599413150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 373301041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3810, -9087, -5156, 2925, 7424]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-3810, -9087, -5156, 2925, 7424]] 
 ![![139, 0, 0, 0, 0], ![57, 1, 0, 0, 0], ![87, 0, 1, 0, 0], ![50, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![-3810, -9087, -5156, 2925, 7424], ![-4388, -10466, -5939, 3370, 8552], ![-5050, -12051, -6842, 3888, 9856], ![3251, 7750, 4395, -2490, -6326], ![1231, 2931, 1660, -937, -2387]]]
  hmulB := by decide  
  f := ![![![1218, -529, -316, 31, 506]], ![![494, -215, -127, 15, 202]], ![![776, -320, -216, 11, 346]], ![![429, -196, -105, 10, 172]], ![![265, -100, -80, 4, 125]]]
  g := ![![![4325, -9087, -5156, 2925, 7424], ![4981, -10466, -5939, 3370, 8552], ![5733, -12051, -6842, 3888, 9856], ![-3690, 7750, 4395, -2490, -6326], ![-1397, 2931, 1660, -937, -2387]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-1218, 529, 316, -31, -506]] ![![-3810, -9087, -5156, 2925, 7424]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![141, 153, -27, 180, 152]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![141, 153, -27, 180, 152]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![33, 20, 67, 1, 0], ![4, 43, 143, 0, 1]] where
  M :=![![![141, 153, -27, 180, 152], ![862, 878, -263, 1252, 1136], ![5702, 5691, -1858, 8436, 7744], ![2744, 2716, -924, 4099, 3784], ![3966, 3939, -1317, 5900, 5435]]]
  hmulB := by decide  
  f := ![![![41, -23, -5, 4, 8]], ![![2, 40, -23, 12, 16]], ![![-58, -49, 24, -124, 64]], ![![-17, -22, 7, -53, 32]], ![![-54, -36, 16, -116, 67]]]
  g := ![![![-43, -67, -227, 180, 152], ![-302, -490, -1655, 1252, 1136], ![-2038, -3329, -11238, 8436, 7744], ![-991, -1624, -5481, 4099, 3784], ![-1426, -2334, -7878, 5900, 5435]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [143, 95, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [137, 91, 11], [90, 57, 138], [0, 1]]
 g := ![![[147, 57, 39], [58, 29], [141, 9, 39], [75, 145], [109, 24, 96], [78, 1], []], ![[99, 146, 142, 101], [82, 73], [76, 64, 106, 105], [78, 86], [27, 87, 136, 62], [133, 120], [116, 121]], ![[136, 64, 135, 41], [108, 24], [52, 31, 118, 34], [142, 9], [59, 23, 87, 137], [90, 86], [138, 121]]]
 h' := ![![[137, 91, 11], [119, 40, 121], [101, 93, 25], [89, 126, 121], [58, 64, 88], [21, 46, 29], [0, 0, 1], [0, 1]], ![[90, 57, 138], [108, 43, 36], [19, 26, 64], [89, 121, 88], [51, 79, 58], [138, 73, 73], [95, 38, 57], [137, 91, 11]], ![[0, 1], [32, 66, 141], [125, 30, 60], [143, 51, 89], [143, 6, 3], [88, 30, 47], [137, 111, 91], [90, 57, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103, 22], []]
 b := ![[], [85, 14, 147], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [143, 95, 71, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3956044874, 3978944106, -1485223446, 5575182296, 5634755232]
  a := ![151, 167, -127, 88, 284]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1359489878, -2347779710, -7924781446, 5575182296, 5634755232]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 145, 85, -50, -120]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![59, 145, 85, -50, -120]] 
 ![![149, 0, 0, 0, 0], ![106, 1, 0, 0, 0], ![88, 0, 1, 0, 0], ![73, 0, 0, 1, 0], ![49, 0, 0, 0, 1]] where
  M :=![![![59, 145, 85, -50, -120], ![70, 164, 105, -40, -160], ![150, 275, 4, -100, 0], ![-90, -160, -30, 29, 60], ![40, 15, -105, 10, 139]]]
  hmulB := by decide  
  f := ![![![32611, -11655, -9565, 2450, 13680]], ![![23064, -8236, -6765, 1740, 9680]], ![![19382, -6885, -5686, 1500, 8160]], ![![15937, -5675, -4675, 1219, 6700]], ![![10771, -3820, -3160, 840, 4539]]]
  g := ![![![-89, 145, 85, -50, -120], ![-106, 164, 105, -40, -160], ![-148, 275, 4, -100, 0], ![97, -160, -30, 29, 60], ![1, 15, -105, 10, 139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 5, -1, 28, -20]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![13, 5, -1, 28, -20]] 
 ![![149, 0, 0, 0, 0], ![133, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![88, 0, 0, 1, 0], ![109, 0, 0, 0, 1]] where
  M :=![![![13, 5, -1, 28, -20], ![66, 100, -147, -116, 264], ![-818, -869, 1092, 116, -1456], ![308, 260, -292, 175, 220], ![-602, -581, 693, -116, -785]]]
  hmulB := by decide  
  f := ![![![-11687, 21669, 13881, -6148, -19884]], ![![-10305, 19431, 12434, -5520, -17812]], ![![-3288, 6261, 4004, -1780, -5736]], ![![-6908, 12700, 8140, -3601, -11660]], ![![-8577, 15824, 10140, -4488, -14525]]]
  g := ![![![-6, 5, -1, 28, -20], ![-172, 100, -147, -116, 264], ![1459, -869, 1092, 116, -1456], ![-412, 260, -292, 175, 220], ![962, -581, 693, -116, -785]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![141, 153, -27, 180, 152]] ![![59, 145, 85, -50, -120]]
  ![![4859, 11592, 6582, -3730, -9472]] where
 M := ![![![4859, 11592, 6582, -3730, -9472]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![4859, 11592, 6582, -3730, -9472]] ![![13, 5, -1, 28, -20]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![-2533, -2831, 3725, 894, -5364]]]
 hmul := by decide  
 g := ![![![![-17, -19, 25, 6, -36]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![40, 233, 128, -67, -188]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![40, 233, 128, -67, -188]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![3, 59, 70, 112, 1]] where
  M :=![![![40, 233, 128, -67, -188], ![124, 224, 125, -102, -160], ![22, 181, 312, 16, -496], ![7, -114, -189, 60, 254], ![-121, -165, 96, 63, -141]]]
  hmulB := by decide  
  f := ![![![0, 3, 0, 3, 2]], ![![16, 14, -5, 22, 20]], ![![98, 99, -34, 144, 136]], ![![47, 46, -15, 70, 64]], ![![87, 86, -29, 128, 119]]]
  g := ![![![4, 75, 88, 139, -188], ![4, 64, 75, 118, -160], ![10, 195, 232, 368, -496], ![-5, -100, -119, -188, 254], ![2, 54, 66, 105, -141]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 4 2 7 [111, 95, 36, 136, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 148, 117, 7], [104, 41, 124, 92], [111, 112, 61, 52], [0, 1]]
 g := ![![[146, 121, 59, 36], [31, 55, 144, 125], [104, 113, 37, 59], [149, 63, 17], [35, 7, 30, 74], [1], []], ![[118, 51, 102, 20, 85, 71], [6, 102, 120, 98, 144, 147], [14, 45, 86, 142, 52, 147], [111, 104, 21], [96, 141, 57, 28, 128, 96], [74, 26, 69], [64, 108, 49]], ![[30, 109, 60, 4, 46, 102], [72, 97, 98, 96, 112, 120], [65, 48, 128, 74, 82, 77], [56, 132, 10], [103, 10, 92, 89, 73, 112], [31, 21, 32], [44, 135, 8]], ![[2, 7, 92, 92, 25, 141], [115, 10, 22, 119, 82, 26], [108, 89, 6, 54, 141, 30], [8, 98, 47], [69, 78, 103, 104, 25, 106], [84, 7, 86], [69, 94, 137]]]
 h' := ![![[102, 148, 117, 7], [32, 104, 48, 6], [83, 52, 77, 27], [91, 37, 70, 132], [41, 65, 131, 35], [40, 56, 115, 15], [0, 0, 1], [0, 1]], ![[104, 41, 124, 92], [39, 25, 93, 119], [76, 1, 113, 126], [111, 8, 52, 126], [79, 72, 29, 25], [122, 77, 71, 10], [129, 44, 136, 89], [102, 148, 117, 7]], ![[111, 112, 61, 52], [9, 95, 29, 56], [40, 8, 57, 126], [17, 21, 130, 31], [58, 132, 12, 37], [69, 136, 42, 82], [43, 84, 96, 33], [104, 41, 124, 92]], ![[0, 1], [105, 78, 132, 121], [138, 90, 55, 23], [90, 85, 50, 13], [125, 33, 130, 54], [97, 33, 74, 44], [132, 23, 69, 29], [111, 112, 61, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [96, 36, 141], []]
 b := ![[], [], [50, 116, 122, 115], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 4
  hpos := by decide
  P := [111, 95, 36, 136, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![636415152458911, 632757834295395, -207358708173151, 950296035283792, 868904623024158]
  a := ![-333, -359, 248, -250, -557]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13048335871613, -335315330623377, -404176704105061, -638192196976304, 868904623024158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 519885601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 3, 0, 3, 2]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![0, 3, 0, 3, 2]] 
 ![![151, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![0, 3, 0, 3, 2], ![16, 14, -5, 22, 20], ![98, 99, -34, 144, 136], ![47, 46, -15, 70, 64], ![69, 69, -24, 101, 95]]]
  hmulB := by decide  
  f := ![![![40, 233, 128, -67, -188]], ![![4, 20, 11, -6, -16]], ![![2, 12, 8, -3, -12]], ![![17, 98, 53, -28, -78]], ![![9, 56, 32, -16, -47]]]
  g := ![![![-2, 3, 0, 3, 2], ![-15, 14, -5, 22, 20], ![-100, 99, -34, 144, 136], ![-48, 46, -15, 70, 64], ![-70, 69, -24, 101, 95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![40, 233, 128, -67, -188]] ![![0, 3, 0, 3, 2]]
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


lemma PB1640I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB1640I3 : PrimesBelowBoundCertificateInterval O 103 151 1640 where
  m := 9
  g := ![3, 3, 2, 1, 2, 2, 2, 3, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB1640I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2]
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
    · exact ![1225043, 107, 107]
    · exact ![11881, 11881, 109]
    · exact ![1442897, 12769]
    · exact ![33038369407]
    · exact ![2248091, 17161]
    · exact ![352275361, 137]
    · exact ![373301041, 139]
    · exact ![3307949, 149, 149]
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
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
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
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I107N1, I107N2, I109N2, I137N1, I139N1, I149N1, I149N2, I151N1]
  Il := ![[I107N1, I107N2], [I109N2], [], [], [], [I137N1], [I139N1], [I149N1, I149N2], [I151N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
