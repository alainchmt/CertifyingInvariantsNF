
import IdealArithmetic.Examples.NF5_1_24300000_2.RI5_1_24300000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39257, 9365, 16189, 4022, 19234]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![39257, 9365, 16189, 4022, 19234]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![108, 72, 73, 1, 0], ![138, 122, 106, 0, 1]] where
  M :=![![![39257, 9365, 16189, 4022, 19234], ![89002, 21000, 36643, 9122, 43366], ![200830, 48035, 82610, 20798, 98098], ![182892, 43521, 75543, 18601, 89760], ![-1783, -688, -734, -243, -1023]]]
  hmulB := by decide  
  f := ![![![-7773, 2249, -209, 780, -2410]], ![![-7300, -2382, 1399, 1212, 2270]], ![![12716, -9229, 2312, -684, 9542]], ![![-2644, -3844, 1565, 757, 3830]], ![![-3893, -6076, 2452, 1159, 6059]]]
  g := ![![![-19423, -16731, -14753, 4022, 19234], ![-43826, -37748, -33287, 9122, 43366], ![-99254, -85461, -75376, 20798, 98098], ![-90528, -78003, -68770, 18601, 89760], ![1055, 902, 799, -243, -1023]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [29, 10, 127, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [141, 73, 29], [46, 83, 128], [0, 1]]
 g := ![![[98, 144, 44], [80, 14], [122, 94, 143], [82, 3, 76], [37, 98, 35], [30, 1], []], ![[14, 49, 129, 149], [], [58, 11, 42, 97], [121, 17, 150, 2], [128, 75, 121, 79], [27, 138], [105, 56]], ![[54, 65, 115, 38], [144, 14], [127, 5, 68, 142], [131, 85, 42, 123], [108, 150, 36, 65], [41, 148], [6, 56]]]
 h' := ![![[141, 73, 29], [26, 114, 94], [73, 37, 93], [134, 83, 92], [26, 88, 95], [72, 142, 105], [0, 0, 1], [0, 1]], ![[46, 83, 128], [110, 61, 118], [96, 78], [12, 125, 152], [92, 61, 75], [115, 61, 116], [37, 14, 83], [141, 73, 29]], ![[0, 1], [46, 139, 102], [104, 42, 64], [25, 106, 70], [7, 8, 144], [134, 111, 93], [58, 143, 73], [46, 83, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [138, 151], []]
 b := ![[], [44, 136, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [29, 10, 127, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![199745, -146627, 96029, -12544, -29766]
  a := ![-13, -7, -11, 0, -26]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![36065, 27949, 26541, -12544, -29766]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![265, -251, 69, -8, 258]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![265, -251, 69, -8, 258]] 
 ![![157, 0, 0, 0, 0], ![62, 1, 0, 0, 0], ![81, 0, 1, 0, 0], ![127, 0, 0, 1, 0], ![85, 0, 0, 0, 1]] where
  M :=![![![265, -251, 69, -8, 258], ![1008, -190, -9, -112, 210], ![504, 467, -204, -116, -462], ![-1602, 649, -109, 141, -684], ![-1121, 76, 58, 139, -97]]]
  hmulB := by decide  
  f := ![![![-737, -47, -477, 114, -594]], ![![-304, -18, -191, 42, -234]], ![![-387, -44, -251, 56, -324]], ![![-629, -28, -406, 99, -498]], ![![-406, -19, -257, 59, -313]]]
  g := ![![![-68, -251, 69, -8, 258], ![63, -190, -9, -112, 210], ![268, 467, -204, -116, -462], ![46, 649, -109, 141, -684], ![-127, 76, 58, 139, -97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 4, -2, 0, -4]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![1, 4, -2, 0, -4]] 
 ![![157, 0, 0, 0, 0], ![106, 1, 0, 0, 0], ![68, 0, 1, 0, 0], ![111, 0, 0, 1, 0], ![111, 0, 0, 0, 1]] where
  M :=![![![1, 4, -2, 0, -4], ![-16, 7, 0, 0, -4], ![-16, -8, 3, 4, -4], ![6, -4, -2, 3, 12], ![18, -4, 2, -4, 11]]]
  hmulB := by decide  
  f := ![![![2277, 532, 934, 232, 1108]], ![![1570, 367, 644, 160, 764]], ![![1060, 248, 435, 108, 516]], ![![1677, 392, 688, 171, 816]], ![![1609, 376, 660, 164, 783]]]
  g := ![![![1, 4, -2, 0, -4], ![-2, 7, 0, 0, -4], ![4, -8, 3, 4, -4], ![-7, -4, -2, 3, 12], ![-3, -4, 2, -4, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![39257, 9365, 16189, 4022, 19234]] ![![265, -251, 69, -8, 258]]
  ![![-2277, -532, -934, -232, -1108]] where
 M := ![![![-2277, -532, -934, -232, -1108]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![-2277, -532, -934, -232, -1108]] ![![1, 4, -2, 0, -4]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![-157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4235437, -1006635, -1744329, -435222, -2068902]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-4235437, -1006635, -1744329, -435222, -2068902]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![85, 81, 16, 77, 1]] where
  M :=![![![-4235437, -1006635, -1744329, -435222, -2068902], ![-9581274, -2277184, -3945981, -984534, -4680234], ![-21674538, -5151321, -8926486, -2227194, -10587438], ![-19725030, -4688079, -8123583, -2026903, -9635184], ![215031, 51084, 88548, 22101, 105005]]]
  hmulB := by decide  
  f := ![![![-757, 255, -33, 72, -270]], ![![-864, -178, 129, 132, 162]], ![![1044, -927, 248, -36, 954]], ![![2286, -237, -87, -277, 288]], ![![362, -156, 29, -32, 167]]]
  g := ![![![1052891, 1021929, 192381, 974664, -2068902], ![2381832, 2311790, 435201, 2204868, -4680234], ![5388084, 5229639, 984494, 4987764, -10587438], ![4903470, 4759275, 895947, 4539155, -9635184], ![-53438, -51867, -9764, -49468, 105005]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 4 2 7 [12, 19, 86, 16, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 110, 112, 95], [11, 12, 83, 78], [32, 40, 131, 153], [0, 1]]
 g := ![![[100, 34, 141, 131], [70, 130, 95, 119], [112, 146, 64], [5, 15, 41], [95, 121, 49], [147, 1], []], ![[147, 135, 45, 152, 71, 140], [144, 2, 79, 95, 44, 38], [38, 39, 54], [129, 60, 51], [136, 71, 35], [20, 137, 121, 54, 102, 9], [150, 108, 60]], ![[104, 61, 120, 84, 53, 5], [106, 34, 121, 26, 26, 45], [123, 20, 43], [80, 0, 40], [84, 85, 81], [72, 8, 125, 19, 162, 123], [9, 38, 53]], ![[62, 2, 115, 118, 161, 50], [27, 25, 11, 131, 137, 130], [27, 113, 155], [129, 105, 57], [91, 106, 126], [103, 19, 31, 112, 161, 17], [138, 18, 100]]]
 h' := ![![[104, 110, 112, 95], [138, 105, 92, 91], [86, 66, 111, 114], [17, 1, 151, 155], [27, 150, 19, 82], [29, 129, 53, 7], [0, 0, 1], [0, 1]], ![[11, 12, 83, 78], [89, 31, 71, 73], [67, 86, 117, 14], [69, 125, 95, 124], [98, 90, 122, 41], [10, 160, 141, 19], [51, 152, 1, 113], [104, 110, 112, 95]], ![[32, 40, 131, 153], [31, 131, 23, 21], [143, 24, 100, 100], [106, 93, 73, 83], [96, 50, 142, 140], [17, 88, 41, 154], [13, 126, 1, 104], [11, 12, 83, 78]], ![[0, 1], [155, 59, 140, 141], [87, 150, 161, 98], [30, 107, 7, 127], [130, 36, 43, 63], [154, 112, 91, 146], [20, 48, 160, 109], [32, 40, 131, 153]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [114, 76, 47], []]
 b := ![[], [], [98, 126, 76, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 4
  hpos := by decide
  P := [12, 19, 86, 16, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13123736760, 15916871724, 1883044634, -3896849474, 17616394592]
  a := ![19, -56, 15, -67, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9266977160, -8656509756, -1717664226, -8345762166, 17616394592]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 705911761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-757, 255, -33, 72, -270]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-757, 255, -33, 72, -270]] 
 ![![163, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![139, 0, 1, 0, 0], ![136, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-757, 255, -33, 72, -270], ![-864, -178, 129, 132, 162], ![1044, -927, 248, -36, 954], ![2286, -237, -87, -277, 288], ![609, 396, -186, -123, -391]]]
  hmulB := by decide  
  f := ![![![-4235437, -1006635, -1744329, -435222, -2068902]], ![![-734372, -174538, -302445, -75462, -358722]], ![![-3744787, -890022, -1542259, -384804, -1829232]], ![![-3654874, -868653, -1505229, -375565, -1785312]], ![![-206555, -49092, -85068, -21225, -100897]]]
  g := ![![![-64, 255, -33, 72, -270], ![-205, -178, 129, 132, 162], ![-74, -927, 248, -36, 954], ![343, -237, -87, -277, 288], ![221, 396, -186, -123, -391]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-4235437, -1006635, -1744329, -435222, -2068902]] ![![-757, 255, -33, 72, -270]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![163, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4622, 3745, -979, 207, -3862]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-4622, 3745, -979, 207, -3862]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![8, 109, 1, 0, 0], ![65, 76, 0, 1, 0], ![130, 54, 0, 0, 1]] where
  M :=![![![-4622, 3745, -979, 207, -3862], ![-14827, 2330, 297, 1697, -2620], ![-5389, -7593, 3104, 1517, 7562], ![24813, -9111, 1353, -2284, 9642], ![16000, -482, -1042, -2048, 777]]]
  hmulB := by decide  
  f := ![![![-1386, 59, -629, -1, -556]], ![![-2227, -904, -499, -701, -562]], ![![-1546, -601, -373, -456, -422]], ![![-1601, -378, -490, -321, -480]], ![![-1798, -248, -646, -232, -607]]]
  g := ![![![2945, 1816, -979, 207, -3862], ![1276, -105, 297, 1697, -2620], ![-6658, -5207, 3104, 1517, 7562], ![-6533, -3016, 1353, -2284, 9642], ![338, 1358, -1042, -2048, 777]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [158, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [95, 166], [0, 1]]
 g := ![![[159, 107], [68, 65], [11, 81], [6], [58], [37, 7], [1]], ![[137, 60], [64, 102], [24, 86], [6], [58], [34, 160], [1]]]
 h' := ![![[95, 166], [111, 146], [99, 137], [37, 9], [22, 29], [166, 152], [9, 95], [0, 1]], ![[0, 1], [120, 21], [88, 30], [57, 158], [105, 138], [77, 15], [16, 72], [95, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [76, 132]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [158, 72, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![224, -122, -16, -217, -147]
  a := ![-2, -4, -2, -3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![201, 156, -16, -217, -147]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6863, 4111, -939, 462, -4272]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-6863, 4111, -939, 462, -4272]] 
 ![![167, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![97, 0, 0, 1, 0], ![139, 0, 0, 0, 1]] where
  M :=![![![-6863, 4111, -939, 462, -4272], ![-15702, 1204, 763, 1932, -1500], ![-204, -10007, 3568, 1094, 10092], ![29676, -8465, 755, -2991, 9078], ![15619, 1216, -1616, -2179, -943]]]
  hmulB := by decide  
  f := ![![![7525673, 1788689, 3099381, 773336, 3676128]], ![![1724244, 409814, 710115, 177182, 842256]], ![![2033170, 483237, 837342, 208928, 993156]], ![![4581067, 1088822, 1886672, 470749, 2237754]], ![![6261596, 1488245, 2578783, 643439, 3058655]]]
  g := ![![![2585, 4111, -939, 462, -4272], ![-410, 1204, 763, 1932, -1500], ![-7734, -10007, 3568, 1094, 10092], ![-3997, -8465, 755, -2991, 9078], ![2269, 1216, -1616, -2179, -943]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17289, -4116, -7114, -1784, -8438]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![-17289, -4116, -7114, -1784, -8438]] 
 ![![167, 0, 0, 0, 0], ![90, 1, 0, 0, 0], ![83, 0, 1, 0, 0], ![61, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![-17289, -4116, -7114, -1784, -8438], ![-39104, -9311, -16122, -4006, -19142], ![-88586, -20948, -36465, -9096, -43178], ![-80448, -19240, -33098, -8325, -39306], ![916, 176, 350, 110, 375]]]
  hmulB := by decide  
  f := ![![![241685, -54644, 1074, -25884, 59518]], ![![131210, -28863, 298, -14138, 31502]], ![![117259, -25520, 169, -12664, 27876]], ![![84691, -20060, 700, -8973, 21776]], ![![79333, -18972, 720, -8386, 20581]]]
  g := ![![![9081, -4116, -7114, -1784, -8438], ![20564, -9311, -16122, -4006, -19142], ![46425, -20948, -36465, -9096, -43178], ![42323, -19240, -33098, -8325, -39306], ![-427, 176, 350, 110, 375]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2

def I167N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2836, 664, 1166, 291, 1376]] i)))

def SI167N3: IdealEqSpanCertificate' Table ![![2836, 664, 1166, 291, 1376]] 
 ![![167, 0, 0, 0, 0], ![99, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![132, 0, 0, 1, 0], ![93, 0, 0, 0, 1]] where
  M :=![![![2836, 664, 1166, 291, 1376], ![6377, 1541, 2622, 665, 3122], ![14483, 3420, 5993, 1457, 7112], ![13221, 3084, 5412, 1376, 6366], ![-173, -2, -82, 1, -81]]]
  hmulB := by decide  
  f := ![![![-15558, -18256, 7660, 3989, 18134]], ![![-8717, -11063, 4588, 2324, 11002]], ![![-3959, -5676, 2315, 1125, 5654]], ![![-12711, -13968, 5922, 3158, 13860]], ![![-9379, -9930, 4236, 2290, 9847]]]
  g := ![![![-1736, 664, 1166, 291, 1376], ![-3956, 1541, 2622, 665, 3122], ![-8919, 3420, 5993, 1457, 7112], ![-8067, 3084, 5412, 1376, 6366], ![70, -2, -82, 1, -81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N3 : Nat.card (O ⧸ I167N3) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N3)

lemma isPrimeI167N3 : Ideal.IsPrime I167N3 := prime_ideal_of_norm_prime hp167.out _ NI167N3
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-4622, 3745, -979, 207, -3862]] ![![-6863, 4111, -939, 462, -4272]]
  ![![-81061134, -11143656, 10101698, 11825111, 9768628]] where
 M := ![![![-81061134, -11143656, 10101698, 11825111, 9768628]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![-81061134, -11143656, 10101698, 11825111, 9768628]] ![![-17289, -4116, -7114, -1784, -8438]]
  ![![-15558, -18256, 7660, 3989, 18134]] where
 M := ![![![-15558, -18256, 7660, 3989, 18134]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI167N2 : IdealMulLeCertificate' Table 
  ![![-15558, -18256, 7660, 3989, 18134]] ![![2836, 664, 1166, 291, 1376]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2, I167N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
    exact isPrimeI167N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1 ⊙ MulI167N2)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-107, 111, -57, 32, -12]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-107, 111, -57, 32, -12]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![81, 34, 48, 55, 1]] where
  M :=![![![-107, 111, -57, 32, -12], ![48, -108, 163, -134, 180], ![318, -283, -196, 280, -624], ![-852, 879, -255, 43, 438], ![111, -120, 258, -245, 373]]]
  hmulB := by decide  
  f := ![![![23, 3, 9, 2, 12]], ![![54, 10, 19, 4, 24]], ![![108, 29, 42, 10, 48]], ![![84, 27, 39, 11, 42]], ![![78, 20, 32, 8, 37]]]
  g := ![![![5, 3, 3, 4, -12], ![-84, -36, -49, -58, 180], ![294, 121, 172, 200, -624], ![-210, -81, -123, -139, 438], ![-174, -74, -102, -120, 373]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 4 2 7 [132, 159, 58, 40, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 50, 164, 58], [152, 3, 135, 13], [81, 119, 47, 102], [0, 1]]
 g := ![![[6, 43, 99, 149], [102, 21, 73], [81, 0, 52, 118], [166, 134, 172, 10], [147, 41, 52], [133, 1], []], ![[89, 29, 158, 24, 28, 26], [157, 81, 117], [41, 59, 79, 33, 95, 70], [0, 51, 153, 99, 168, 71], [14, 145, 138], [143, 107, 41, 167, 46, 68], [122, 28, 77]], ![[41, 171, 95, 62, 128, 36], [131, 102, 43], [44, 157, 110, 0, 38, 49], [88, 128, 31, 91, 124, 92], [41, 110, 54], [23, 4, 83, 94, 32, 92], [101, 37, 169]], ![[159, 95, 10, 50, 5, 107], [151, 125, 124], [28, 131, 142, 29, 63, 104], [69, 92, 156, 44, 140, 141], [34, 108, 116], [91, 168, 16, 135, 36, 110], [23, 151, 24]]]
 h' := ![![[73, 50, 164, 58], [148, 38, 161, 144], [34, 117, 0, 65], [59, 54, 113, 139], [114, 106, 138, 150], [90, 0, 85, 158], [0, 0, 1], [0, 1]], ![[152, 3, 135, 13], [153, 11, 105, 50], [64, 157, 2, 109], [100, 24, 64, 27], [80, 162, 3, 127], [5, 146, 1, 151], [124, 122, 81, 66], [73, 50, 164, 58]], ![[81, 119, 47, 102], [30, 38, 155, 103], [117, 75, 79, 40], [22, 8, 163, 149], [51, 156, 141, 96], [163, 108, 100, 20], [84, 37, 80, 77], [152, 3, 135, 13]], ![[0, 1], [63, 86, 98, 49], [10, 170, 92, 132], [12, 87, 6, 31], [43, 95, 64, 146], [129, 92, 160, 17], [65, 14, 11, 30], [81, 119, 47, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [142, 48, 35], []]
 b := ![[], [], [44, 30, 108, 157], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 4
  hpos := by decide
  P := [132, 159, 58, 40, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![822408943, 260657315, 307975713, 128492257, 385472406]
  a := ![23, 27, 19, 12, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-175727491, -74250893, -105171675, -121806301, 385472406]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 895745041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 3, 9, 2, 12]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![23, 3, 9, 2, 12]] 
 ![![173, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![121, 0, 1, 0, 0], ![123, 0, 0, 1, 0], ![132, 0, 0, 0, 1]] where
  M :=![![![23, 3, 9, 2, 12], ![54, 10, 19, 4, 24], ![108, 29, 42, 10, 48], ![84, 27, 39, 11, 42], ![-9, 0, 0, 1, -1]]]
  hmulB := by decide  
  f := ![![![-107, 111, -57, 32, -12]], ![![-9, 9, -4, 2, 0]], ![![-73, 76, -41, 24, -12]], ![![-81, 84, -42, 23, -6]], ![![-81, 84, -42, 23, -7]]]
  g := ![![![-17, 3, 9, 2, 12], ![-35, 10, 19, 4, 24], ![-75, 29, 42, 10, 48], ![-69, 27, 39, 11, 42], ![0, 0, 0, 1, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-107, 111, -57, 32, -12]] ![![23, 3, 9, 2, 12]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![173, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24, -10, -12, -1, -14]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-24, -10, -12, -1, -14]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![162, 104, 116, 1, 0], ![118, 70, 146, 0, 1]] where
  M :=![![![-24, -10, -12, -1, -14], ![-59, -9, -26, -9, -20], ![-107, -54, -47, -23, -74], ![-153, -10, -74, 6, -96], ![-29, 18, -2, 1, 9]]]
  hmulB := by decide  
  f := ![![![-10, 6, -2, 1, -8]], ![![-29, 5, 0, 3, -2]], ![![1, -22, 9, -1, 16]], ![![-25, -6, 4, 2, 2]], ![![-17, -12, 6, 1, 7]]]
  g := ![![![10, 6, 12, -1, -14], ![21, 13, 22, -9, -20], ![69, 42, 75, -23, -74], ![57, 34, 74, 6, -96], ![-7, -4, -8, 1, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [63, 71, 89, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 112, 6], [4, 66, 173], [0, 1]]
 g := ![![[10, 152, 156], [37, 37, 155], [7, 177], [146, 75], [117, 59, 126], [153, 90, 1], []], ![[10, 169, 18, 78], [18, 100, 82, 128], [99, 75], [64, 60], [41, 48, 36, 114], [99, 12, 160, 2], [109, 36]], ![[69, 117, 122, 39], [18, 134, 157, 76], [98, 36], [4, 125], [5, 155, 119, 80], [163, 160, 0, 95], [121, 36]]]
 h' := ![![[86, 112, 6], [175, 85, 131], [116, 62, 100], [60, 23, 78], [147, 161, 84], [27, 114, 157], [0, 0, 1], [0, 1]], ![[4, 66, 173], [172, 154, 27], [173, 54, 170], [161, 30, 95], [75, 144, 66], [162, 107, 127], [171, 128, 66], [86, 112, 6]], ![[0, 1], [133, 119, 21], [56, 63, 88], [12, 126, 6], [117, 53, 29], [114, 137, 74], [90, 51, 112], [4, 66, 173]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136, 29], []]
 b := ![[], [44, 99, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [63, 71, 89, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2030457, -1830763, -950513, 1369654, -3479027]
  a := ![-33, -9, -27, 15, -65]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1065205, 554509, 1944735, 1369654, -3479027]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, 6, -2, 1, -8]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-10, 6, -2, 1, -8]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![96, 126, 1, 0, 0], ![38, 76, 0, 1, 0], ![161, 22, 0, 0, 1]] where
  M :=![![![-10, 6, -2, 1, -8], ![-29, 5, 0, 3, -2], ![1, -22, 9, -1, 16], ![45, -14, -4, 0, 6], ![21, 6, -4, -3, 1]]]
  hmulB := by decide  
  f := ![![![-24, -10, -12, -1, -14]], ![![-59, -9, -26, -9, -20]], ![![-55, -12, -25, -7, -22]], ![![-31, -6, -14, -4, -12]], ![![-29, -10, -14, -2, -15]]]
  g := ![![![8, 2, -2, 1, -8], ![1, -1, 0, 3, -2], ![-19, -8, 9, -1, 16], ![-3, 2, -4, 0, 6], ![2, 4, -4, -3, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [23, 169, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 178], [0, 1]]
 g := ![![[163, 20], [126, 151], [144], [20], [64, 74], [3, 100], [1]], ![[5, 159], [25, 28], [144], [20], [88, 105], [108, 79], [1]]]
 h' := ![![[10, 178], [145, 119], [149, 35], [66, 167], [139, 119], [110, 49], [156, 10], [0, 1]], ![[0, 1], [82, 60], [141, 144], [125, 12], [76, 60], [63, 130], [77, 169], [10, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [46, 134]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal' SI179N1 179 where
  n := 2
  hpos := by decide
  P := [23, 169, 1]
  hirr := P179P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1517, 2444, -2764, 458, -1100]
  a := ![14, -4, 12, -22, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2383, 1900, -2764, 458, -1100]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N1 B_one_repr
lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-24, -10, -12, -1, -14]] ![![-10, 6, -2, 1, -8]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![179, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2754, 999, -555, -477, -940]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![2754, 999, -555, -477, -940]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![0, 0, 0, 181, 0], ![123, 18, 171, 55, 1]] where
  M :=![![![2754, 999, -555, -477, -940], ![-5191, 3602, -895, 307, -3802], ![-14287, 1825, 414, 1705, -1960], ![1233, -5925, 2085, 388, 6036], ![8674, -4090, 784, -692, 4157]]]
  hmulB := by decide  
  f := ![![![25274, 6007, 10409, 2597, 12346]], ![![57175, 13588, 23547, 5875, 27928]], ![![129337, 30741, 53266, 13291, 63178]], ![![117705, 27975, 48477, 12094, 57498]], ![![180812, 42975, 74466, 18580, 88323]]]
  g := ![![![654, 99, 885, 283, -940], ![2555, 398, 3587, 1157, -3802], ![1253, 205, 1854, 605, -1960], ![-4095, -633, -5691, -1832, 6036], ![-2777, -436, -3923, -1267, 4157]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 4 2 7 [165, 119, 154, 66, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 53, 140, 91], [60, 29, 169, 166], [39, 98, 53, 105], [0, 1]]
 g := ![![[1, 105, 115, 132], [13, 79, 49], [50, 57, 128, 4], [79, 102, 101], [30, 35, 30, 73], [115, 1], []], ![[155, 6, 95, 111, 163, 66], [11, 160, 167], [59, 156, 48, 175, 106, 41], [122, 165, 14], [127, 163, 33, 76, 46, 58], [77, 172, 44, 30, 139, 78], [151, 33, 136]], ![[101, 174, 22, 22, 91, 37], [110, 96, 136], [136, 15, 165, 30, 16, 14], [106, 18, 172], [71, 154, 165, 54, 16, 13], [98, 112, 70, 149, 42, 114], [36, 171, 44]], ![[60, 44, 144, 32, 45, 103], [137, 63, 101], [37, 5, 82, 154, 22, 162], [151, 60, 144], [160, 10, 138, 58, 26, 171], [163, 123, 130, 12, 35, 110], [58, 59, 165]]]
 h' := ![![[16, 53, 140, 91], [11, 111, 124, 48], [76, 105, 172, 7], [165, 166, 83, 179], [118, 62, 173, 120], [30, 87, 90, 39], [0, 0, 1], [0, 1]], ![[60, 29, 169, 166], [165, 161, 91, 133], [52, 174, 7, 23], [108, 27, 144, 156], [50, 110, 76, 106], [46, 144, 36, 109], [138, 2, 22, 95], [16, 53, 140, 91]], ![[39, 98, 53, 105], [5, 24, 3, 156], [112, 63, 159, 90], [161, 145, 46, 118], [53, 174, 167, 124], [124, 7, 162, 95], [13, 122, 95, 120], [60, 29, 169, 166]], ![[0, 1], [100, 66, 144, 25], [108, 20, 24, 61], [136, 24, 89, 90], [142, 16, 127, 12], [32, 124, 74, 119], [96, 57, 63, 147], [39, 98, 53, 105]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [79, 26, 166], []]
 b := ![[], [], [6, 128, 21, 180], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 4
  hpos := by decide
  P := [165, 119, 154, 66, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![714611376, 190753445, 278903017, 91241909, 337732902]
  a := ![29, 19, 20, 10, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-225560970, -32532811, -317532725, -102121921, 337732902]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 1073283121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25274, -6007, -10409, -2597, -12346]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-25274, -6007, -10409, -2597, -12346]] 
 ![![181, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![125, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-25274, -6007, -10409, -2597, -12346], ![-57175, -13588, -23547, -5875, -27928], ![-129337, -30741, -53266, -13291, -63178], ![-117705, -27975, -48477, -12094, -57498], ![1282, 306, 528, 132, 627]]]
  hmulB := by decide  
  f := ![![![-2754, -999, 555, 477, 940]], ![![-443, -191, 100, 80, 182]], ![![-1823, -700, 381, 320, 660]], ![![-585, -177, 105, 98, 164]], ![![-124, -5, 11, 17, 3]]]
  g := ![![![8964, -6007, -10409, -2597, -12346], ![20278, -13588, -23547, -5875, -27928], ![45872, -30741, -53266, -13291, -63178], ![41747, -27975, -48477, -12094, -57498], ![-455, 306, 528, 132, 627]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![2754, 999, -555, -477, -940]] ![![-25274, -6007, -10409, -2597, -12346]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![-181, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12, -3, -3, -3, -2]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-12, -3, -3, -3, -2]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![106, 85, 1, 0, 0], ![79, 70, 0, 1, 0], ![15, 151, 0, 0, 1]] where
  M :=![![![-12, -3, -3, -3, -2], ![-17, -14, -11, -1, -20], ![-83, 11, -36, -1, -26], ![-45, -27, -3, -22, -6], ![14, -14, 2, 2, -11]]]
  hmulB := by decide  
  f := ![![![-88, 55, -13, 5, -56]], ![![-209, 16, 9, 25, -26]], ![![-142, 37, -3, 14, -42]], ![![-111, 28, -2, 11, -32]], ![![-171, 17, 6, 20, -25]]]
  g := ![![![3, 4, -3, -3, -2], ![8, 21, -11, -1, -20], ![22, 37, -36, -1, -26], ![11, 14, -3, -22, -6], ![-1, 7, 2, 2, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [55, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [165, 190], [0, 1]]
 g := ![![[188, 128], [169, 40], [152, 138], [107, 1], [4, 8], [182, 103], [1]], ![[107, 63], [84, 151], [2, 53], [81, 190], [178, 183], [178, 88], [1]]]
 h' := ![![[165, 190], [64, 117], [44, 68], [36, 105], [162, 1], [113, 77], [136, 165], [0, 1]], ![[0, 1], [78, 74], [186, 123], [171, 86], [136, 190], [21, 114], [48, 26], [165, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [170, 160]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [55, 26, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21, 226, -244, 131, -123]
  a := ![3, -3, 3, -6, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![91, 159, -244, 131, -123]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-50, 55, -41, 29, -22]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-50, 55, -41, 29, -22]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![167, 74, 1, 0, 0], ![124, 20, 0, 1, 0], ![141, 103, 0, 0, 1]] where
  M :=![![![-50, 55, -41, 29, -22], ![-1, -18, 91, -89, 152], ![341, -303, -44, 119, -382], ![-585, 599, -269, 132, 90], ![-60, 26, 134, -144, 275]]]
  hmulB := by decide  
  f := ![![![-246, 101, 17, 37, -64]], ![![-145, -64, 111, 61, 158]], ![![-267, 62, 59, 56, 8]], ![![-169, 59, 23, 30, -24]], ![![-259, 41, 72, 60, 37]]]
  g := ![![![33, 25, -41, 29, -22], ![-134, -108, 91, -89, 152], ![245, 209, -44, 119, -382], ![80, 45, -269, 132, 90], ![-227, -185, 134, -144, 275]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P1 : CertificateIrreducibleZModOfList' 191 2 2 7 [15, 185, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 190], [0, 1]]
 g := ![![[76, 51], [93, 80], [54, 109], [175, 64], [129, 60], [36, 36], [1]], ![[0, 140], [0, 111], [135, 82], [177, 127], [107, 131], [61, 155], [1]]]
 h' := ![![[6, 190], [133, 137], [145, 135], [49, 142], [166, 8], [33, 92], [176, 6], [0, 1]], ![[0, 1], [0, 54], [0, 56], [137, 49], [23, 183], [12, 99], [21, 185], [6, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [143, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N1 : CertifiedPrimeIdeal' SI191N1 191 where
  n := 2
  hpos := by decide
  P := [15, 185, 1]
  hirr := P191P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7743, 1167, 4447, 352, 6808]
  a := ![19, 9, 16, -1, 35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9102, -5425, 4447, 352, 6808]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N1 B_one_repr
lemma NI191N1 : Nat.card (O ⧸ I191N1) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -98, 34, 10, 98]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![1, -98, 34, 10, 98]] 
 ![![191, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![122, 0, 1, 0, 0], ![133, 0, 0, 1, 0], ![95, 0, 0, 0, 1]] where
  M :=![![![1, -98, 34, 10, 98], ![422, -151, 20, -40, 158], ![512, 86, -73, -78, -82], ![-492, 338, -86, 27, -354], ![-546, 128, -4, 58, -139]]]
  hmulB := by decide  
  f := ![![![1455, -1546, 890, -546, 134]], ![![238, -251, 136, -80, 6]], ![![898, -962, 583, -370, 138]], ![![1089, -1152, 644, -387, 64]], ![![721, -762, 422, -252, 35]]]
  g := ![![![-61, -98, 34, 10, 98], ![-36, -151, 20, -40, 158], ![130, 86, -73, -78, -82], ![153, 338, -86, 27, -354], ![7, 128, -4, 58, -139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-12, -3, -3, -3, -2]] ![![-50, 55, -41, 29, -22]]
  ![![1455, -1546, 890, -546, 134]] where
 M := ![![![1455, -1546, 890, -546, 134]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![1455, -1546, 890, -546, 134]] ![![1, -98, 34, 10, 98]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![191, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, -49, 17, -4, -26]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![41, -49, 17, -4, -26]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![106, 3, 145, 1, 0], ![138, 187, 29, 0, 1]] where
  M :=![![![41, -49, 17, -4, -26], ![-116, 106, -83, 64, -50], ![-8, -35, 184, -180, 334], ![456, -389, 11, 75, -348], ![-117, 160, -152, 113, -131]]]
  hmulB := by decide  
  f := ![![![-297, -73, -121, -30, -142]], ![![-658, -164, -275, -70, -322]], ![![-1498, -359, -626, -158, -742]], ![![-1306, -314, -544, -137, -644]], ![![-1075, -265, -447, -113, -525]]]
  g := ![![![21, 25, 7, -4, -26], ![0, 48, -41, 64, -50], ![-140, -321, 86, -180, 334], ![210, 334, -4, 75, -348], ![31, 126, -66, 113, -131]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [178, 146, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 192, 56], [144, 0, 137], [0, 1]]
 g := ![![[157, 192, 147], [135, 107], [133, 42], [74, 109], [49, 186], [183, 100], [1]], ![[189, 54, 156, 128], [101, 181], [61, 138], [85, 50], [81, 16], [15, 75], [71, 148, 189, 179]], ![[106, 71, 76, 65], [161, 25], [143, 75], [65, 109], [63, 184], [75, 31], [185, 20, 53, 14]]]
 h' := ![![[39, 192, 56], [111, 168, 98], [189, 56, 140], [33, 151, 106], [184, 147, 130], [75, 124, 147], [15, 47, 183], [0, 1]], ![[144, 0, 137], [160, 168, 144], [31, 38, 48], [184, 47, 157], [158, 23, 126], [78, 187, 189], [168, 29, 123], [39, 192, 56]], ![[0, 1], [24, 50, 144], [120, 99, 5], [22, 188, 123], [28, 23, 130], [137, 75, 50], [154, 117, 80], [144, 0, 137]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [183, 35], []]
 b := ![[], [110, 12, 120], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [178, 146, 10, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-261155, 411197, 139699, -143352, 575789]
  a := ![21, 7, 17, -8, 41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-334325, -553530, 21906, -143352, 575789]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![297, 73, 121, 30, 142]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![297, 73, 121, 30, 142]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![140, 96, 1, 0, 0], ![35, 191, 0, 1, 0], ![135, 70, 0, 0, 1]] where
  M :=![![![297, 73, 121, 30, 142], ![658, 164, 275, 70, 322], ![1498, 359, 626, 158, 742], ![1392, 317, 571, 141, 684], ![1, -8, -6, -3, -3]]]
  hmulB := by decide  
  f := ![![![-41, 49, -17, 4, 26]], ![![116, -106, 83, -64, 50]], ![![28, -17, 28, -28, 42]], ![![105, -94, 79, -63, 56]], ![![14, -5, 19, -21, 37]]]
  g := ![![![-191, -141, 121, 30, 142], ![-434, -322, 275, 70, 322], ![-994, -735, 626, 158, 742], ![-911, -670, 571, 141, 684], ![7, 7, -6, -3, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P1 : CertificateIrreducibleZModOfList' 193 2 2 7 [30, 186, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 192], [0, 1]]
 g := ![![[122, 186], [177], [138], [147], [85], [168], [7, 1]], ![[73, 7], [177], [138], [147], [85], [168], [14, 192]]]
 h' := ![![[7, 192], [38, 147], [152, 131], [25, 157], [31, 98], [74, 144], [176, 19], [0, 1]], ![[0, 1], [102, 46], [104, 62], [159, 36], [138, 95], [117, 49], [116, 174], [7, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [155]]
 b := ![[], [163, 174]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N1 : CertifiedPrimeIdeal' SI193N1 193 where
  n := 2
  hpos := by decide
  P := [30, 186, 1]
  hirr := P193P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5370, 1270, 3233, 294, 5546]
  a := ![15, 8, 11, 1, 26]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6250, -3904, 3233, 294, 5546]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N1 B_one_repr
lemma NI193N1 : Nat.card (O ⧸ I193N1) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![41, -49, 17, -4, -26]] ![![297, 73, 121, 30, 142]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![-193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![182959, 43489, 75349, 18802, 89372]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![182959, 43489, 75349, 18802, 89372]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![162, 144, 109, 133, 1]] where
  M :=![![![182959, 43489, 75349, 18802, 89372], ![413894, 98366, 170465, 42524, 202184], ![936308, 222515, 385598, 96222, 457328], ![852042, 202553, 350911, 87561, 416238], ![-9285, -2212, -3814, -965, -4519]]]
  hmulB := by decide  
  f := ![![![105, -19, -1, -12, 20]], ![![44, 52, -23, -10, -52]], ![![-238, 115, -20, 16, -112]], ![![-222, -35, 29, 33, 18]], ![![-163, 62, -9, 14, -71]]]
  g := ![![![-72565, -65107, -49067, -60242, 89372], ![-164162, -147290, -111003, -136284, 202184], ![-371324, -333161, -251082, -308266, 457328], ![-337962, -303227, -228523, -280569, 416238], ![3669, 3292, 2481, 3046, -4519]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 4 2 7 [88, 111, 81, 90, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [187, 152, 119, 32], [59, 129, 61, 146], [58, 112, 17, 19], [0, 1]]
 g := ![![[121, 182, 73, 24], [68, 58, 158], [168, 129, 163, 49], [155, 28, 107], [16, 105, 144], [139, 107, 1], []], ![[51, 100, 30, 21, 63, 68], [52, 86, 188], [175, 164, 126, 148, 23, 185], [176, 108, 15], [90, 89, 193], [41, 65, 116], [74, 143, 190, 172, 103, 66]], ![[189, 26, 9, 13, 94, 146], [83, 42, 172], [56, 91, 96, 182, 189, 22], [152, 94, 187], [165, 182, 142], [43, 24, 7], [76, 2, 99, 22, 27, 127]], ![[123, 4, 129, 36, 79, 76], [130, 1, 15], [44, 60, 116, 5, 1, 187], [191, 81, 81], [156, 166, 70], [151, 109, 47], [121, 152, 28, 161, 178, 161]]]
 h' := ![![[187, 152, 119, 32], [7, 162, 55, 40], [188, 98, 156, 143], [101, 172, 3, 7], [98, 56, 118, 86], [179, 174, 22, 185], [0, 0, 0, 1], [0, 1]], ![[59, 129, 61, 146], [133, 120, 147, 154], [104, 167, 179, 42], [38, 18, 86, 70], [95, 14, 18, 139], [23, 28, 62, 28], [171, 177, 191, 126], [187, 152, 119, 32]], ![[58, 112, 17, 19], [133, 85, 120, 1], [98, 8, 18, 70], [127, 79, 186, 187], [86, 47, 144, 160], [182, 128, 50, 39], [115, 117, 114, 91], [59, 129, 61, 146]], ![[0, 1], [124, 27, 72, 2], [170, 121, 41, 139], [143, 125, 119, 130], [3, 80, 114, 9], [170, 64, 63, 142], [72, 100, 89, 176], [58, 112, 17, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [68, 83, 183], []]
 b := ![[], [], [139, 11, 118, 189], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 4
  hpos := by decide
  P := [88, 111, 81, 90, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-184128131, 217559675, -72027875, 24273107, 65679533]
  a := ![9, -7, 1, -25, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-54945241, -46905041, -36706076, -44218806, 65679533]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 1506138481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![105, -19, -1, -12, 20]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![105, -19, -1, -12, 20]] 
 ![![197, 0, 0, 0, 0], ![186, 1, 0, 0, 0], ![76, 0, 1, 0, 0], ![128, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![105, -19, -1, -12, 20], ![44, 52, -23, -10, -52], ![-238, 115, -20, 16, -112], ![-222, -35, 29, 33, 18], ![11, -76, 24, 9, 75]]]
  hmulB := by decide  
  f := ![![![182959, 43489, 75349, 18802, 89372]], ![![174844, 41560, 72007, 17968, 85408]], ![![75336, 17907, 31026, 7742, 36800]], ![![123202, 29285, 50739, 12661, 60182]], ![![33387, 7936, 13750, 3431, 16309]]]
  g := ![![![23, -19, -1, -12, 20], ![-24, 52, -23, -10, -52], ![-92, 115, -20, 16, -112], ![-4, -35, 29, 33, 18], ![43, -76, 24, 9, 75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![182959, 43489, 75349, 18802, 89372]] ![![105, -19, -1, -12, 20]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![197, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)


lemma PB307I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB307I4 : PrimesBelowBoundCertificateInterval O 151 197 307 where
  m := 9
  g := ![3, 2, 4, 2, 2, 2, 3, 2, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB307I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1, I167N2, I167N3]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1, I191N2]
    · exact ![I193N0, I193N1]
    · exact ![I197N0, I197N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
    · exact PBC197
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![3869893, 157, 157]
    · exact ![705911761, 163]
    · exact ![27889, 167, 167, 167]
    · exact ![895745041, 173]
    · exact ![5735339, 32041]
    · exact ![1073283121, 181]
    · exact ![36481, 36481, 191]
    · exact ![7189057, 37249]
    · exact ![1506138481, 197]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
      exact NI167N3
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I157N1, I157N2, I163N1, I167N1, I167N2, I167N3, I173N1, I181N1, I191N2, I197N1]
  Il := ![[I157N1, I157N2], [I163N1], [I167N1, I167N2, I167N3], [I173N1], [], [I181N1], [I191N2], [], [I197N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
