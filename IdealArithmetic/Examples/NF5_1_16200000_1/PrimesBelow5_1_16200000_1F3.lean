
import IdealArithmetic.Examples.NF5_1_16200000_1.RI5_1_16200000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22415, -9026, 7780, -4240, 18728]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-22415, -9026, 7780, -4240, 18728]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![54, 23, 61, 49, 1]] where
  M :=![![![-22415, -9026, 7780, -4240, 18728], ![37456, -3683, 518, -696, -8120], ![-16240, 50966, -35699, 20756, -57304], ![-76032, -68122, 53426, -29937, 109872], ![11684, -35414, 24818, -14420, 39739]]]
  hmulB := by decide  
  f := ![![![-741, -258, -16, 96, 8]], ![![16, -1437, 822, -528, 2344]], ![![4688, 2190, -213, -404, -952]], ![![-960, 4846, -2966, 2013, -8400]], ![![1834, 3021, -1313, 631, -3885]]]
  g := ![![![-9661, -4110, -10604, -8616, 18728], ![4448, 1711, 4634, 3712, -8120], ![28768, 12794, 32335, 26436, -57304], ![-56160, -24254, -62138, -50595, 109872], ![-19946, -8873, -22423, -18333, 39739]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 4 2 6 [4, 60, 57, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 72, 67, 55], [5, 85, 71, 101], [87, 56, 76, 58], [0, 1]]
 g := ![![[104, 84, 28, 48], [24, 38, 106, 1], [72, 84, 86], [82, 29, 53, 76], [59, 104, 1], []], ![[71, 59, 80, 9, 11, 72], [94, 23, 0, 4, 30, 68], [62, 77, 9], [91, 65, 8, 79, 34, 21], [11, 99, 27], [69, 39, 19, 95, 81, 97]], ![[27, 76, 30, 80, 11, 99], [29, 4, 41, 76, 31, 1], [53, 83, 105], [90, 68, 32, 61, 29, 57], [69, 53, 40], [43, 102, 64, 73, 77, 105]], ![[100, 1, 46, 76, 31, 6], [29, 73, 35, 55, 55, 55], [48], [83, 42, 16, 36, 73, 38], [35, 77, 86], [67, 98, 97, 23, 77, 51]]]
 h' := ![![[12, 72, 67, 55], [11, 103, 22, 72], [82, 8, 106, 106], [100, 49, 90, 34], [85, 3, 23, 41], [0, 0, 0, 1], [0, 1]], ![[5, 85, 71, 101], [56, 10, 50, 35], [6, 62, 93, 9], [19, 102, 54, 104], [39, 28, 88, 11], [61, 58, 34, 53], [12, 72, 67, 55]], ![[87, 56, 76, 58], [50, 84, 54, 12], [66, 100, 18, 93], [99, 15, 35, 76], [7, 89, 43, 77], [60, 70, 13, 19], [5, 85, 71, 101]], ![[0, 1], [80, 17, 88, 95], [56, 44, 104, 6], [26, 48, 35], [59, 94, 60, 85], [78, 86, 60, 34], [87, 56, 76, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [12, 33, 30], []]
 b := ![[], [], [12, 56, 44, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 4
  hpos := by decide
  P := [4, 60, 57, 3, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2762708132, 993593626, 3480243750, -327018163, 4828911534]
  a := ![0, 36, -63, 23, -131]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2411201072, -1028704408, -2720405232, -2214426947, 4828911534]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 131079601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-741, -258, -16, 96, 8]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-741, -258, -16, 96, 8]] 
 ![![107, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![91, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![93, 0, 0, 0, 1]] where
  M :=![![![-741, -258, -16, 96, 8], ![16, -1437, 822, -528, 2344], ![4688, 2190, -213, -404, -952], ![-960, 4846, -2966, 2013, -8400], ![-3044, -814, -206, 484, -367]]]
  hmulB := by decide  
  f := ![![![-22415, -9026, 7780, -4240, 18728]], ![![-21227, -8723, 7494, -4088, 17952]], ![![-19215, -7200, 6283, -3412, 15392]], ![![-16841, -7132, 6098, -3331, 14504]], ![![-19373, -8176, 6994, -3820, 16649]]]
  g := ![![![179, -258, -16, 96, 8], ![-973, -1437, 822, -528, 2344], ![-765, 2190, -213, -404, -952], ![3701, 4846, -2966, 2013, -8400], ![901, -814, -206, 484, -367]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-22415, -9026, 7780, -4240, 18728]] ![![-741, -258, -16, 96, 8]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0, 0, 0]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]] where
  M :=![![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 5 2 6 [75, 99, 71, 1, 41, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 40, 85, 83, 88], [29, 102, 22, 84, 69], [108, 50, 48, 8, 107], [69, 25, 63, 43, 63], [0, 1]]
 g := ![![[28, 91, 36, 77, 108], [48, 103, 95, 27], [1, 94, 19, 26, 81], [43, 54, 76, 58, 63], [68, 1], []], ![[69, 94, 21, 25, 79, 55, 84, 31], [93, 99, 85, 93], [100, 2, 92, 46, 68, 17, 3, 82], [81, 93, 68, 5, 35, 90, 78, 16], [41, 26, 20, 46], [58, 70, 30, 101, 95, 36, 100, 4]], ![[19, 47, 97, 102, 82, 102, 100, 68], [62, 19, 89, 46], [102, 23, 93, 60, 49, 30, 16, 19], [30, 46, 46, 74, 11, 68, 82, 98], [96, 55, 57, 9], [95, 62, 102, 84, 50, 36, 52, 92]], ![[34, 29, 89, 86, 78, 93, 1, 68], [86, 68, 7, 106], [29, 65, 24, 92, 77, 59, 79, 85], [31, 45, 85, 96, 70, 57, 21, 44], [17, 56, 82, 34], [52, 106, 91, 21, 104, 38, 97, 101]], ![[85, 43, 63, 51, 20, 45, 107, 89], [81, 81, 4, 27], [99, 55, 70, 13, 94, 12, 44, 93], [77, 89, 51, 73, 89, 97, 0, 75], [65, 54, 103, 80], [58, 8, 15, 88, 54, 106, 96, 1]]]
 h' := ![![[80, 40, 85, 83, 88], [63, 99, 26, 49, 76], [34, 108, 76, 10, 71], [45, 70, 106, 26, 100], [23, 60, 87, 79, 45], [0, 0, 0, 1], [0, 1]], ![[29, 102, 22, 84, 69], [105, 11, 31, 81, 75], [70, 20, 90, 29, 86], [9, 60, 35, 14, 22], [38, 99, 60, 30, 67], [37, 3, 45, 103, 41], [80, 40, 85, 83, 88]], ![[108, 50, 48, 8, 107], [2, 36, 76, 14, 85], [69, 29, 7, 52, 41], [55, 0, 52, 65, 53], [14, 30, 32, 90, 49], [42, 3, 105, 71, 3], [29, 102, 22, 84, 69]], ![[69, 25, 63, 43, 63], [91, 74, 39, 100, 82], [1, 86, 60, 88, 91], [2, 54, 30, 50, 11], [17, 80, 11, 83, 14], [23, 23, 82, 30, 90], [108, 50, 48, 8, 107]], ![[0, 1], [63, 107, 46, 83, 9], [19, 84, 94, 39, 38], [81, 34, 104, 63, 32], [79, 58, 28, 45, 43], [102, 80, 95, 13, 84], [69, 25, 63, 43, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 90, 3, 54], [], [], []]
 b := ![[], [12, 11, 24, 49, 96], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 5
  hpos := by decide
  P := [75, 99, 71, 1, 41, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-986782143029599110, -372768026438063389, -1243770245572271641, 110417391946574061, -1711677220520269848]
  a := ![3, 431, -805, 243, -1672]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9053047183757790, -3419890150807921, -11410736197910749, 1013003595840129, -15703460738718072]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 15386239549 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51059, -63475, 48590, -27444, 95583]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-51059, -63475, 48590, -27444, 95583]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![29, 53, 35, 1, 0], ![58, 66, 35, 0, 1]] where
  M :=![![![-51059, -63475, 48590, -27444, 95583], ![191166, 94056, -78610, 43234, -180741], ![-361482, -9341, 27407, -11908, 133911], ![38328, -239343, 170007, -98351, 282252], ![252942, 7457, -19840, 8714, -94838]]]
  hmulB := by decide  
  f := ![![![-26683, -10075, -33568, 2988, -46197]], ![![-92394, -34970, -115798, 10318, -159273]], ![![-318546, -121145, -399291, 35360, -548733]], ![![-153295, -58199, -192188, 17053, -264201]], ![![-166838, -63312, -209185, 18570, -287591]]]
  g := ![![![-42469, -43517, -20675, -27444, 95583], ![83366, 86120, 41895, 43234, -180741], ![-68876, -72711, -37546, -11908, 133911], ![-119293, -120844, -55456, -98351, 282252], ![48680, 51371, 26500, 8714, -94838]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [45, 111, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 36, 26], [52, 76, 87], [0, 1]]
 g := ![![[72, 71, 52], [104, 26], [59, 95], [43, 13], [91, 92, 11], [1]], ![[27, 33, 38, 60], [88, 15], [86, 50], [6, 83], [101, 12, 31, 22], [46, 58, 15, 61]], ![[107, 112, 92, 26], [29, 95], [9, 28], [82, 2], [17, 39, 72, 98], [77, 11, 104, 52]]]
 h' := ![![[37, 36, 26], [107, 85, 39], [70, 89, 79], [37, 36, 78], [86, 101, 37], [68, 2, 89], [0, 1]], ![[52, 76, 87], [90, 100, 89], [35, 36, 69], [17, 9, 84], [93, 31, 14], [106, 16, 36], [37, 36, 26]], ![[0, 1], [25, 41, 98], [58, 101, 78], [24, 68, 64], [18, 94, 62], [74, 95, 101], [52, 76, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 61], []]
 b := ![[], [92, 108, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [45, 111, 24, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7020485, -2282472, -9350037, 924822, -13224645]
  a := ![1, 34, -62, 20, -129]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6488399, 7270164, 3726936, 924822, -13224645]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26683, 10075, 33568, -2988, 46197]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![26683, 10075, 33568, -2988, 46197]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![49, 43, 1, 0, 0], ![20, 61, 0, 1, 0], ![102, 82, 0, 0, 1]] where
  M :=![![![26683, 10075, 33568, -2988, 46197], ![92394, 34970, 115798, -10318, 159273], ![318546, 121145, 399291, -35360, 548733], ![502536, 190827, 631293, -55883, 867876], ![57966, 21811, 73108, -6518, 100684]]]
  hmulB := by decide  
  f := ![![![51059, 63475, -48590, 27444, -95583]], ![![-191166, -94056, 78610, -43234, 180741]], ![![-47405, -8184, 8601, -4446, 26145]], ![![-94498, -37421, 32331, -17611, 78153]], ![![-94872, -11023, 13360, -6678, 45718]]]
  g := ![![![-55491, -44595, 33568, -2988, 46197], ![-191338, -153764, 115798, -10318, 159273], ![-659383, -529978, 399291, -35360, 548733], ![-1042801, -838157, 631293, -55883, 867876], ![-120918, -97171, 73108, -6518, 100684]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [71, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 112], [0, 1]]
 g := ![![[85, 97], [11], [32], [99], [68, 8], [67, 1]], ![[30, 16], [11], [32], [99], [39, 105], [21, 112]]]
 h' := ![![[67, 112], [93, 53], [14, 24], [34, 22], [31, 41], [102, 11], [0, 1]], ![[0, 1], [28, 60], [40, 89], [39, 91], [66, 72], [48, 102], [67, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [64, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [71, 46, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![375638, -2046, 532163, -89907, 841182]
  a := ![1, -178, 320, -109, 665]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-970821, -764404, 532163, -89907, 841182]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-51059, -63475, 48590, -27444, 95583]] ![![26683, 10075, 33568, -2988, 46197]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-133, -497, 1914, -138, 3105]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-133, -497, 1914, -138, 3105]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![116, 54, 1, 0, 0], ![43, 61, 0, 1, 0], ![79, 48, 0, 0, 1]] where
  M :=![![![-133, -497, 1914, -138, 3105], ![6210, -358, 7300, -1692, 12213], ![24426, 13141, 17669, -1366, 20457], ![17352, 15779, 26093, 1473, 28644], ![-3382, -2653, 4380, -80, 7594]]]
  hmulB := by decide  
  f := ![![![175277, -175127, 115968, -68690, 156675]], ![![313350, 615400, -460692, 262036, -865185]], ![![279706, 92917, -82857, 44730, -209313]], ![![224075, 236692, -183115, 103085, -367824]], ![![236947, 129808, -106952, 59070, -240341]]]
  g := ![![![-3634, -1925, 1914, -138, 3105], ![-13643, -6910, 7300, -1692, 12213], ![-28209, -14485, 17669, -1366, 20457], ![-42013, -22504, 26093, 1473, 28644], ![-8724, -4715, 4380, -80, 7594]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [59, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 126], [0, 1]]
 g := ![![[50, 121], [77, 79], [79, 64], [116, 124], [71, 19], [98, 1]], ![[97, 6], [72, 48], [1, 63], [76, 3], [28, 108], [69, 126]]]
 h' := ![![[98, 126], [29, 11], [38, 98], [14, 119], [2, 39], [60, 20], [0, 1]], ![[0, 1], [91, 116], [117, 29], [119, 8], [14, 88], [115, 107], [98, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [56, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [59, 29, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44959, 16220, 18174, -1962, 22544]
  a := ![-1, 70, -111, 53, -232]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-29605, -15178, 18174, -1962, 22544]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 4, -4, 2, -10]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![13, 4, -4, 2, -10]] 
 ![![127, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![114, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![71, 0, 0, 0, 1]] where
  M :=![![![13, 4, -4, 2, -10], ![-20, 5, -4, 2, -2], ![-4, -36, 21, -14, 38], ![48, 36, -36, 17, -72], ![0, 24, -18, 10, -31]]]
  hmulB := by decide  
  f := ![![![-117, 60, -64, 54, -170]], ![![-34, 13, -16, 14, -42]], ![![-98, 52, -55, 46, -146]], ![![-63, 48, -44, 35, -118]], ![![-69, 36, -38, 32, -101]]]
  g := ![![![7, 4, -4, 2, -10], ![2, 5, -4, 2, -2], ![-22, -36, 21, -14, 38], ![53, 36, -36, 17, -72], ![21, 24, -18, 10, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-365, -627, 472, -268, 897]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![-365, -627, 472, -268, 897]] 
 ![![127, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-365, -627, 472, -268, 897], ![1794, 1086, -884, 490, -1947], ![-3894, -573, 635, -324, 2025], ![1128, -2051, 1411, -825, 2148], ![2722, 409, -450, 230, -1426]]]
  hmulB := by decide  
  f := ![![![-1067, -845, -46, -36, 363]], ![![-616, -502, -28, -26, 219]], ![![-926, -713, -83, -24, 237]], ![![-170, -61, -69, 21, -90]], ![![-75, -58, 0, -2, 29]]]
  g := ![![![-68, -627, 472, -268, 897], ![199, 1086, -884, 490, -1947], ![-311, -573, 635, -324, 2025], ![-60, -2051, 1411, -825, 2148], ![218, 409, -450, 230, -1426]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2

def I127N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 18, -14, 8, -28]] i)))

def SI127N3: IdealEqSpanCertificate' Table ![![15, 18, -14, 8, -28]] 
 ![![127, 0, 0, 0, 0], ![92, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![15, 18, -14, 8, -28], ![-56, -27, 22, -12, 52], ![104, -2, -3, 0, -28], ![0, 78, -54, 31, -96], ![-72, 2, 2, 0, 19]]]
  hmulB := by decide  
  f := ![![![209, 98, 226, -16, 292]], ![![156, 73, 170, -12, 220]], ![![91, 40, 103, -8, 136]], ![![101, 44, 112, -9, 148]], ![![106, 50, 114, -8, 147]]]
  g := ![![![3, 18, -14, 8, -28], ![-10, -27, 22, -12, 52], ![17, -2, -3, 0, -28], ![-1, 78, -54, 31, -96], ![-12, 2, 2, 0, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N3 : Nat.card (O ⧸ I127N3) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N3)

lemma isPrimeI127N3 : Ideal.IsPrime I127N3 := prime_ideal_of_norm_prime hp127.out _ NI127N3
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-133, -497, 1914, -138, 3105]] ![![13, 4, -4, 2, -10]]
  ![![-6069, -2369, -8208, 648, -11263]] where
 M := ![![![-6069, -2369, -8208, 648, -11263]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![-6069, -2369, -8208, 648, -11263]] ![![-365, -627, 472, -268, 897]]
  ![![209, 98, 226, -16, 292]] where
 M := ![![![209, 98, 226, -16, 292]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N2 : IdealMulLeCertificate' Table 
  ![![209, 98, 226, -16, 292]] ![![15, 18, -14, 8, -28]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2, I127N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
    exact isPrimeI127N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1 ⊙ MulI127N2)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3541, 4318, -1679, 666, -5049]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![3541, 4318, -1679, 666, -5049]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![122, 71, 47, 1, 0], ![17, 0, 42, 0, 1]] where
  M :=![![![3541, 4318, -1679, 666, -5049], ![-10098, 2249, -3503, 3410, -9261], ![-18522, -28210, 11976, -5534, 35535], ![40584, -2796, 10512, -11429, 27060], ![16254, 17338, -6293, 2152, -19142]]]
  hmulB := by decide  
  f := ![![![-1369, -1346, 1045, -588, 2121]], ![![4242, 1671, -1451, 788, -3507]], ![![-7014, 782, -182, 172, 1377]], ![![-1498, -111, 153, -77, 624]], ![![-2389, 72, 78, -22, 709]]]
  g := ![![![62, -328, 1367, 666, -5049], ![-2051, -1831, 1719, 3410, -9261], ![401, 2784, -9316, -5534, 35535], ![7442, 6173, -4495, -11429, 27060], ![604, -1034, 5317, 2152, -19142]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [11, 45, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 29, 87], [0, 101, 44], [0, 1]]
 g := ![![[78, 120, 64], [126, 84, 3], [38, 77], [6, 36], [36, 114], [59, 1], []], ![[114, 85, 114, 47], [125, 50, 2, 122], [53, 64], [38, 13], [117, 12], [72, 114], [60, 102]], ![[0, 82, 105, 3], [33, 129, 61, 4], [66, 123], [13, 36], [47, 101], [114, 55], [103, 102]]]
 h' := ![![[59, 29, 87], [55, 99, 8], [76, 65, 93], [106, 110, 48], [33, 111, 125], [6, 85, 30], [0, 0, 1], [0, 1]], ![[0, 101, 44], [37, 64, 120], [72, 55, 114], [0, 103, 8], [5, 117, 12], [47, 28, 76], [70, 124, 101], [59, 29, 87]], ![[0, 1], [30, 99, 3], [31, 11, 55], [87, 49, 75], [19, 34, 125], [76, 18, 25], [46, 7, 29], [0, 101, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103, 98], []]
 b := ![[], [23, 61, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [11, 45, 72, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-810869, 1522454, -1271802, 999382, -3701328]
  a := ![0, -42, 54, -42, 112]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-456587, -530028, 818420, 999382, -3701328]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-517, 351, -223, 134, -258]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-517, 351, -223, 134, -258]] 
 ![![131, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![119, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![112, 0, 0, 0, 1]] where
  M :=![![![-517, 351, -223, 134, -258], ![-516, -1420, 1051, -600, 1926], ![3852, 2809, -2242, 1250, -4770], ![-4512, -475, 599, -297, 2112], ![-2680, -1965, 1567, -874, 3331]]]
  hmulB := by decide  
  f := ![![![5161, 2161, -109, -536, -666]], ![![2984, 1326, -107, -282, -510]], ![![4441, 1830, -79, -472, -528]], ![![1067, 172, 132, -211, 306]], ![![4576, 1903, -89, -480, -569]]]
  g := ![![![190, 351, -223, 134, -258], ![-1667, -1420, 1051, -600, 1926], ![4276, 2809, -2242, 1250, -4770], ![-2052, -475, 599, -297, 2112], ![-2985, -1965, 1567, -874, 3331]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 2, 0, 3]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![1, 1, 2, 0, 3]] 
 ![![131, 0, 0, 0, 0], ![92, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![97, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![1, 1, 2, 0, 3], ![6, 0, 10, -2, 15], ![30, 15, 23, 0, 27], ![24, 13, 43, -3, 60], ![-2, -3, 8, -2, 14]]]
  hmulB := by decide  
  f := ![![![35, -45, 44, -32, 93]], ![![26, -30, 30, -22, 63]], ![![9, -18, 17, -12, 36]], ![![25, -38, 35, -25, 75]], ![![9, -8, 8, -6, 17]]]
  g := ![![![-2, 1, 2, 0, 3], ![-5, 0, 10, -2, 15], ![-24, 15, 23, 0, 27], ![-34, 13, 43, -3, 60], ![-2, -3, 8, -2, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![3541, 4318, -1679, 666, -5049]] ![![-517, 351, -223, 134, -258]]
  ![![35, -45, 44, -32, 93]] where
 M := ![![![35, -45, 44, -32, 93]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![35, -45, 44, -32, 93]] ![![1, 1, 2, 0, 3]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![653, -84, 194, -200, 502]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![653, -84, 194, -200, 502]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![96, 115, 103, 52, 1]] where
  M :=![![![653, -84, 194, -200, 502], ![1004, 1745, -778, 384, -2290], ![-4580, -172, -901, 1104, -2234], ![-2736, -6360, 3024, -1619, 8808], ![2556, -620, 910, -876, 2407]]]
  hmulB := by decide  
  f := ![![![-3, 4, 6, 0, 10]], ![![20, -7, 34, -8, 50]], ![![100, 60, 55, 8, 58]], ![![48, 24, 144, -19, 216]], ![![108, 51, 129, -8, 175]]]
  g := ![![![-347, -422, -376, -192, 502], ![1612, 1935, 1716, 872, -2290], ![1532, 1874, 1673, 856, -2234], ![-6192, -7440, -6600, -3355, 8808], ![-1668, -2025, -1803, -920, 2407]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 4 2 7 [25, 30, 31, 42, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 4, 126, 60], [89, 111, 131, 71], [87, 21, 17, 6], [0, 1]]
 g := ![![[69, 29, 125, 98], [64, 54, 8], [60, 7, 38], [25, 70, 9, 69], [8, 30, 120], [1], []], ![[135, 122, 113, 133, 99, 118], [104, 86, 14], [63, 126, 32], [57, 54, 126, 84, 96, 76], [121, 76, 65], [66, 36, 72], [102, 98, 38]], ![[129, 111, 125, 112, 86, 125], [37, 72, 78], [5, 136, 99], [29, 40, 22, 121, 53, 45], [49, 83, 74], [128, 89, 126], [44, 50, 109]], ![[123, 6, 39, 17, 41, 79], [93, 18, 36], [47, 42, 63], [11, 118, 132, 44, 19, 125], [52, 21, 77], [55, 58, 103], [109, 62, 36]]]
 h' := ![![[56, 4, 126, 60], [14, 67, 101, 80], [45, 66, 30, 75], [60, 25, 83, 60], [14, 99, 83, 53], [112, 107, 106, 95], [0, 0, 1], [0, 1]], ![[89, 111, 131, 71], [52, 17, 18, 45], [130, 4, 30, 98], [46, 31, 46, 13], [92, 106, 134, 42], [68, 118, 106, 105], [38, 7, 89, 88], [56, 4, 126, 60]], ![[87, 21, 17, 6], [43, 49, 20, 18], [134, 32, 136, 107], [56, 54, 62, 28], [86, 85, 5, 93], [107, 8, 86, 99], [108, 63, 47, 117], [89, 111, 131, 71]], ![[0, 1], [12, 4, 135, 131], [62, 35, 78, 131], [135, 27, 83, 36], [38, 121, 52, 86], [67, 41, 113, 112], [49, 67, 0, 69], [87, 21, 17, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [117, 18, 79], []]
 b := ![[], [], [118, 136, 31, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 4
  hpos := by decide
  P := [25, 30, 31, 42, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6250072245, 2467088296, 7273823300, -629385970, 9885848886]
  a := ![13, 62, -101, 45, -211]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6881689203, -8280332362, -7379332934, -3756887066, 9885848886]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 352275361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -4, -6, 0, -10]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![3, -4, -6, 0, -10]] 
 ![![137, 0, 0, 0, 0], ![117, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![120, 0, 0, 1, 0], ![97, 0, 0, 0, 1]] where
  M :=![![![3, -4, -6, 0, -10], ![-20, 7, -34, 8, -50], ![-100, -60, -55, -8, -58], ![-48, -24, -144, 19, -216], ![12, 20, -34, 12, -59]]]
  hmulB := by decide  
  f := ![![![-653, 84, -194, 200, -502]], ![![-565, 59, -160, 168, -412]], ![![-19, 8, -9, 8, -24]], ![![-552, 120, -192, 187, -504]], ![![-481, 64, -144, 148, -373]]]
  g := ![![![11, -4, -6, 0, -10], ![25, 7, -34, 8, -50], ![103, -60, -55, -8, -58], ![168, -24, -144, 19, -216], ![17, 20, -34, 12, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![653, -84, 194, -200, 502]] ![![3, -4, -6, 0, -10]]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0, 0, 0]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]] where
  M :=![![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 5 2 7 [64, 125, 0, 135, 7, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 129, 62, 59, 100], [118, 0, 72, 58, 61], [99, 2, 36, 26, 109], [121, 7, 108, 135, 8], [0, 1]]
 g := ![![[51, 69, 19, 130, 24], [86, 131, 78, 8, 1], [17, 16, 80, 127], [49, 19, 129, 126, 131], [18, 53, 132, 1], [], []], ![[15, 111, 82, 51, 29, 72, 64, 11], [121, 123, 59, 79, 32, 133, 71, 69], [109, 122, 9, 79], [31, 79, 9, 124, 79, 121, 114, 118], [138, 93, 15, 79], [137, 92, 113, 96], [101, 133, 41, 131]], ![[84, 39, 25, 38, 61, 21, 11, 8], [128, 96, 15, 90, 118, 34, 52, 93], [97, 133, 54, 67], [53, 87, 118, 19, 23, 102, 88, 23], [38, 51, 25, 66], [23, 66, 125, 47], [30, 118, 72, 107]], ![[79, 102, 98, 22, 46, 74, 106, 115], [124, 92, 136, 13, 33, 40, 98, 97], [74, 48, 34, 127], [130, 60, 47, 65, 94, 64, 0, 72], [126, 120, 69, 63], [136, 5, 106, 118], [9, 7, 63, 66]], ![[30, 133, 121, 104, 69, 133, 48, 39], [117, 90, 129, 56, 48, 66, 86, 110], [43, 49, 123, 131], [127, 19, 111, 52, 77, 94, 109, 53], [102, 51, 137, 47], [75, 44, 111, 36], [90, 24, 44, 64]]]
 h' := ![![[72, 129, 62, 59, 100], [56, 112, 79, 26, 118], [131, 67, 50, 62, 138], [61, 97, 99, 121, 31], [99, 57, 78, 49, 100], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[118, 0, 72, 58, 61], [43, 56, 52, 7, 40], [86, 10, 130, 6, 72], [116, 111, 63, 37, 94], [80, 86, 91, 53, 38], [135, 8, 22, 74, 94], [110, 80, 65, 128, 97], [72, 129, 62, 59, 100]], ![[99, 2, 36, 26, 109], [14, 89, 26, 55, 111], [98, 126, 137, 113, 45], [107, 60, 14, 34, 22], [37, 77, 104, 47, 13], [55, 138, 33, 117, 30], [50, 96, 136, 45, 73], [118, 0, 72, 58, 61]], ![[121, 7, 108, 135, 8], [24, 95, 96, 64, 23], [45, 24, 82, 91, 125], [74, 59, 52, 53, 31], [28, 81, 72, 91, 9], [13, 97, 115, 94, 87], [51, 74, 1, 40, 102], [99, 2, 36, 26, 109]], ![[0, 1], [60, 65, 25, 126, 125], [34, 51, 18, 6, 37], [80, 90, 50, 33, 100], [10, 116, 72, 38, 118], [12, 35, 108, 132, 66], [124, 28, 75, 65, 6], [121, 7, 108, 135, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 110, 105, 67], [], [], []]
 b := ![[], [78, 113, 77, 61, 73], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 5
  hpos := by decide
  P := [64, 125, 0, 135, 7, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17980335826, -6857523022, -22330675399, 1988817838, -30659972399]
  a := ![-1, 4, -12, -1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-129354934, -49334698, -160652341, 14308042, -220575341]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 51888844699 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0, 0, 0]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![0, 0, 0, 0, 149]] where
  M :=![![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![0, 0, 0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 5 2 7 [104, 75, 92, 63, 24, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 120, 34, 46, 14], [67, 133, 12, 84, 97], [128, 62, 91, 138, 56], [65, 131, 12, 30, 131], [0, 1]]
 g := ![![[146, 126, 35, 4, 123], [134, 79, 101, 9], [31, 79, 144, 115, 4], [82, 29, 136, 129], [123, 134, 66, 125, 1], [], []], ![[33, 33, 112, 70, 40, 8, 120, 77], [40, 13, 15, 125], [90, 64, 144, 8, 123, 140, 131, 137], [121, 87, 114, 16], [114, 137, 38, 32, 32, 124, 82, 139], [104, 85, 123, 19], [24, 141, 11, 47]], ![[118, 125, 3, 137, 48, 88, 26, 134], [5, 59, 145, 76], [21, 87, 82, 103, 32, 146, 27, 89], [132, 98, 116, 29], [97, 118, 83, 24, 90, 97, 122, 62], [130, 131, 33, 148], [49, 129, 123, 22]], ![[68, 42, 49, 102, 53, 11, 79, 92], [53, 49, 83, 26], [106, 84, 53, 146, 109, 113, 117, 137], [94, 70, 88, 145], [79, 127, 104, 74, 82, 79, 63, 14], [148, 80, 87, 145], [88, 113, 90, 7]], ![[106, 140, 119, 83, 115, 31, 37, 51], [89, 47, 17, 144], [79, 8, 5, 62, 60, 2, 124, 52], [136, 109, 127, 61], [105, 124, 9, 107, 116, 17, 125, 74], [25, 69, 87, 82], [118, 92, 84, 26]]]
 h' := ![![[14, 120, 34, 46, 14], [6, 127, 0, 79, 47], [54, 42, 83, 28, 3], [2, 148, 105, 90, 2], [22, 83, 80, 117, 24], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[67, 133, 12, 84, 97], [48, 48, 93, 127, 26], [6, 19, 61, 137, 42], [64, 86, 23, 71, 130], [79, 20, 9, 124, 145], [114, 51, 43, 106, 53], [84, 8, 84, 128, 82], [14, 120, 34, 46, 14]], ![[128, 62, 91, 138, 56], [54, 50, 123, 45, 7], [96, 111, 94, 138, 134], [128, 21, 106, 127, 135], [105, 105, 55, 52, 25], [11, 29, 110, 126, 145], [138, 135, 70, 49, 105], [67, 133, 12, 84, 97]], ![[65, 131, 12, 30, 131], [97, 119, 86, 24, 17], [29, 30, 69, 59, 131], [13, 89, 67, 101, 65], [113, 46, 116, 61, 61], [97, 86, 109, 64, 74], [80, 53, 17, 99, 88], [128, 62, 91, 138, 56]], ![[0, 1], [109, 103, 145, 23, 52], [53, 96, 140, 85, 137], [20, 103, 146, 58, 115], [146, 44, 38, 93, 43], [83, 132, 36, 2, 25], [148, 102, 126, 22, 23], [65, 131, 12, 30, 131]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 133, 120, 60], [], [], []]
 b := ![[], [10, 106, 49, 3, 17], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 5
  hpos := by decide
  P := [104, 75, 92, 63, 24, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1047982709, 501479466, 1476038700, -70754289, 1952649768]
  a := ![3, -18, 28, -15, 56]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7033441, 3365634, 9906300, -474861, 13105032]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 73439775749 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15475, 926, -1552, 728, -6382]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![15475, 926, -1552, 728, -6382]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![69, 50, 135, 1, 0], ![12, 79, 110, 0, 1]] where
  M :=![![![15475, 926, -1552, 728, -6382], ![-12764, 15209, -10212, 6020, -14438], ![-28876, -50678, 38115, -21648, 72290], ![78672, 36638, -30862, 16935, -71832], ![19916, 35342, -26568, 15092, -50339]]]
  hmulB := by decide  
  f := ![![![1533, 590, 1848, -168, 2530]], ![![5060, 2027, 6332, -524, 8618]], ![![17236, 6442, 22117, -1952, 30514]], ![![17971, 6768, 22947, -2017, 31612]], ![![15348, 5809, 19598, -1712, 26975]]]
  g := ![![![277, 3104, 3988, 728, -6382], ![-1688, 5661, 5068, 6020, -14438], ![3956, -30988, -33055, -21648, 72290], ![-1509, 32216, 36983, 16935, -71832], ![-2764, 21573, 23002, 15092, -50339]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [24, 1, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 79, 16], [2, 71, 135], [0, 1]]
 g := ![![[15, 12, 100], [16, 86, 69], [147, 137, 20], [138, 29], [63, 16, 88], [95, 1], []], ![[81, 147, 100, 34], [129, 121, 39, 118], [36, 39], [3, 47], [65, 137, 92, 31], [15, 58], [121, 105]], ![[120, 24, 75, 24], [101, 127, 80, 3], [64, 127, 23, 133], [101, 72], [22, 48, 133, 77], [107, 50], [2, 105]]]
 h' := ![![[93, 79, 16], [69, 39, 10], [96, 83, 62], [14, 54, 41], [149, 80, 28], [136, 32, 115], [0, 0, 1], [0, 1]], ![[2, 71, 135], [142, 93, 126], [95, 51, 143], [38, 139], [84, 128, 97], [142, 27, 70], [7, 124, 71], [93, 79, 16]], ![[0, 1], [9, 19, 15], [101, 17, 97], [130, 109, 110], [134, 94, 26], [123, 92, 117], [107, 27, 79], [2, 71, 135]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146, 25], []]
 b := ![[], [63, 108, 140], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [24, 1, 56, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7388840, 2265958, 7579827, -1038130, 10752257]
  a := ![1, -48, 78, -35, 163]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-331174, -5266595, -6854443, -1038130, 10752257]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-487, 860, -679, 438, -1785]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-487, 860, -679, 438, -1785]] 
 ![![151, 0, 0, 0, 0], ![45, 1, 0, 0, 0], ![89, 0, 1, 0, 0], ![89, 0, 0, 1, 0], ![126, 0, 0, 0, 1]] where
  M :=![![![-487, 860, -679, 438, -1785], ![-3570, -2447, 323, 22, 1587], ![3174, -4988, 2556, -2638, 8463], ![10248, 9090, -4470, 677, -11292], ![-1302, 3980, -2731, 1784, -7444]]]
  hmulB := by decide  
  f := ![![![-915649, -684332, 544753, -303996, 1154133]], ![![-257589, -199947, 158596, -88600, 333846]], ![![-559889, -395672, 316713, -176444, 677622]], ![![-549959, -425878, 337877, -188743, 711519]], ![![-749868, -576320, 457555, -255542, 964772]]]
  g := ![![![1372, 860, -679, 438, -1785], ![-822, -2447, 323, 22, 1587], ![-5506, -4988, 2556, -2638, 8463], ![9017, 9090, -4470, 677, -11292], ![5575, 3980, -2731, 1784, -7444]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, 38, -27, 16, -53]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![27, 38, -27, 16, -53]] 
 ![![151, 0, 0, 0, 0], ![138, 1, 0, 0, 0], ![133, 0, 1, 0, 0], ![116, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![27, 38, -27, 16, -53], ![-106, -59, 55, -28, 119], ![238, 26, -10, 12, -77], ![-24, 140, -64, 51, -108], ![-154, -14, 23, -10, 76]]]
  hmulB := by decide  
  f := ![![![-1715, -1114, 257, 34, 857]], ![![-1556, -1035, 247, 22, 817]], ![![-1443, -928, 211, 32, 706]], ![![-1372, -804, 156, 59, 544]], ![![-730, -470, 107, 16, 358]]]
  g := ![![![-2, 38, -27, 16, -53], ![-21, -59, 55, -28, 119], ![8, 26, -10, 12, -77], ![-68, 140, -64, 51, -108], ![-31, -14, 23, -10, 76]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![15475, 926, -1552, 728, -6382]] ![![-487, 860, -679, 438, -1785]]
  ![![1715, 1114, -257, -34, -857]] where
 M := ![![![1715, 1114, -257, -34, -857]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![1715, 1114, -257, -34, -857]] ![![27, 38, -27, 16, -53]]
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


lemma PB251I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB251I3 : PrimesBelowBoundCertificateInterval O 103 151 251 where
  m := 9
  g := ![2, 1, 2, 4, 3, 2, 1, 1, 3]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB251I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2, I127N3]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0, I137N1]
    · exact ![I139N0]
    · exact ![I149N0]
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
    · exact ![131079601, 107]
    · exact ![15386239549]
    · exact ![1442897, 12769]
    · exact ![16129, 127, 127, 127]
    · exact ![2248091, 131, 131]
    · exact ![352275361, 137]
    · exact ![51888844699]
    · exact ![73439775749]
    · exact ![3442951, 151, 151]
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
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
      exact NI127N3
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
  β := ![I107N1, I127N1, I127N2, I127N3, I131N1, I131N2, I137N1, I151N1, I151N2]
  Il := ![[I107N1], [], [], [I127N1, I127N2, I127N3], [I131N1, I131N2], [I137N1], [], [], [I151N1, I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
