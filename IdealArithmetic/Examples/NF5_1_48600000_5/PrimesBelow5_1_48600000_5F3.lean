
import IdealArithmetic.Examples.NF5_1_48600000_5.RI5_1_48600000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-103, -140, 140, -40, -60]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-103, -140, 140, -40, -60]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![71, 13, 89, 1, 0], ![81, 65, 81, 0, 1]] where
  M :=![![![-103, -140, 140, -40, -60], ![200, 257, -480, 200, -120], ![-80, 360, 337, -280, 720], ![-540, -2080, 1040, -43, -1500], ![620, 1760, -1460, 360, 737]]]
  hmulB := by decide  
  f := ![![![-269, -380, -20, 120, 180]], ![![-600, -949, -160, 200, 360]], ![![-560, -1080, -389, 40, 240]], ![![-717, -1271, -363, 133, 360]], ![![-987, -1675, -407, 240, 533]]]
  g := ![![![71, 40, 80, -40, -60], ![-40, 51, -80, 200, -120], ![-360, -400, -309, -280, 720], ![1159, 897, 1181, -43, -1500], ![-791, -475, -871, 360, 737]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [98, 38, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 98, 44], [12, 8, 63], [0, 1]]
 g := ![![[90, 39, 44], [11, 3, 9], [17, 37], [53, 98, 92], [88, 86], [1]], ![[14, 3, 87, 14], [86, 18, 62, 36], [61, 34], [9, 72, 76, 34], [10, 3], [48, 22, 71, 12]], ![[93, 27, 22, 88], [15, 97, 69, 93], [84, 53], [11, 39, 57, 5], [32, 29], [78, 82, 6, 95]]]
 h' := ![![[61, 98, 44], [99, 19, 77], [93, 105, 3], [49, 13, 12], [17, 63, 29], [9, 69, 73], [0, 1]], ![[12, 8, 63], [100, 49, 61], [44, 103, 43], [64, 9, 26], [36, 5, 8], [38, 92, 89], [61, 98, 44]], ![[0, 1], [8, 39, 76], [26, 6, 61], [33, 85, 69], [72, 39, 70], [76, 53, 52], [12, 8, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 77], []]
 b := ![[], [21, 64, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [98, 38, 34, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![110466, 33852, 13076, -85292, -212856]
  a := ![5, -7, -8, -8, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![218762, 139984, 232200, -85292, -212856]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-269, -380, -20, 120, 180]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-269, -380, -20, 120, 180]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![83, 18, 1, 0, 0], ![4, 39, 0, 1, 0], ![33, 69, 0, 0, 1]] where
  M :=![![![-269, -380, -20, 120, 180], ![-600, -949, -160, 200, 360], ![-560, -1080, -389, 40, 240], ![20, -560, -720, -449, -300], ![540, 720, -20, -280, -389]]]
  hmulB := by decide  
  f := ![![![-103, -140, 140, -40, -60]], ![![200, 257, -480, 200, -120]], ![![-47, -62, 31, 0, -60]], ![![64, 69, -160, 71, -60]], ![![103, 139, -280, 120, -89]]]
  g := ![![![-47, -160, -20, 120, 180], ![0, -287, -160, 200, 360], ![221, -114, -389, 40, 240], ![668, 473, -720, -449, -300], ![151, 363, -20, -280, -389]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P1 : CertificateIrreducibleZModOfList' 107 2 2 6 [91, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 106], [0, 1]]
 g := ![![[48, 90], [87, 53], [100], [64, 49], [33], [19, 1]], ![[46, 17], [24, 54], [100], [32, 58], [33], [38, 106]]]
 h' := ![![[19, 106], [1, 25], [78, 38], [61, 97], [68, 7], [90, 56], [0, 1]], ![[0, 1], [48, 82], [51, 69], [85, 10], [94, 100], [84, 51], [19, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [65, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N1 : CertifiedPrimeIdeal' SI107N1 107 where
  n := 2
  hpos := by decide
  P := [91, 88, 1]
  hirr := P107P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![125, 56308, -52763, 57211, 59997]
  a := ![-6, -56, 11, -57, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![20287, -50140, -52763, 57211, 59997]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N1 B_one_repr
lemma NI107N1 : Nat.card (O ⧸ I107N1) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-103, -140, 140, -40, -60]] ![![-269, -380, -20, 120, 180]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 5 2 6 [84, 76, 20, 20, 105, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 4, 21, 35, 103], [44, 91, 33, 35, 26], [66, 62, 84, 80, 2], [55, 60, 80, 68, 87], [0, 1]]
 g := ![![[11, 2, 87, 6, 81], [25, 89, 42, 31], [44, 95, 102, 53, 43], [33, 11, 105, 101, 16], [4, 1], []], ![[82, 24, 4, 57, 37, 5, 92, 17], [15, 73, 61, 36], [45, 75, 55, 49, 20, 72, 51, 52], [30, 52, 44, 62, 41, 38, 38, 67], [95, 64, 31, 27], [90, 49, 70, 105, 84, 17, 82, 2]], ![[63, 38, 8, 52, 11, 42, 41, 35], [97, 22, 85, 60], [33, 39, 81, 60, 50, 56, 23, 27], [17, 14, 98, 82, 20, 96, 66, 27], [95, 30, 14, 97], [79, 92, 99, 37, 35, 40, 20, 27]], ![[29, 80, 74, 33, 26, 51, 18, 50], [65, 47, 44, 5], [56, 40, 35, 69, 48, 54, 81, 92], [84, 86, 97, 40, 28, 54, 40, 77], [48, 32, 106, 28], [29, 7, 102, 18, 34, 52, 11, 8]], ![[70, 88, 90, 6, 89, 54, 78, 28], [42, 77, 58, 38], [46, 35, 5, 39, 18, 44, 96, 93], [30, 9, 35, 47, 102, 9, 77, 60], [91, 48, 38, 43], [39, 5, 108, 51, 97, 101, 9, 34]]]
 h' := ![![[57, 4, 21, 35, 103], [71, 55, 14, 54, 100], [10, 41, 102, 21, 24], [62, 28, 47, 85, 32], [100, 48, 62, 9, 105], [0, 0, 0, 1], [0, 1]], ![[44, 91, 33, 35, 26], [74, 9, 15, 58, 52], [35, 90, 21, 16, 103], [0, 92, 53, 42, 8], [38, 59, 27, 42, 15], [72, 19, 37, 75, 38], [57, 4, 21, 35, 103]], ![[66, 62, 84, 80, 2], [73, 81, 108, 44, 100], [68, 74, 46, 94, 96], [48, 96, 104, 97, 26], [23, 100, 2, 68, 83], [68, 98, 89, 93, 73], [44, 91, 33, 35, 26]], ![[55, 60, 80, 68, 87], [68, 104, 26, 11, 104], [29, 31, 32, 15, 88], [107, 69, 103, 86, 68], [81, 93, 57, 98, 86], [25, 61, 68, 98, 30], [66, 62, 84, 80, 2]], ![[0, 1], [73, 78, 55, 51, 80], [2, 91, 17, 72, 16], [59, 42, 20, 17, 84], [12, 27, 70, 1, 38], [35, 40, 24, 60, 77], [55, 60, 80, 68, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 31, 4, 54], [], [], []]
 b := ![[], [60, 76, 81, 108, 9], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 5
  hpos := by decide
  P := [84, 76, 20, 20, 105, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-98711272, -115681264, 76803144, 39741400, 75701808]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-905608, -1061296, 704616, 364600, 694512]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18, 44, -56, 20, -1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![18, 44, -56, 20, -1]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![65, 28, 1, 0, 0], ![101, 40, 0, 1, 0], ![57, 92, 0, 0, 1]] where
  M :=![![![18, 44, -56, 20, -1], ![-38, 7, 126, -72, 122], ![-50, -333, 57, 54, -338], ![303, 899, -680, 147, 439], ![-261, -556, 642, -214, -74]]]
  hmulB := by decide  
  f := ![![![-124, 16, 190, 166, 145]], ![![-622, -327, 654, 712, 706]], ![![-238, -81, 281, 284, 271]], ![![-353, -121, 414, 419, 400]], ![![-569, -260, 626, 662, 647]]]
  g := ![![![15, 8, -56, 20, -1], ![-70, -105, 126, -72, 122], ![89, 239, 57, 54, -338], ![41, -233, -680, 147, 439], ![-143, -28, 642, -214, -74]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [41, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 112], [0, 1]]
 g := ![![[87, 102], [25], [8], [111], [60, 56], [49, 1]], ![[0, 11], [25], [8], [111], [92, 57], [98, 112]]]
 h' := ![![[49, 112], [101, 21], [83, 5], [80, 11], [26, 26], [25, 100], [0, 1]], ![[0, 1], [0, 92], [102, 108], [54, 102], [57, 87], [66, 13], [49, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [47, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [41, 64, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15664, -10840, 12697, 13340, 16822]
  a := ![-8, 27, 13, 26, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-27851, -21660, 12697, 13340, 16822]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48986, 10799, 2882, -2334, -9143]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-48986, 10799, 2882, -2334, -9143]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![40, 77, 1, 0, 0], ![84, 24, 0, 1, 0], ![15, 5, 0, 0, 1]] where
  M :=![![![-48986, 10799, 2882, -2334, -9143], ![22954, -5057, -1356, 1096, 4282], ![-5378, 1190, 321, -260, -994], ![-10223, 2225, 614, -487, -1927], ![-17975, 3989, 1038, -852, -3346]]]
  hmulB := by decide  
  f := ![![![-1896, -2345, 290, 1116, 1451]], ![![-5134, -6629, 444, 2812, 3794]], ![![-4228, -5427, 405, 2340, 3140]], ![![-2547, -3225, 298, 1443, 1913]], ![![-449, -569, 52, 254, 337]]]
  g := ![![![1495, -968, 2882, -2334, -9143], ![-700, 457, -1356, 1096, 4282], ![164, -109, 321, -260, -994], ![310, -210, 614, -487, -1927], ![551, -343, 1038, -852, -3346]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [23, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 112], [0, 1]]
 g := ![![[106, 106], [60], [52], [77], [112, 102], [48, 1]], ![[109, 7], [60], [52], [77], [36, 11], [96, 112]]]
 h' := ![![[48, 112], [20, 28], [48, 88], [1, 39], [23, 90], [26, 21], [0, 1]], ![[0, 1], [8, 85], [91, 25], [65, 74], [49, 23], [17, 92], [48, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [112, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [23, 65, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3741, 7292, -11162, 4838, -114]
  a := ![-6, -4, 10, -14, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![403, 6648, -11162, 4838, -114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-136198, 30031, 8008, -6488, -25419]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-136198, 30031, 8008, -6488, -25419]] 
 ![![113, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![98, 0, 1, 0, 0], ![112, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![-136198, 30031, 8008, -6488, -25419], ![63814, -14071, -3752, 3040, 11910], ![-14950, 3296, 879, -712, -2790], ![-28405, 6263, 1670, -1353, -5301], ![-50001, 11025, 2940, -2382, -9332]]]
  hmulB := by decide  
  f := ![![![72, 19, -32, -122, -93]], ![![14, 5, -8, -20, -18]], ![![70, 26, -33, -112, -84]], ![![79, 21, -30, -131, -105]], ![![27, 11, -16, -40, -32]]]
  g := ![![![3026, 30031, 8008, -6488, -25419], ![-1418, -14071, -3752, 3040, 11910], ![332, 3296, 879, -712, -2790], ![631, 6263, 1670, -1353, -5301], ![1111, 11025, 2940, -2382, -9332]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![18, 44, -56, 20, -1]] ![![-48986, 10799, 2882, -2334, -9143]]
  ![![242911, -54255, -14522, 11884, 44304]] where
 M := ![![![242911, -54255, -14522, 11884, 44304]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![242911, -54255, -14522, 11884, 44304]] ![![-136198, 30031, 8008, -6488, -25419]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![-38881926372, 8573298926, 2286131250, -1852213284, -7256657391]]]
 hmul := by decide  
 g := ![![![![-344087844, 75869902, 20231250, -16391268, -64218207]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 5 2 6 [9, 120, 6, 51, 45, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 2, 1, 62, 114], [92, 20, 97, 22, 96], [110, 78, 126, 22, 38], [29, 26, 30, 21, 6], [0, 1]]
 g := ![![[73, 126, 27, 59, 64], [96, 63, 57, 27, 49], [90, 66, 18, 89, 49], [107, 109, 36, 95, 122], [69, 82, 1], []], ![[28, 125, 53, 31, 70, 28, 4, 33], [27, 94, 53, 44, 49, 12, 119, 126], [102, 120, 97, 1, 92, 126, 118, 40], [51, 64, 32, 109, 124, 64, 61, 90], [54, 30, 103, 114, 104, 50, 19, 86], [68, 95, 66, 24, 22, 111, 124, 89]], ![[8, 106, 96, 75, 83, 88, 95, 67], [18, 49, 57, 124, 11, 23, 63, 55], [23, 95, 13, 17, 108, 95, 86, 112], [17, 28, 43, 96, 29, 37, 35, 78], [123, 99, 60, 91, 5, 101, 9, 108], [9, 28, 125, 126, 64, 14, 36, 54]], ![[4, 12, 20, 118, 59, 94, 104, 11], [89, 44, 51, 26, 110, 9, 60, 104], [97, 96, 35, 79, 22, 42], [103, 118, 27, 126, 80, 89, 8, 36], [26, 5, 107, 60, 0, 86, 43, 47], [65, 29, 4, 71, 37, 71, 75, 8]], ![[45, 23, 39, 101, 103, 24, 13, 110], [114, 88, 4, 81, 67, 71, 87, 56], [3, 86, 37, 68, 111, 101, 88, 114], [69, 19, 4, 83, 119, 104, 126, 125], [105, 54, 68, 105, 108, 7, 120, 33], [103, 19, 23, 73, 36, 95, 41, 89]]]
 h' := ![![[105, 2, 1, 62, 114], [25, 123, 44, 17, 8], [79, 51, 8, 105, 7], [53, 91, 23, 55, 7], [14, 126, 24, 60, 73], [0, 0, 0, 1], [0, 1]], ![[92, 20, 97, 22, 96], [107, 54, 43, 71, 115], [56, 119, 68, 53, 71], [5, 24, 80, 68, 121], [111, 55, 23, 37, 9], [43, 112, 89, 124, 59], [105, 2, 1, 62, 114]], ![[110, 78, 126, 22, 38], [43, 122, 116, 3, 38], [22, 30, 35, 82, 44], [75, 24, 13, 124, 19], [32, 80, 27, 6, 55], [97, 32, 56, 96, 115], [92, 20, 97, 22, 96]], ![[29, 26, 30, 21, 6], [26, 42, 7, 62, 115], [101, 67, 65, 112, 105], [54, 59, 16, 71], [115, 88, 53, 5, 104], [90, 2, 30, 23, 66], [110, 78, 126, 22, 38]], ![[0, 1], [120, 40, 44, 101, 105], [28, 114, 78, 29, 27], [19, 56, 122, 63, 107], [29, 32, 0, 19, 13], [94, 108, 79, 10, 14], [29, 26, 30, 21, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 4, 106, 90], [], [], []]
 b := ![[], [126, 87, 80, 119, 46], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 5
  hpos := by decide
  P := [9, 120, 6, 51, 45, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-99696049274, -127978761060, -13994418544, 66325089346, 74734346086]
  a := ![-6, 19, 16, 20, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-785008262, -1007706780, -110192272, 522244798, 588459418]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![404817, -89260, -23802, 19284, 75552]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![404817, -89260, -23802, 19284, 75552]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![77, 84, 1, 0, 0], ![82, 57, 0, 1, 0], ![12, 74, 0, 0, 1]] where
  M :=![![![404817, -89260, -23802, 19284, 75552], ![-189672, 41823, 11152, -9036, -35400], ![44436, -9796, -2613, 2116, 8292], ![84428, -18614, -4964, 4021, 15756], ![148616, -32770, -8738, 7080, 27737]]]
  hmulB := by decide  
  f := ![![![-37, -4, 26, 28, 72]], ![![-200, -315, 192, 108, 24]], ![![-151, -204, 137, 88, 60]], ![![-114, -143, 104, 65, 60]], ![![-116, -180, 110, 64, 17]]]
  g := ![![![-1911, -36488, -23802, 19284, 75552], ![896, 17097, 11152, -9036, -35400], ![-209, -4004, -2613, 2116, 8292], ![-398, -7609, -4964, 4021, 15756], ![-702, -13396, -8738, 7080, 27737]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [92, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 130], [0, 1]]
 g := ![![[103, 46], [11, 84], [63], [34], [63], [102], [1]], ![[44, 85], [114, 47], [63], [34], [63], [102], [1]]]
 h' := ![![[87, 130], [36, 35], [16, 79], [21, 71], [108, 77], [128, 71], [39, 87], [0, 1]], ![[0, 1], [68, 96], [77, 52], [41, 60], [126, 54], [17, 60], [10, 44], [87, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [11, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [92, 44, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![351, 624, -827, 292, 262]
  a := ![-2, -3, 3, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![282, 260, -827, 292, 262]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1191, -7445, 1528, 1066, -7320]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-1191, -7445, 1528, 1066, -7320]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![36, 109, 1, 0, 0], ![6, 124, 0, 1, 0], ![26, 47, 0, 0, 1]] where
  M :=![![![-1191, -7445, 1528, 1066, -7320], ![12508, 39069, -27398, 5188, 21036], ![-26224, -54847, 65293, -22210, -5472], ![21428, -8530, -68830, 40489, -71676], ![7428, 70947, -2418, -16914, 80645]]]
  hmulB := by decide  
  f := ![![![-925033, 204493, 54226, -44414, -173100]], ![![435028, -94135, -26042, 19624, 79716]], ![![107004, -21940, -6727, 4074, 18600]], ![![367962, -79390, -22086, 16457, 67236]], ![![-30114, 7380, 1574, -1894, -6235]]]
  g := ![![![975, 289, 1528, 1066, -7320], ![3212, 10637, -27398, 5188, 21036], ![-16040, -31760, 65293, -22210, -5472], ![31450, 44596, -68830, 40489, -71676], ![-14510, -10370, -2418, -16914, 80645]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [16, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 130], [0, 1]]
 g := ![![[58, 41], [51, 65], [60], [75], [45], [121], [1]], ![[0, 90], [122, 66], [60], [75], [45], [121], [1]]]
 h' := ![![[120, 130], [101, 33], [18, 14], [42, 86], [71, 59], [23, 69], [115, 120], [0, 1]], ![[0, 1], [0, 98], [126, 117], [13, 45], [77, 72], [50, 62], [105, 11], [120, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [9, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [16, 11, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1098, -2957, -4478, 5948, -2742]
  a := ![-10, 9, 20, 5, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1494, -943, -4478, 5948, -2742]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![519, 651, -72, -302, -396]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![519, 651, -72, -302, -396]] 
 ![![131, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![95, 0, 0, 0, 1]] where
  M :=![![![519, 651, -72, -302, -396], ![1396, 1823, -94, -748, -1020], ![1768, 2453, 55, -842, -1224], ![1368, 2218, 434, -413, -792], ![-936, -1125, 182, 574, 731]]]
  hmulB := by decide  
  f := ![![![329, 2013, -586, -190, 1800]], ![![-7, 34, 24, -22, 60]], ![![151, 724, -305, -16, 564]], ![![257, 1809, -404, -239, 1728]], ![![217, 1310, -402, -112, 1151]]]
  g := ![![![544, 651, -72, -302, -396], ![1339, 1823, -94, -748, -1020], ![1492, 2453, 55, -842, -1224], ![693, 2218, 434, -413, -792], ![-1038, -1125, 182, 574, 731]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![404817, -89260, -23802, 19284, 75552]] ![![-1191, -7445, 1528, 1066, -7320]]
  ![![329, 2013, -586, -190, 1800]] where
 M := ![![![329, 2013, -586, -190, 1800]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![329, 2013, -586, -190, 1800]] ![![519, 651, -72, -302, -396]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-744, 171, 46, -36, -141]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-744, 171, 46, -36, -141]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![76, 25, 1, 0, 0], ![18, 30, 0, 1, 0], ![76, 9, 0, 0, 1]] where
  M :=![![![-744, 171, 46, -36, -141], ![354, -65, -12, 20, 66], ![-86, 26, 21, 8, -6], ![-179, 23, 34, 19, -3], ![-283, 47, 14, -10, -46]]]
  hmulB := by decide  
  f := ![![![22, 83, -42, 2, 57]], ![![-118, -301, 284, -80, -102]], ![![-8, -7, 25, -12, 12]], ![![-23, -51, 58, -19, -9]], ![![3, 20, -2, -4, 20]]]
  g := ![![![52, 10, 46, -36, -141], ![-30, -7, -12, 20, 66], ![-10, -5, 21, 8, -6], ![-21, -10, 34, 19, -3], ![17, 3, 14, -10, -46]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [44, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 136], [0, 1]]
 g := ![![[22, 109], [99], [100], [67, 9], [133], [81], [1]], ![[0, 28], [99], [100], [123, 128], [133], [81], [1]]]
 h' := ![![[128, 136], [46, 66], [93, 109], [66, 127], [21, 134], [16, 63], [93, 128], [0, 1]], ![[0, 1], [0, 71], [71, 28], [19, 10], [48, 3], [134, 74], [37, 9], [128, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [127, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [44, 9, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1447, -2573, 442, 1730, -339]
  a := ![-6, 7, 9, 6, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-295, -456, 442, 1730, -339]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-685336736, 151113823, 40295582, -32647298, -127906573]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-685336736, 151113823, 40295582, -32647298, -127906573]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![78, 134, 1, 0, 0], ![97, 99, 0, 1, 0], ![16, 15, 0, 0, 1]] where
  M :=![![![-685336736, 151113823, 40295582, -32647298, -127906573], ![321107742, -70802885, -18880096, 15296568, 59929358], ![-75225926, 16586996, 4423041, -3583528, -14039654], ![-142930689, 31515607, 8403862, -6808771, -26675609], ![-251601161, 55476981, 14793334, -11985492, -46957124]]]
  hmulB := by decide  
  f := ![![![10, -293, -186, 256, -491]], ![![470, 2791, -1056, 140, 2518]], ![![446, 2516, -1099, 276, 2168]], ![![367, 1841, -960, 315, 1458]], ![![45, 284, -110, 26, 258]]]
  g := ![![![10108766, -713964, 40295582, -32647298, -127906573], ![-4736362, 334521, -18880096, 15296568, 59929358], ![1109588, -78368, 4423041, -3583528, -14039654], ![2108238, -148901, 8403862, -6808771, -26675609], ![3711135, -262111, 14793334, -11985492, -46957124]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P1 : CertificateIrreducibleZModOfList' 137 2 2 7 [78, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [126, 136], [0, 1]]
 g := ![![[30, 65], [37], [60], [112, 2], [128], [121], [1]], ![[0, 72], [37], [60], [90, 135], [128], [121], [1]]]
 h' := ![![[126, 136], [59, 105], [43, 41], [32, 103], [126, 106], [71, 111], [59, 126], [0, 1]], ![[0, 1], [0, 32], [3, 96], [132, 34], [56, 31], [83, 26], [43, 11], [126, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132]]
 b := ![[], [89, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N1 : CertifiedPrimeIdeal' SI137N1 137 where
  n := 2
  hpos := by decide
  P := [78, 11, 1]
  hirr := P137P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2050, -2222, 1682, 1562, 1588]
  a := ![-3, 8, 6, 9, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2264, -2964, 1682, 1562, 1588]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N1 B_one_repr
lemma NI137N1 : Nat.card (O ⧸ I137N1) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48826, -132266, 112822, -28728, -53221]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![-48826, -132266, 112822, -28728, -53221]] 
 ![![137, 0, 0, 0, 0], ![93, 1, 0, 0, 0], ![128, 0, 1, 0, 0], ![98, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![-48826, -132266, 112822, -28728, -53221], ![163898, 272645, -428430, 168188, -65926], ![-102262, 200737, 374907, -260242, 570490], ![-392197, -1686467, 725200, 30571, -1318253], ![523139, 1524508, -1177668, 262842, 723478]]]
  hmulB := by decide  
  f := ![![![313944, 746162, 387424, 79890, -68843]], ![![212954, 515317, 274050, 61054, -42229]], ![![281994, 698153, 382097, 92518, -48358]], ![![190815, 511721, 306456, 91737, -13831]], ![![139171, 335740, 177754, 39056, -28170]]]
  g := ![![![29432, -132266, 112822, -28728, -53221], ![126889, 272645, -428430, 168188, -65926], ![-567639, 200737, 374907, -260242, 570490], ![1058364, -1686467, 725200, 30571, -1318253], ![-456757, 1524508, -1177668, 262842, 723478]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-744, 171, 46, -36, -141]] ![![-685336736, 151113823, 40295582, -32647298, -127906573]]
  ![![601960831375, -132729792004, -35393348664, 28675530680, 112345862854]] where
 M := ![![![601960831375, -132729792004, -35393348664, 28675530680, 112345862854]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![601960831375, -132729792004, -35393348664, 28675530680, 112345862854]] ![![-48826, -132266, 112822, -28728, -53221]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-47140034628, 10394176574, 2771681250, -2245603716, -8797894359]]]
 hmul := by decide  
 g := ![![![![-344087844, 75869902, 20231250, -16391268, -64218207]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-58, 10, 184, -104, 177]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-58, 10, 184, -104, 177]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![57, 110, 78, 107, 1]] where
  M :=![![![-58, 10, 184, -104, 177], ![-146, -967, 166, 160, -978], ![818, 2615, -1785, 326, 1458], ![-1711, -3319, 4316, -1539, 9], ![837, 474, -2454, 1242, -1646]]]
  hmulB := by decide  
  f := ![![![156, -22, -10, 2, 21]], ![![-46, 45, 2, -16, -30]], ![![46, 37, -1, -14, -18]], ![![55, 31, 4, -7, -9]], ![![96, 71, 0, -25, -32]]]
  g := ![![![-73, -140, -98, -137, 177], ![400, 767, 550, 754, -978], ![-592, -1135, -831, -1120, 1458], ![-16, -31, 26, -18, 9], ![681, 1306, 906, 1276, -1646]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 4 2 7 [111, 138, 27, 121, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [101, 127, 92, 86], [52, 75, 105, 96], [4, 75, 81, 96], [0, 1]]
 g := ![![[88, 117, 5, 45], [116, 116, 12, 79], [87, 12, 121], [5, 38, 12, 45], [128, 134, 46], [1], []], ![[99, 6, 101, 13, 83, 67], [34, 84, 79, 13, 47, 107], [33, 22, 28], [135, 53, 96, 7, 81, 1], [82, 27, 121], [84, 37, 16], [22, 83, 29]], ![[125, 46, 110, 137, 22, 25], [5, 53, 33, 16, 76, 29], [90, 4, 57], [70, 27, 61, 100, 43, 117], [106, 31, 7], [62, 25, 64], [42, 66, 42]], ![[17, 45, 74, 126, 61, 46], [52, 133, 6, 22, 106, 49], [38, 128, 116], [14, 42, 6, 104, 115, 64], [4], [70, 103, 5], [65, 45, 42]]]
 h' := ![![[101, 127, 92, 86], [51, 83, 44, 103], [74, 71, 77, 45], [1, 102, 10, 128], [59, 44, 69, 103], [28, 1, 112, 18], [0, 0, 1], [0, 1]], ![[52, 75, 105, 96], [69, 6, 43, 20], [119, 40, 32, 33], [53, 69, 27, 58], [100, 53, 136, 102], [58, 16, 136, 11], [114, 61, 125, 4], [101, 127, 92, 86]], ![[4, 75, 81, 96], [53, 134, 104, 76], [138, 118, 25, 84], [113, 23, 106, 125], [96, 101, 60, 7], [73, 54, 28, 110], [127, 99, 112, 8], [52, 75, 105, 96]], ![[0, 1], [115, 55, 87, 79], [73, 49, 5, 116], [11, 84, 135, 106], [136, 80, 13, 66], [21, 68, 2], [29, 118, 40, 127], [4, 75, 81, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [83, 48, 38], []]
 b := ![[], [], [26, 84, 119, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 4
  hpos := by decide
  P := [111, 138, 27, 121, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1807393661, 4582139000, -4301376615, 1176936869, 1542288727]
  a := ![16, -7, -33, -7, -41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-619446502, -1187551230, -896402139, -1178762280, 1542288727]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 373301041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![156, -22, -10, 2, 21]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![156, -22, -10, 2, 21]] 
 ![![139, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![86, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![156, -22, -10, 2, 21], ![-46, 45, 2, -16, -30], ![46, 37, -1, -14, -18], ![55, 31, 4, -7, -9], ![39, -30, 0, 12, 22]]]
  hmulB := by decide  
  f := ![![![-58, 10, 184, -104, 177]], ![![-24, -3, 74, -40, 63]], ![![-30, 25, 101, -62, 120]], ![![-29, -21, 84, -41, 51]], ![![-9, 6, 30, -18, 34]]]
  g := ![![![10, -22, -10, 2, 21], ![-7, 45, 2, -16, -30], ![-5, 37, -1, -14, -18], ![-10, 31, 4, -7, -9], ![3, -30, 0, 12, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-58, 10, 184, -104, 177]] ![![156, -22, -10, 2, 21]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3069108353, 676725277, 180453638, -146202718, -572797442]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-3069108353, 676725277, 180453638, -146202718, -572797442]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![42, 94, 28, 32, 1]] where
  M :=![![![-3069108353, 676725277, 180453638, -146202718, -572797442], ![1438000320, -317072941, -84549766, 68501840, 268378576], ![-336880416, 74280677, 19807475, -16047926, -62873056], ![-640079178, 141134714, 37634578, -30491371, -119460010], ![-1126732566, 248439727, 66248228, -53674018, -210285685]]]
  hmulB := by decide  
  f := ![![![-133, -199, 352, -146, 86]], ![![120, -503, -518, 412, -1048]], ![![636, 2833, -1139, -106, 2284]], ![![-2238, -5816, 5270, -1451, -2078]], ![![-312, -1071, 662, -102, -657]]]
  g := ![![![140861639, 365903925, 108850886, 122035674, -572797442], ![-65999328, -171440665, -51001006, -57178608, 268378576], ![15461664, 40163409, 11948007, 13395234, -62873056], ![29377458, 76311246, 22701442, 25451201, -119460010], ![51713196, 134330833, 39961392, 44801798, -210285685]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 4 2 7 [99, 106, 71, 48, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 134, 98, 75], [120, 84, 31, 140], [140, 79, 20, 83], [0, 1]]
 g := ![![[119, 23, 10, 133], [31, 120, 63], [42, 90, 17, 9], [118, 49, 36], [114, 66, 77, 69], [1], []], ![[87, 83, 57, 27, 142, 55], [9, 79, 25], [74, 129, 15, 77, 31, 38], [95, 141, 116], [105, 37, 51, 23, 106, 115], [86, 103, 4], [42, 86, 112]], ![[24, 92, 47, 18, 145, 80], [23, 95, 88], [91, 133, 111, 67, 23, 69], [67, 43, 100], [142, 43, 30, 69, 80, 124], [104, 147, 123], [145, 24, 81]], ![[141, 41, 95, 77, 88, 2], [103, 75, 143], [96, 30, 72, 82, 65, 101], [48, 103, 35], [82, 107, 73, 127, 15, 66], [101, 122, 88], [104, 1, 35]]]
 h' := ![![[139, 134, 98, 75], [107, 104, 146, 27], [14, 109, 129, 130], [43, 35, 99, 146], [38, 123, 63, 143], [50, 43, 78, 101], [0, 0, 1], [0, 1]], ![[120, 84, 31, 140], [42, 144, 118, 109], [121, 19, 36, 144], [55, 81, 55, 134], [85, 98, 4, 99], [12, 127, 141, 140], [114, 148, 111, 2], [139, 134, 98, 75]], ![[140, 79, 20, 83], [4, 119, 37, 16], [33, 109, 96, 45], [65, 20, 35, 41], [69, 144, 108, 139], [73, 69, 54, 101], [45, 30, 45, 102], [120, 84, 31, 140]], ![[0, 1], [104, 80, 146, 146], [13, 61, 37, 128], [77, 13, 109, 126], [106, 82, 123, 66], [19, 59, 25, 105], [66, 120, 141, 45], [140, 79, 20, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [135, 109, 64], []]
 b := ![[], [], [132, 113, 148, 123], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 4
  hpos := by decide
  P := [99, 106, 71, 48, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![52821811, 95021192, -138829876, 51134308, -10149902]
  a := ![7, -4, -13, -5, -20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3215555, 7041020, 975620, 2523028, -10149902]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 492884401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-133, -199, 352, -146, 86]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-133, -199, 352, -146, 86]] 
 ![![149, 0, 0, 0, 0], ![108, 1, 0, 0, 0], ![128, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![87, 0, 0, 0, 1]] where
  M :=![![![-133, -199, 352, -146, 86], ![120, -503, -518, 412, -1048], ![636, 2833, -1139, -106, 2284], ![-2238, -5816, 5270, -1451, -2078], ![1626, 2849, -4202, 1606, -449]]]
  hmulB := by decide  
  f := ![![![-3069108353, 676725277, 180453638, -146202718, -572797442]], ![![-2214937596, 488384275, 130231162, -105512696, -413380840]], ![![-2638810400, 581846417, 155153511, -125704670, -492489568]], ![![-766423411, 168993087, 45063216, -36510013, -143040036]], ![![-1799591673, 396802274, 105810166, -85726916, -335863511]]]
  g := ![![![-173, -199, 352, -146, 86], ![1320, -503, -518, 412, -1048], ![-2378, 2833, -1139, -106, 2284], ![1247, -5816, 5270, -1451, -2078], ![1419, 2849, -4202, 1606, -449]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-3069108353, 676725277, 180453638, -146202718, -572797442]] ![![-133, -199, 352, -146, 86]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![149, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![44554730, -9824128, -2619674, 2122448, 8315391]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![44554730, -9824128, -2619674, 2122448, 8315391]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![60, 132, 44, 1, 0], ![56, 51, 89, 0, 1]] where
  M :=![![![44554730, -9824128, -2619674, 2122448, 8315391], ![-20875678, 4602997, 1227422, -994452, -3896094], ![4890546, -1078345, -287549, 232970, 912738], ![9292131, -2048875, -546348, 442647, 1734219], ![16356955, -3606638, -961736, 779194, 3052750]]]
  hmulB := by decide  
  f := ![![![-4, 36, -32, 6, 63]], ![![-138, -339, 210, -52, -90]], ![![142, 209, -481, 158, -66]], ![![-81, -219, 32, 1, -69]], ![![35, 18, -223, 78, -50]]]
  g := ![![![-3632146, -4728955, -5536935, 2122448, 8315391], ![1701806, 2215705, 2594276, -994452, -3896094], ![-398682, -519073, -607761, 232970, 912738], ![-757503, -986248, -1154757, 442647, 1734219], ![-1333435, -1736096, -2032722, 779194, 3052750]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [75, 131, 106, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [145, 20, 14], [51, 130, 137], [0, 1]]
 g := ![![[139, 137, 55], [39, 28, 64], [103, 91, 80], [103, 9], [79, 131, 80], [45, 1], []], ![[66, 95, 104, 75], [105, 47, 59, 134], [77, 74, 16, 104], [14, 43], [71, 21, 20, 101], [119, 139], [18, 45]], ![[136, 40, 8, 50], [105, 115, 2, 50], [60, 83, 103, 22], [17, 127], [5, 84, 122, 37], [69, 98], [46, 45]]]
 h' := ![![[145, 20, 14], [95, 11, 31], [127, 86, 8], [64, 26, 69], [115, 0, 3], [98, 70, 82], [0, 0, 1], [0, 1]], ![[51, 130, 137], [65, 32, 107], [122, 142, 130], [144, 9, 123], [99, 50, 88], [46, 99, 13], [45, 67, 130], [145, 20, 14]], ![[0, 1], [7, 108, 13], [137, 74, 13], [38, 116, 110], [135, 101, 60], [37, 133, 56], [57, 84, 20], [51, 130, 137]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 123], []]
 b := ![[], [96, 76, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [75, 131, 106, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2642633, -2746458, 1242164, 1994074, 2189238]
  a := ![-6, 14, 11, 19, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1621751, -2500764, -1863174, 1994074, 2189238]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 36, -32, 6, 63]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-4, 36, -32, 6, 63]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![131, 107, 1, 0, 0], ![26, 93, 0, 1, 0], ![64, 94, 0, 0, 1]] where
  M :=![![![-4, 36, -32, 6, 63], ![-138, -339, 210, -52, -90], ![142, 209, -481, 158, -66], ![-23, 323, 196, -297, 585], ![-91, -610, 218, 32, -614]]]
  hmulB := by decide  
  f := ![![![44554730, -9824128, -2619674, 2122448, 8315391]], ![![-20875678, 4602997, 1227422, -994452, -3896094]], ![![23893130, -5268334, -1404839, 1138194, 4459251]], ![![-5123993, 1129818, 301274, -244091, -956307]], ![![5996993, -1322312, -352604, 285678, 1119238]]]
  g := ![![![0, -20, -32, 6, 63], ![-136, -63, 210, -52, -90], ![419, 286, -481, 158, -66], ![-367, -318, 196, -297, 585], ![65, 204, 218, 32, -614]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [49, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 150], [0, 1]]
 g := ![![[82, 37], [53, 81], [17, 72], [5], [147, 21], [8], [1]], ![[0, 114], [0, 70], [37, 79], [5], [27, 130], [8], [1]]]
 h' := ![![[59, 150], [121, 108], [73, 9], [119, 26], [45, 96], [46, 126], [102, 59], [0, 1]], ![[0, 1], [0, 43], [0, 142], [143, 125], [122, 55], [81, 25], [110, 92], [59, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [129, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [49, 92, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2913, -4684, -17618, 11925, -15441]
  a := ![18, -9, -28, -5, -51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![19795, 14721, -17618, 11925, -15441]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![44554730, -9824128, -2619674, 2122448, 8315391]] ![![-4, 36, -32, 6, 63]]
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


lemma PB434I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB434I3 : PrimesBelowBoundCertificateInterval O 103 151 434 where
  m := 9
  g := ![2, 1, 3, 1, 3, 3, 2, 2, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB434I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0, I137N1, I137N2]
    · exact ![I139N0, I139N1]
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
    · exact ![1225043, 11449]
    · exact ![15386239549]
    · exact ![12769, 12769, 113]
    · exact ![33038369407]
    · exact ![17161, 17161, 131]
    · exact ![18769, 18769, 137]
    · exact ![373301041, 139]
    · exact ![492884401, 149]
    · exact ![3442951, 22801]
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
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
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
  β := ![I113N2, I131N2, I137N2, I139N1, I149N1]
  Il := ![[], [], [I113N2], [], [I131N2], [I137N2], [I139N1], [I149N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
