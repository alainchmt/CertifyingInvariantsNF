
import IdealArithmetic.Examples.NF5_1_48600000_4.RI5_1_48600000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 24, -11, -3, 4]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-11, 24, -11, -3, 4]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![22, 40, 79, 1, 0], ![94, 36, 3, 0, 1]] where
  M :=![![![-11, 24, -11, -3, 4], ![24, -71, 41, 17, -6], ![-36, 114, -84, -1, 34], ![204, -546, 283, 154, -2], ![12, 60, -159, 135, 137]]]
  hmulB := by decide  
  f := ![![![95, -180, -107, 7, 16]], ![![96, -145, -93, 5, 14]], ![![84, -114, -70, 5, 10]], ![![118, -176, -109, 7, 16]], ![![118, -210, -127, 8, 19]]]
  g := ![![![-3, 0, 2, -3, 4], ![2, -5, -12, 17, -6], ![-30, -10, -1, -1, 34], ![-28, -62, -111, 154, -2], ![-148, -96, -105, 135, 137]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [9, 93, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 57, 49], [81, 49, 58], [0, 1]]
 g := ![![[11, 0, 35], [100, 32, 53], [47, 81], [23, 57, 62], [84, 3], [1]], ![[59, 5, 0, 83], [30, 92, 60, 37], [31, 53], [85, 13, 77, 14], [47, 3], [73, 0, 74, 56]], ![[44, 53, 11, 77], [73, 38, 102, 77], [92, 69], [14, 48, 2, 82], [], [49, 1, 106, 51]]]
 h' := ![![[8, 57, 49], [63, 69, 79], [54, 89, 38], [7, 42, 9], [74, 41, 13], [98, 14, 89], [0, 1]], ![[81, 49, 58], [39, 60, 83], [65, 19, 17], [39, 20, 38], [58, 73, 78], [69, 89, 18], [8, 57, 49]], ![[0, 1], [10, 85, 52], [47, 106, 52], [33, 45, 60], [76, 100, 16], [66, 4], [81, 49, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76, 91], []]
 b := ![[], [35, 13, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [9, 93, 18, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1900215, 4172268, -963429, -2627009, -1434036]
  a := ![0, -1, -3, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1782181, 1503532, 1970770, -2627009, -1434036]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![95, -180, -107, 7, 16]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![95, -180, -107, 7, 16]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![87, 28, 1, 0, 0], ![25, 52, 0, 1, 0], ![102, 73, 0, 0, 1]] where
  M :=![![![95, -180, -107, 7, 16], ![96, -145, -93, 5, 14], ![84, -114, -70, 5, 10], ![60, -66, -59, 0, 10], ![-12, 12, 27, 3, -5]]]
  hmulB := by decide  
  f := ![![![-11, 24, -11, -3, 4]], ![![24, -71, 41, 17, -6]], ![![-3, 2, 1, 2, 2]], ![![11, -34, 20, 9, -2]], ![![6, -25, 16, 10, 1]]]
  g := ![![![71, 12, -107, 7, 16], ![62, 11, -93, 5, 14], ![47, 8, -70, 5, 10], ![39, 8, -59, 0, 10], ![-18, -5, 27, 3, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P1 : CertificateIrreducibleZModOfList' 107 2 2 6 [90, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 106], [0, 1]]
 g := ![![[23, 44], [48, 36], [16], [79, 11], [25], [70, 1]], ![[0, 63], [0, 71], [16], [100, 96], [25], [33, 106]]]
 h' := ![![[70, 106], [67, 77], [8, 6], [59, 103], [59, 15], [13, 102], [0, 1]], ![[0, 1], [0, 30], [0, 101], [100, 4], [39, 92], [91, 5], [70, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [62, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N1 : CertifiedPrimeIdeal' SI107N1 107 where
  n := 2
  hpos := by decide
  P := [90, 37, 1]
  hirr := P107P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2376, 4148, 1478, -2860, 1278]
  a := ![3, -64, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1774, 170, 1478, -2860, 1278]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N1 B_one_repr
lemma NI107N1 : Nat.card (O ⧸ I107N1) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-11, 24, -11, -3, 4]] ![![95, -180, -107, 7, 16]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8363, -24150, 14553, 4241, -3494]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![8363, -24150, 14553, 4241, -3494]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![95, 90, 30, 1, 0], ![101, 60, 86, 0, 1]] where
  M :=![![![8363, -24150, 14553, 4241, -3494], ![-20964, 60773, -37379, -9905, 8482], ![50892, -148194, 93278, 21995, -19810], ![-118860, 348042, -225249, -45392, 43990], ![106524, -315258, 214661, 30343, -35487]]]
  hmulB := by decide  
  f := ![![![1727, -678, -733, 33, 118]], ![![708, -43, -55, 93, 66]], ![![396, -282, 380, 407, 186]], ![![2209, -726, -570, 233, 216]], ![![2323, -924, -396, 432, 307]]]
  g := ![![![-382, -1800, 1723, 4241, -3494], ![581, 4067, -4309, -9905, 8482], ![-347, -8616, 10432, 21995, -19810], ![-2290, 16458, -24281, -45392, 43990], ![7414, -8412, 21617, 30343, -35487]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [21, 68, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 12, 86], [53, 96, 23], [0, 1]]
 g := ![![[34, 102, 94], [104, 81], [87, 99, 26], [3, 20, 15], [64, 49], [1]], ![[3, 52, 15, 52], [0, 3], [105, 39, 6, 72], [21, 30, 68, 54], [12, 73], [14, 12, 9, 41]], ![[90, 69, 11, 23], [101, 94], [48, 13, 49, 47], [13, 41, 21, 79], [54, 60], [10, 78, 39, 68]]]
 h' := ![![[49, 12, 86], [18, 93, 58], [26, 7, 9], [46, 10, 74], [78, 91, 48], [88, 41, 102], [0, 1]], ![[53, 96, 23], [29, 57, 50], [62, 8, 49], [107, 28, 7], [102, 69, 8], [71, 103, 20], [49, 12, 86]], ![[0, 1], [87, 68, 1], [30, 94, 51], [17, 71, 28], [37, 58, 53], [100, 74, 96], [53, 96, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 25], []]
 b := ![[], [74, 42, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [21, 68, 7, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-203939, 457839, -120862, -269843, -136240]
  a := ![1, -3, -1, -1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![359554, 302001, 180652, -269843, -136240]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6187, 17660, -9976, -3776, 2828]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-6187, 17660, -9976, -3776, 2828]] 
 ![![109, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![82, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![85, 0, 0, 0, 1]] where
  M :=![![![-6187, 17660, -9976, -3776, 2828], ![16968, -48607, 28024, 9820, -7552], ![-45312, 130248, -76547, -24840, 19640], ![117840, -339912, 203608, 60933, -49680], ![-126384, 366396, -225416, -59656, 51113]]]
  hmulB := by decide  
  f := ![![![40409, -81548, 14424, 43696, 22644]], ![![15334, -31175, 5720, 16820, 8696]], ![![35210, -72128, 13701, 39176, 20208]], ![![35721, -76452, 17344, 43101, 21956]], ![![66929, -143240, 32480, 80744, 41133]]]
  g := ![![![645, 17660, -9976, -3776, 2828], ![-2146, -48607, 28024, 9820, -7552], ![6702, 130248, -76547, -24840, 19640], ![-20005, -339912, 203608, 60933, -49680], ![25455, 366396, -225416, -59656, 51113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-197, 594, -392, -96, 86]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-197, 594, -392, -96, 86]] 
 ![![109, 0, 0, 0, 0], ![41, 1, 0, 0, 0], ![63, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![-197, 594, -392, -96, 86], ![516, -1487, 928, 210, -192], ![-1152, 3396, -2237, -416, 420], ![2520, -7452, 5080, 703, -832], ![-1920, 5802, -4336, -164, 493]]]
  hmulB := by decide  
  f := ![![![-483761, 1087638, -289752, -637196, -320530]], ![![-199609, 448783, -119560, -262922, -132258]], ![![-349755, 786366, -209501, -460700, -231746]], ![![-425373, 956418, -254832, -560341, -281866]], ![![-763499, 1716672, -457400, -1005756, -505921]]]
  g := ![![![-13, 594, -392, -96, 86], ![61, -1487, 928, 210, -192], ![-81, 3396, -2237, -416, 420], ![97, -7452, 5080, 703, -832], ![107, 5802, -4336, -164, 493]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![8363, -24150, 14553, 4241, -3494]] ![![-6187, 17660, -9976, -3776, 2828]]
  ![![-179599481, 495294358, -223092347, -163373291, 102570582]] where
 M := ![![![-179599481, 495294358, -223092347, -163373291, 102570582]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-179599481, 495294358, -223092347, -163373291, 102570582]] ![![-197, 594, -392, -96, 86]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![-60680840531, 211765868824, -245588620817, 82386782687, -17746982804]]]
 hmul := by decide  
 g := ![![![![-556704959, 1942806136, -2253106613, 755842043, -162816356]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0, 0, 0]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]] where
  M :=![![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 5 2 6 [112, 28, 29, 106, 98, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 70, 73, 71, 40], [17, 76, 10, 112, 88], [23, 61, 87, 79, 59], [19, 18, 56, 77, 39], [0, 1]]
 g := ![![[69, 90, 15, 69, 4], [99, 70, 72, 32], [66, 61, 16, 25], [76, 66, 108, 97], [6, 15, 1], []], ![[10, 105, 17, 39, 35, 53, 56, 19], [109, 9, 53, 26], [33, 101, 109, 14], [34, 111, 4, 51], [46, 65, 6, 57, 108, 73, 85, 94], [39, 110, 110, 111, 69, 37, 57, 42]], ![[98, 30, 15, 41, 90, 12, 65, 99], [32, 29, 78, 41], [61, 103, 39, 106], [30, 100, 70, 69], [104, 33, 39, 89, 1, 57, 30, 8], [47, 62, 13, 38, 24, 82, 33, 82]], ![[95, 77, 0, 100, 62, 90, 44, 94], [47, 5, 54, 77], [36, 86, 66, 63], [38, 29, 108, 104], [0, 38, 107, 77, 13, 33, 29, 93], [19, 97, 53, 58, 104, 98, 63, 58]], ![[27, 72, 84, 87, 16, 107, 10, 29], [80, 73, 80, 100], [99, 46, 101, 62], [67, 70, 12, 105], [103, 78, 12, 64, 3, 12, 82, 84], [107, 107, 16, 107, 2, 43, 57, 107]]]
 h' := ![![[69, 70, 73, 71, 40], [68, 91, 21, 87, 2], [67, 20, 31, 1, 22], [112, 57, 32, 111, 5], [6, 73, 85, 31, 53], [0, 0, 0, 1], [0, 1]], ![[17, 76, 10, 112, 88], [10, 6, 97, 0, 61], [63, 52, 84, 10, 34], [16, 45, 86, 86, 50], [35, 74, 46, 12, 86], [57, 21, 100, 20, 102], [69, 70, 73, 71, 40]], ![[23, 61, 87, 79, 59], [46, 10, 112, 84, 10], [50, 89, 73, 68, 70], [92, 35, 79, 51, 28], [66, 17, 0, 107, 71], [101, 2, 32, 23, 80], [17, 76, 10, 112, 88]], ![[19, 18, 56, 77, 39], [107, 71, 63, 8, 69], [88, 4, 65, 105, 90], [74, 20, 0, 89, 96], [107, 91, 97, 99, 68], [95, 96, 59, 108, 61], [23, 61, 87, 79, 59]], ![[0, 1], [105, 48, 46, 47, 84], [108, 61, 86, 42, 10], [3, 69, 29, 2, 47], [106, 84, 111, 90, 61], [73, 107, 35, 74, 96], [19, 18, 56, 77, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 42, 52, 58], [], [], []]
 b := ![[], [110, 70, 78, 0, 72], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 5
  hpos := by decide
  P := [112, 28, 29, 106, 98, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3961657980566, -8905657210428, 2367498049436, 5223715922116, 2625441354092]
  a := ![1, 19, 4, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![35058920182, -78811125756, 20951310172, 46227574532, 23233994284]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 18424351793 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![175, 1252, 518, -62, -84]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![175, 1252, 518, -62, -84]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![115, 84, 1, 0, 0], ![119, 44, 0, 1, 0], ![16, 11, 0, 0, 1]] where
  M :=![![![175, 1252, 518, -62, -84], ![-504, 1435, 770, -70, -124], ![-744, 1356, 745, -98, -140], ![-840, 1356, 558, -235, -196], ![-216, 372, -302, -358, -165]]]
  hmulB := by decide  
  f := ![![![-1295, 3524, -1426, -1326, 796]], ![![4776, -13235, 6178, 4146, -2652]], ![![1861, -5212, 2619, 1444, -968]], ![![833, -2388, 1384, 475, -368]], ![![-272, 781, -456, -152, 119]]]
  g := ![![![-399, -304, 518, -62, -84], ![-620, -463, 770, -70, -124], ![-571, -436, 745, -98, -140], ![-267, -260, 558, -235, -196], ![628, 341, -302, -358, -165]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [124, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 126], [0, 1]]
 g := ![![[10, 42], [3, 38], [102, 22], [26, 71], [18, 69], [30, 1]], ![[0, 85], [0, 89], [0, 105], [124, 56], [56, 58], [60, 126]]]
 h' := ![![[30, 126], [9, 114], [52, 66], [78, 99], [54, 84], [90, 14], [0, 1]], ![[0, 1], [0, 13], [0, 61], [0, 28], [34, 43], [2, 113], [30, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [51, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [124, 97, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-758, 5604, -6587, 3023, 6668]
  a := ![-1, 0, -4, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2286, 2776, -6587, 3023, 6668]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10633, 31233, -20525, -3758, 3820]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-10633, 31233, -20525, -3758, 3820]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![116, 20, 1, 0, 0], ![93, 97, 0, 1, 0], ![31, 19, 0, 0, 1]] where
  M :=![![![-10633, 31233, -20525, -3758, 3820], ![22920, -67933, 46575, 6215, -7516], ![-45096, 135660, -99298, -6037, 12430], ![74580, -231546, 191773, -12288, -12074], ![-13674, 60015, -102453, 56646, -18503]]]
  hmulB := by decide  
  f := ![![![-11923, 8415, 7979, 396, -778]], ![![-4668, -253, 4921, 2533, 792]], ![![-11588, 7516, 8112, 843, -546]], ![![-12057, 5408, 9753, 2553, 200]], ![![-3133, 965, 2955, 1087, 237]]]
  g := ![![![20483, 5777, -20525, -3758, 3820], ![-45077, -11492, 46575, 6215, -7516], ![91729, 19457, -99298, -6037, 12430], ![-162630, -20832, 191773, -12288, -12074], ![56507, -23890, -102453, 56646, -18503]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [3, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 126], [0, 1]]
 g := ![![[76, 72], [123, 11], [51, 35], [52, 84], [120, 47], [26, 1]], ![[43, 55], [28, 116], [72, 92], [77, 43], [72, 80], [52, 126]]]
 h' := ![![[26, 126], [12, 31], [101, 30], [98, 17], [21, 46], [49, 38], [0, 1]], ![[0, 1], [56, 96], [119, 97], [32, 110], [74, 81], [21, 89], [26, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [106, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [3, 101, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9957, 27792, -13100, -9142, 6098]
  a := ![0, 0, 4, -10, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![17093, 8352, -13100, -9142, 6098]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -13, -7, 2, 2]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![13, -13, -7, 2, 2]] 
 ![![127, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![106, 0, 1, 0, 0], ![102, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![13, -13, -7, 2, 2], ![12, -17, -1, 7, 4], ![24, -48, 10, 27, 14], ![84, -186, 49, 108, 54], ![150, -339, 91, 200, 101]]]
  hmulB := by decide  
  f := ![![![7, -131, 213, 44, -48]], ![![-1, -18, 36, 7, -8]], ![![10, -122, 186, 39, -42]], ![![-6, -72, 151, 30, -34]], ![![14, -79, 95, 20, -21]]]
  g := ![![![6, -13, -7, 2, 2], ![-3, -17, -1, 7, 4], ![-26, -48, 10, 27, 14], ![-112, -186, 49, 108, 54], ![-209, -339, 91, 200, 101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![175, 1252, 518, -62, -84]] ![![-10633, 31233, -20525, -3758, 3820]]
  ![![-7, 131, -213, -44, 48]] where
 M := ![![![-7, 131, -213, -44, 48]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![-7, 131, -213, -44, 48]] ![![13, -13, -7, 2, 2]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![-127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![205, 1099, -1288, -1179, -500]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![205, 1099, -1288, -1179, -500]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![129, 44, 14, 1, 0], ![14, 84, 121, 0, 1]] where
  M :=![![![205, 1099, -1288, -1179, -500], ![-3000, 7705, -2580, -4788, -2358], ![-14148, 32370, -8873, -19086, -9576], ![-57456, 129492, -34596, -75905, -38172], ![-107442, 241377, -64200, -141357, -71117]]]
  hmulB := by decide  
  f := ![![![1211, -3407, 1760, 897, -614]], ![![-3684, 10421, -5580, -2538, 1794]], ![![10764, -30594, 16853, 6978, -5076]], ![![873, -2461, 1286, 634, -438]], ![![7988, -22739, 12639, 5073, -3727]]]
  g := ![![![1216, 725, 578, -1179, -500], ![4944, 3179, 2670, -4788, -2358], ![19710, 12798, 10817, -19086, -9576], ![78387, 50960, 43106, -75905, -38172], ![145979, 94923, 80305, -141357, -71117]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [62, 65, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 113, 48], [61, 17, 83], [0, 1]]
 g := ![![[126, 44, 60], [61, 69, 59], [98, 52], [60, 55], [65, 21], [109, 1], []], ![[69, 111, 69, 75], [47, 33, 14, 62], [109, 58], [7, 59], [101, 43], [111, 27], [115, 77]], ![[27, 106, 14, 29], [61, 110, 88, 50], [30, 55], [41, 64], [26, 5], [76, 62], [80, 77]]]
 h' := ![![[48, 113, 48], [17, 53, 45], [49, 1, 94], [112, 75, 24], [65, 82, 102], [54, 58, 26], [0, 0, 1], [0, 1]], ![[61, 17, 83], [100, 60, 34], [106, 74, 74], [24, 3, 78], [117, 115, 37], [109, 127, 82], [21, 40, 17], [48, 113, 48]], ![[0, 1], [26, 18, 52], [103, 56, 94], [103, 53, 29], [126, 65, 123], [67, 77, 23], [71, 91, 113], [61, 17, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 9], []]
 b := ![[], [47, 48, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [62, 65, 22, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2263176, 4635575, -542524, -3569605, -2320496]
  a := ![13, -1, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3745823, 2722289, 2520702, -3569605, -2320496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1585, -4957, 4214, -373, -214]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![1585, -4957, 4214, -373, -214]] 
 ![![131, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![73, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![1585, -4957, 4214, -373, -214], ![-1284, 4795, -6400, 2716, -746], ![-4476, 9906, 3781, -11622, 5432], ![32592, -85956, 25444, 41805, -23244], ![-67494, 185673, -82076, -62821, 39089]]]
  hmulB := by decide  
  f := ![![![37391, -7783, -14190, -545, 1704]], ![![12066, -2405, -4548, -192, 538]], ![![19930, -3956, -7551, -348, 876]], ![![20629, -3869, -7934, -514, 836]], ![![826, 409, -604, -399, -141]]]
  g := ![![![-436, -4957, 4214, -373, -214], ![382, 4795, -6400, 2716, -746], ![1080, 9906, 3781, -11622, 5432], ![-8375, -85956, 25444, 41805, -23244], ![17627, 185673, -82076, -62821, 39089]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-133, 216, 134, -8, -20]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![-133, 216, 134, -8, -20]] 
 ![![131, 0, 0, 0, 0], ![75, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![55, 0, 0, 1, 0], ![95, 0, 0, 0, 1]] where
  M :=![![![-133, 216, 134, -8, -20], ![-120, 167, 108, -6, -16], ![-96, 120, 81, -4, -12], ![-72, 84, 56, -3, -8], ![24, -36, -20, 2, 3]]]
  hmulB := by decide  
  f := ![![![-71, 216, -134, -40, 36]], ![![-39, 119, -74, -22, 20]], ![![-8, 24, -15, -4, 4]], ![![-19, 60, -38, -11, 12]], ![![-59, 180, -114, -30, 31]]]
  g := ![![![-115, 216, 134, -8, -20], ![-89, 167, 108, -6, -16], ![-64, 120, 81, -4, -12], ![-45, 84, 56, -3, -8], ![19, -36, -20, 2, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![205, 1099, -1288, -1179, -500]] ![![1585, -4957, 4214, -373, -214]]
  ![![-71, 216, -134, -40, 36]] where
 M := ![![![-71, 216, -134, -40, 36]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![-71, 216, -134, -40, 36]] ![![-133, 216, 134, -8, -20]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0, 0, 0]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![0, 0, 0, 0, 137]] where
  M :=![![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![0, 0, 0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 5 2 7 [9, 58, 101, 121, 73, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 127, 41, 30, 109], [112, 26, 10, 85, 9], [61, 118, 50, 120, 83], [19, 2, 36, 39, 73], [0, 1]]
 g := ![![[136, 116, 0, 108, 49], [120, 0, 19, 109], [101, 124, 77, 8], [121, 48, 3, 54, 39], [92, 2, 64, 1], [], []], ![[16, 27, 90, 60, 14, 19, 42, 68], [82, 106, 95, 93], [38, 127, 43, 18], [52, 22, 70, 112, 99, 32, 67, 123], [22, 11, 106, 14], [84, 46, 47, 38], [117, 60, 135, 99]], ![[104, 127, 94, 46, 1, 100, 106, 63], [6, 84, 115, 133], [67, 26, 7, 135], [63, 68, 120, 69, 39, 34, 26, 73], [54, 90, 123, 14], [15, 108, 83, 119], [113, 134, 1, 81]], ![[14, 98, 125, 110, 53, 67, 68, 45], [40, 88, 87, 36], [36, 112, 73, 61], [42, 23, 99, 53, 24, 87, 6, 84], [48, 56, 83, 17], [97, 116, 96, 63], [129, 131, 85, 39]], ![[98, 86, 121, 2, 124, 40, 117, 25], [117, 15, 29, 72], [81, 39, 113, 73], [70, 94, 2, 105, 77, 92, 79, 81], [107, 132, 74, 112], [36, 105, 118, 77], [34, 32, 3, 123]]]
 h' := ![![[9, 127, 41, 30, 109], [90, 34, 8, 136, 7], [99, 63, 31, 6, 71], [7, 121, 33, 44, 62], [131, 126, 17, 15, 83], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[112, 26, 10, 85, 9], [86, 12, 127, 34, 72], [106, 111, 54, 3, 97], [96, 28, 53, 92, 93], [90, 109, 79, 33, 84], [98, 125, 38, 112, 98], [124, 29, 81, 100, 60], [9, 127, 41, 30, 109]], ![[61, 118, 50, 120, 83], [33, 10, 126, 0, 125], [118, 50, 111, 41, 63], [6, 5, 17, 94, 51], [37, 37, 134, 35, 84], [89, 77, 9, 34, 39], [19, 119, 25, 60, 16], [112, 26, 10, 85, 9]], ![[19, 2, 36, 39, 73], [49, 136, 22, 48, 76], [86, 38, 106, 82, 131], [37, 109, 20, 76, 46], [131, 26, 108, 21, 67], [17, 33, 62, 17, 47], [94, 118, 2, 128, 36], [61, 118, 50, 120, 83]], ![[0, 1], [13, 82, 128, 56, 131], [92, 12, 109, 5, 49], [37, 11, 14, 105, 22], [10, 113, 73, 33, 93], [98, 39, 28, 111, 89], [55, 8, 28, 123, 25], [19, 2, 36, 39, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91, 59, 132, 108], [], [], []]
 b := ![[], [107, 79, 85, 29, 43], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 5
  hpos := by decide
  P := [9, 58, 101, 121, 73, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18475453251, -39958626696, 8128116840, 26448653916, 14757120496]
  a := ![-1, -3, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![134857323, -291668808, 59329320, 193055868, 107716208]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 17, -7, -4, 2]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-7, 17, -7, -4, 2]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![2, 46, 1, 0, 0], ![47, 110, 0, 1, 0], ![28, 42, 0, 0, 1]] where
  M :=![![![-7, 17, -7, -4, 2], ![12, -37, 23, 7, -8], ![-48, 132, -70, -33, 14], ![84, -258, 169, 28, -66], ![-174, 471, -245, -130, 21]]]
  hmulB := by decide  
  f := ![![![1127, -1253, -871, 42, 128]], ![![768, -793, -571, 25, 84]], ![![274, -284, -204, 9, 30]], ![![991, -1053, -748, 34, 110]], ![![458, -491, -347, 16, 51]]]
  g := ![![![1, 5, -7, -4, 2], ![-1, -11, 23, 7, -8], ![9, 46, -70, -33, 14], ![2, -60, 169, 28, -66], ![42, 181, -245, -130, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [90, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [135, 138], [0, 1]]
 g := ![![[68, 38], [41, 67], [89], [17, 25], [131], [16], [1]], ![[55, 101], [51, 72], [89], [56, 114], [131], [16], [1]]]
 h' := ![![[135, 138], [63, 90], [53, 117], [138, 111], [30, 134], [127, 100], [49, 135], [0, 1]], ![[0, 1], [120, 49], [2, 22], [111, 28], [50, 5], [5, 39], [65, 4], [135, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118]]
 b := ![[], [118, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [90, 4, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3795, 12456, -7520, -1693, 5527]
  a := ![3, 0, 7, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-460, 2248, -7520, -1693, 5527]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4559, -11165, 2986, 6483, 3252]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![4559, -11165, 2986, 6483, 3252]] 
 ![![139, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![96, 0, 0, 0, 1]] where
  M :=![![![4559, -11165, 2986, 6483, 3252], ![19512, -44221, 11578, 25750, 12966], ![77796, -174978, 46359, 102340, 51500], ![309000, -694704, 184862, 406859, 204680], ![575142, -1293111, 344598, 757641, 381109]]]
  hmulB := by decide  
  f := ![![![-298735, 891377, -629854, -62573, 90942]], ![![-15417, 45752, -31548, -4003, 4988]], ![![-130054, 389372, -279233, -23178, 38044]], ![![-72490, 211178, -133218, -31043, 28108]], ![![-186030, 563229, -423438, -13737, 47023]]]
  g := ![![![-4322, -11165, 2986, 6483, 3252], ![-17081, -44221, 11578, 25750, 12966], ![-68056, -174978, 46359, 102340, 51500], ![-270814, -694704, 184862, 406859, 204680], ![-504459, -1293111, 344598, 757641, 381109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, -462, -204, 18, 30]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![-43, -462, -204, 18, 30]] 
 ![![139, 0, 0, 0, 0], ![40, 1, 0, 0, 0], ![68, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-43, -462, -204, 18, 30], ![180, -493, -294, 6, 36], ![216, -360, -307, -42, 12], ![72, 36, -342, -223, -84], ![-360, 846, -150, -444, -229]]]
  hmulB := by decide  
  f := ![![![15383, -43926, 24864, 9342, -7014]], ![![4124, -11773, 6654, 2514, -1884]], ![![8332, -23808, 13529, 5010, -3780]], ![![4548, -12924, 7110, 2957, -2148]], ![![4117, -11856, 7038, 2190, -1759]]]
  g := ![![![221, -462, -204, 18, 30], ![280, -493, -294, 6, 36], ![272, -360, -307, -42, 12], ![264, 36, -342, -223, -84], ![47, 846, -150, -444, -229]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2

def I139N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4039, 9112, -2452, -5352, -2690]] i)))

def SI139N3: IdealEqSpanCertificate' Table ![![-4039, 9112, -2452, -5352, -2690]] 
 ![![139, 0, 0, 0, 0], ![44, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![116, 0, 0, 1, 0], ![84, 0, 0, 0, 1]] where
  M :=![![![-4039, 9112, -2452, -5352, -2690], ![-16140, 36311, -9690, -21282, -10704], ![-64224, 144420, -38491, -84618, -42564], ![-255384, 574236, -153018, -336439, -169236], ![-475596, 1069368, -284946, -626526, -315157]]]
  hmulB := by decide  
  f := ![![![-3397, 10184, -7592, -204, 818]], ![![-1040, 3111, -2302, -78, 256]], ![![-262, 812, -687, 66, 32]], ![![-2996, 8884, -6310, -499, 844]], ![![-1560, 4824, -4086, 414, 179]]]
  g := ![![![3355, 9112, -2452, -5352, -2690], ![13316, 36311, -9690, -21282, -10704], ![52930, 144420, -38491, -84618, -42564], ![210440, 574236, -153018, -336439, -169236], ![391884, 1069368, -284946, -626526, -315157]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N3 : Nat.card (O ⧸ I139N3) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N3)

lemma isPrimeI139N3 : Ideal.IsPrime I139N3 := prime_ideal_of_norm_prime hp139.out _ NI139N3
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-7, 17, -7, -4, 2]] ![![4559, -11165, 2986, 6483, 3252]]
  ![![-330497, 743838, -198841, -436165, -219344]] where
 M := ![![![-330497, 743838, -198841, -436165, -219344]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![-330497, 743838, -198841, -436165, -219344]] ![![-43, -462, -204, 18, 30]]
  ![![152712515, -343706724, 91847233, 201518935, 101344802]] where
 M := ![![![152712515, -343706724, 91847233, 201518935, 101344802]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI139N2 : IdealMulLeCertificate' Table 
  ![![152712515, -343706724, 91847233, 201518935, 101344802]] ![![-4039, 9112, -2452, -5352, -2690]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![-100632070162949, 226270074355172, -60293045123145, -132568462432423, -66684927764640]]]
 hmul := by decide  
 g := ![![![![-723971727791, 1627842261548, -433762914555, -953729945557, -479747681760]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2, I139N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
    exact isPrimeI139N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1 ⊙ MulI139N2)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 6, -29, -31, 20]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![43, 6, -29, -31, 20]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![99, 45, 6, 140, 1]] where
  M :=![![![43, 6, -29, -31, 20], ![120, -257, 75, 111, -62], ![-372, 1050, -456, -359, 222], ![1332, -3702, 1801, 1098, -718], ![-1968, 5526, -2869, -1433, 987]]]
  hmulB := by decide  
  f := ![![![-1, 6, 5, 1, 0]], ![![0, -1, 7, 5, 2]], ![![12, -30, 14, 21, 10]], ![![60, -138, 41, 84, 42]], ![![57, -129, 45, 83, 41]]]
  g := ![![![-13, -6, -1, -19, 20], ![42, 17, 3, 59, -62], ![-150, -60, -12, -211, 222], ![486, 192, 41, 682, -718], ![-669, -261, -59, -937, 987]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 4 2 7 [121, 114, 86, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 147, 84, 57], [41, 45, 116, 20], [137, 105, 98, 72], [0, 1]]
 g := ![![[100, 9, 95, 35], [19, 3, 130], [147, 133, 88, 69], [129, 40, 46], [14, 131, 38, 4], [1], []], ![[106, 114, 105, 116, 80, 126], [65, 27, 145], [29, 98, 91, 143, 30, 72], [87, 147, 35], [83, 34, 119, 68, 15, 59], [142, 26, 82], [37, 98, 120]], ![[68, 62, 6, 52, 47, 112], [40, 121, 31], [21, 43, 144, 66, 49, 64], [57, 109, 142], [122, 65, 92, 54, 27, 22], [4, 16, 61], [145, 115, 102]], ![[106, 47, 70, 26, 103, 3], [57, 39, 140], [0, 97, 80, 121, 21, 12], [91, 34, 6], [69, 43, 34, 50, 32, 11], [132, 6, 102], [85, 19, 118]]]
 h' := ![![[118, 147, 84, 57], [92, 95, 36, 83], [93, 83, 96, 117], [81, 54, 38, 101], [94, 25, 147, 116], [28, 35, 63, 147], [0, 0, 1], [0, 1]], ![[41, 45, 116, 20], [26, 61, 144, 75], [21, 57, 89, 88], [45, 63, 9, 8], [80, 32, 4, 83], [126, 148, 109, 101], [60, 140, 43, 23], [118, 147, 84, 57]], ![[137, 105, 98, 72], [86, 62, 36, 63], [3, 7, 118, 110], [80, 80, 125, 35], [47, 28, 32, 69], [95, 130, 81, 145], [79, 65, 137, 106], [41, 45, 116, 20]], ![[0, 1], [105, 80, 82, 77], [105, 2, 144, 132], [111, 101, 126, 5], [29, 64, 115, 30], [52, 134, 45, 54], [140, 93, 117, 20], [137, 105, 98, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [18, 132, 110], []]
 b := ![[], [], [85, 47, 59, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 4
  hpos := by decide
  P := [121, 114, 86, 2, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![556503834, -1219325878, 274851347, 774987387, 420674355]
  a := ![1, 1, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-275773539, -135232697, -15095267, -390063237, 420674355]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 492884401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -6, -5, -1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![1, -6, -5, -1, 0]] 
 ![![149, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![123, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![122, 0, 0, 0, 1]] where
  M :=![![![1, -6, -5, -1, 0], ![0, 1, -7, -5, -2], ![-12, 30, -14, -21, -10], ![-60, 138, -41, -84, -42], ![-120, 270, -71, -157, -79]]]
  hmulB := by decide  
  f := ![![![-43, -6, 29, 31, -20]], ![![-6, 1, 3, 3, -2]], ![![-33, -12, 27, 28, -18]], ![![-15, 24, -8, -3, 2]], ![![-22, -42, 43, 35, -23]]]
  g := ![![![5, -6, -5, -1, 0], ![8, 1, -7, -5, -2], ![19, 30, -14, -21, -10], ![63, 138, -41, -84, -42], ![112, 270, -71, -157, -79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![43, 6, -29, -31, 20]] ![![1, -6, -5, -1, 0]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4099, -607, -1376, -27, 186]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![4099, -607, -1376, -27, 186]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![133, 33, 34, 1, 0], ![4, 34, 43, 0, 1]] where
  M :=![![![4099, -607, -1376, -27, 186], ![1116, 1309, 296, -74, -54], ![-324, 1926, 965, -82, -148], ![-888, 1896, 1104, -71, -164], ![-330, -177, 20, 19, 3]]]
  hmulB := by decide  
  f := ![![![-95, 271, -152, -59, 44]], ![![264, -755, 432, 156, -118]], ![![-708, 2034, -1189, -394, 312]], ![![-173, 496, -286, -100, 78]], ![![-158, 455, -269, -85, 69]]]
  g := ![![![46, -40, -56, -27, 186], ![74, 37, 34, -74, -54], ![74, 64, 67, -82, -148], ![61, 65, 70, -71, -164], ![-19, -6, -5, 19, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [25, 135, 145, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 42, 147], [98, 108, 4], [0, 1]]
 g := ![![[52, 113, 69], [146, 64, 11], [22, 115, 99], [90, 62], [99, 52, 137], [6, 1], []], ![[60, 117, 73, 79], [52, 117, 31, 3], [4, 36, 14, 122], [15, 90], [20, 108, 121, 73], [103, 37], [62, 16]], ![[88, 102, 25, 1], [36, 40, 122, 64], [71, 31, 75, 5], [27, 25], [143, 85, 139, 95], [119, 103], [54, 16]]]
 h' := ![![[59, 42, 147], [125, 28, 89], [54, 120, 39], [23, 84, 34], [92, 134, 106], [1, 71, 52], [0, 0, 1], [0, 1]], ![[98, 108, 4], [137, 121, 138], [148, 46, 108], [116, 88, 14], [76, 135, 40], [110, 48, 47], [119, 112, 108], [59, 42, 147]], ![[0, 1], [142, 2, 75], [10, 136, 4], [28, 130, 103], [117, 33, 5], [79, 32, 52], [100, 39, 42], [98, 108, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 58], []]
 b := ![[], [51, 138, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [25, 135, 145, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10335, 37620, -18173, -10771, 9913]
  a := ![4, 0, -1, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9156, 371, -518, -10771, 9913]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![95, -271, 152, 59, -44]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![95, -271, 152, 59, -44]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![51, 117, 1, 0, 0], ![73, 103, 0, 1, 0], ![66, 68, 0, 0, 1]] where
  M :=![![![95, -271, 152, 59, -44], ![-264, 755, -432, -156, 118], ![708, -2034, 1189, 394, -312], ![-1872, 5388, -3200, -995, 788], ![2010, -5829, 3572, 961, -839]]]
  hmulB := by decide  
  f := ![![![-4099, 607, 1376, 27, -186]], ![![-1116, -1309, -296, 74, 54]], ![![-2247, -822, 229, 67, -20]], ![![-2737, -612, 456, 64, -52]], ![![-2292, -323, 468, 45, -57]]]
  g := ![![![-60, -140, 152, 59, -44], ![168, 393, -432, -156, 118], ![-451, -1063, 1189, 394, -312], ![1205, 2839, -3200, -995, 788], ![-1291, -3084, 3572, 961, -839]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [137, 108, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 150], [0, 1]]
 g := ![![[57, 97], [147, 123], [9, 103], [42], [87, 40], [37], [1]], ![[0, 54], [0, 28], [59, 48], [42], [146, 111], [37], [1]]]
 h' := ![![[43, 150], [95, 61], [126, 127], [84, 42], [10, 93], [110, 77], [14, 43], [0, 1]], ![[0, 1], [0, 90], [0, 24], [78, 109], [83, 58], [99, 74], [51, 108], [43, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [106, 125]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [137, 108, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16260, -10796, -28039, 43397, 57709]
  a := ![7, 2, -24, 0, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-36626, -33936, -28039, 43397, 57709]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![4099, -607, -1376, -27, 186]] ![![95, -271, 152, 59, -44]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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
  g := ![2, 3, 1, 3, 3, 1, 4, 2, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB434I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0]
    · exact ![I139N0, I139N1, I139N2, I139N3]
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
    · exact ![1295029, 109, 109]
    · exact ![18424351793]
    · exact ![16129, 16129, 127]
    · exact ![2248091, 131, 131]
    · exact ![48261724457]
    · exact ![19321, 139, 139, 139]
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
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
      exact NI139N3
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I109N1, I109N2, I127N2, I131N1, I131N2, I139N1, I139N2, I139N3, I149N1]
  Il := ![[], [I109N1, I109N2], [], [I127N2], [I131N1, I131N2], [], [I139N1, I139N2, I139N3], [I149N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
