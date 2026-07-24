
import IdealArithmetic.Examples.NF5_1_7500000_1.RI5_1_7500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0, 0, 0]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![0, 0, 0, 0, 107]] where
  M :=![![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![0, 0, 0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 5 2 6 [69, 4, 13, 102, 76, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 14, 47, 95, 15], [82, 60, 25, 106, 76], [46, 6, 90, 84, 1], [57, 26, 52, 36, 15], [0, 1]]
 g := ![![[41, 101, 89, 51, 49], [30, 92, 5, 50, 14], [64, 87, 100, 75], [20, 105, 77, 61, 9], [31, 1], []], ![[67, 3, 81, 99, 48, 97, 49, 51], [9, 96, 94, 1, 88, 61, 74, 54], [8, 13, 72, 16], [78, 103, 102, 56, 101, 75, 18, 5], [102, 23, 29, 56], [27, 22, 62, 92, 85, 102, 11, 58]], ![[80, 19, 62, 26, 78, 95, 20, 1], [44, 86, 103, 104, 60, 22, 47, 44], [4, 90, 73, 10], [1, 25, 68, 59, 57, 21, 67, 83], [99, 95, 52, 36], [68, 28, 58, 24, 2, 22, 2, 62]], ![[73, 62, 63, 27, 77, 44, 84, 53], [50, 47, 62, 14, 53, 54, 95, 34], [60, 52, 26, 76], [1, 32, 19, 18, 51, 88, 18, 27], [69, 6, 62, 92], [47, 77, 102, 36, 70, 42, 69, 1]], ![[34, 58, 31, 62, 69, 53, 21, 18], [10, 54, 30, 10, 0, 94, 79, 15], [23, 2, 22, 81], [64, 98, 86, 0, 1, 22, 26, 17], [33, 63, 12, 99], [39, 36, 22, 7, 100, 96, 97, 58]]]
 h' := ![![[60, 14, 47, 95, 15], [70, 70, 67, 59, 100], [92, 68, 48, 2, 11], [11, 59, 41, 51, 17], [1, 21, 21, 35, 3], [0, 0, 0, 1], [0, 1]], ![[82, 60, 25, 106, 76], [103, 29, 104, 49, 93], [13, 68, 48, 80, 102], [64, 22, 50, 53, 103], [68, 67, 4, 70, 6], [30, 95, 60, 22, 22], [60, 14, 47, 95, 15]], ![[46, 6, 90, 84, 1], [58, 20, 2, 28, 60], [85, 21, 11, 100, 19], [19, 94, 97, 35, 44], [79, 100, 27, 44, 22], [13, 86, 1, 53, 101], [82, 60, 25, 106, 76]], ![[57, 26, 52, 36, 15], [54, 8, 41, 80, 38], [102, 54, 44, 96, 81], [60, 27, 79, 29, 41], [49, 71, 34, 91, 53], [40, 59, 54, 22, 29], [46, 6, 90, 84, 1]], ![[0, 1], [21, 87, 0, 105, 30], [79, 3, 63, 43, 1], [32, 12, 54, 46, 9], [72, 62, 21, 81, 23], [67, 81, 99, 9, 62], [57, 26, 52, 36, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 86, 9, 78], [], [], []]
 b := ![[], [82, 75, 93, 58, 59], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 5
  hpos := by decide
  P := [69, 4, 13, 102, 76, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1570002761, 999892209, -644826191, -1445580486, 550057254]
  a := ![0, -2, 2, -3, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14672923, 9344787, -6026413, -13510098, 5140722]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 14025517307 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, -448, -168, -94, -104]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-33, -448, -168, -94, -104]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![37, 63, 10, 3, 1]] where
  M :=![![![-33, -448, -168, -94, -104], ![-416, -617, -354, -128, -188], ![-752, -1522, -489, -332, -256], ![-304, -824, -418, -169, -238], ![-852, -1598, -572, -346, -297]]]
  hmulB := by decide  
  f := ![![![3, 0, -4, -2, 4]], ![![16, 15, 2, -16, -4]], ![![-16, 2, 31, 12, -32]], ![![-72, -64, -6, 71, 14]], ![![7, 7, 2, -7, -3]]]
  g := ![![![35, 56, 8, 2, -104], ![60, 103, 14, 4, -188], ![80, 134, 19, 4, -256], ![78, 130, 18, 5, -238], ![93, 157, 22, 5, -297]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 4 2 6 [66, 87, 7, 23, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 9, 67, 94], [105, 1, 56, 28], [54, 98, 95, 96], [0, 1]]
 g := ![![[49, 52, 71, 93], [20, 46, 74], [15, 10, 69, 84], [14, 105, 84, 94], [86, 86, 1], []], ![[44, 28, 55, 56, 4, 88], [79, 21, 31], [36, 103, 58, 50, 78, 35], [83, 85, 10, 74, 76, 34], [107, 64, 106], [82, 89, 66, 81, 7, 4]], ![[92, 51, 97, 58, 58, 80], [12, 67, 73], [3, 40, 62, 34, 56, 88], [12, 10, 59, 106, 72, 94], [48, 106, 80], [22, 105, 46, 87, 32, 43]], ![[86, 92, 0, 108, 83, 44], [83, 76, 97], [85, 33, 92, 14, 46, 52], [31, 61, 67, 35, 59, 96], [108, 101, 64], [16, 108, 27, 4, 51, 92]]]
 h' := ![![[36, 9, 67, 94], [69, 16, 42, 86], [100, 85, 49, 69], [57, 91, 96, 53], [101, 31, 25, 58], [0, 0, 0, 1], [0, 1]], ![[105, 1, 56, 28], [67, 99, 9, 63], [7, 52, 38, 24], [46, 23, 75, 90], [43, 70, 99, 21], [42, 75, 94, 91], [36, 9, 67, 94]], ![[54, 98, 95, 96], [7, 90, 92, 90], [103, 82, 49, 89], [37, 38, 28, 9], [93, 61, 44, 31], [10, 33, 52, 25], [105, 1, 56, 28]], ![[0, 1], [86, 13, 75, 88], [88, 108, 82, 36], [7, 66, 19, 66], [6, 56, 50, 108], [102, 1, 72, 101], [54, 98, 95, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2, 74, 19], []]
 b := ![[], [], [60, 11, 96, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 4
  hpos := by decide
  P := [66, 87, 7, 23, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6935262968, -7512148814, -3733207536, 7565837594, 5365737262]
  a := ![3, -65, -1, -66, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1885023318, -3170216480, -526519084, -78269488, 5365737262]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 141158161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, -4, -2, 4]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![3, 0, -4, -2, 4]] 
 ![![109, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![73, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![103, 0, 0, 0, 1]] where
  M :=![![![3, 0, -4, -2, 4], ![16, 15, 2, -16, -4], ![-16, 2, 31, 12, -32], ![-72, -64, -6, 71, 14], ![20, -10, -52, -14, 55]]]
  hmulB := by decide  
  f := ![![![-33, -448, -168, -94, -104]], ![![-35, -429, -162, -90, -100]], ![![-29, -314, -117, -66, -72]], ![![-4, -24, -10, -5, -6]], ![![-39, -438, -164, -92, -101]]]
  g := ![![![-1, 0, -4, -2, 4], ![-11, 15, 2, -16, -4], ![7, 2, 31, 12, -32], ![48, -64, -6, 71, 14], ![-7, -10, -52, -14, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-33, -448, -168, -94, -104]] ![![3, 0, -4, -2, 4]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0, 0, 0]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]] where
  M :=![![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 5 2 6 [36, 54, 64, 65, 12, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 87, 81, 106, 72], [80, 42, 76, 47, 90], [94, 3, 2, 7, 86], [5, 93, 67, 66, 91], [0, 1]]
 g := ![![[21, 10, 110, 27, 28], [62, 62, 48, 50], [82, 94, 69, 53], [101, 112, 75, 36], [79, 101, 1], []], ![[38, 70, 105, 8, 100, 51, 31, 4], [83, 18, 112, 16], [57, 47, 62, 102], [75, 78, 97, 51], [5, 40, 9, 53, 80, 109, 53, 2], [63, 78, 51, 90, 40, 71, 73, 9]], ![[13, 24, 36, 2, 112, 46, 25, 20], [63, 4, 38, 102], [32, 51, 72, 14], [29, 107, 27, 52], [29, 38, 67, 19, 22, 0, 78, 71], [54, 71, 109, 87, 74, 47, 17, 37]], ![[40, 8, 7, 61, 29, 28, 31, 93], [24, 85, 106, 98], [71, 19, 51, 14], [92, 90, 57, 83], [101, 20, 100, 51, 52, 38, 106, 94], [112, 110, 106, 9, 100, 19, 80, 92]], ![[76, 95, 99, 30, 70, 93, 101, 64], [10, 35, 56, 28], [110, 42, 82, 41], [81, 79, 106, 52], [101, 110, 5, 109, 101, 79, 37, 7], [104, 99, 66, 40, 20, 77, 94, 87]]]
 h' := ![![[35, 87, 81, 106, 72], [15, 28, 75, 21, 49], [103, 36, 10, 20, 84], [2, 41, 44, 71, 36], [94, 8, 76, 99, 107], [0, 0, 0, 1], [0, 1]], ![[80, 42, 76, 47, 90], [94, 43, 42, 51, 65], [12, 79, 35, 38, 4], [16, 35, 14, 36, 21], [111, 0, 91, 78, 27], [40, 53, 26, 61, 94], [35, 87, 81, 106, 72]], ![[94, 3, 2, 7, 86], [80, 77, 103, 52, 17], [38, 67, 37, 13, 92], [25, 102, 101, 88, 63], [39, 36, 53, 4, 39], [87, 97, 66, 39, 61], [80, 42, 76, 47, 90]], ![[5, 93, 67, 66, 91], [101, 47, 60, 24, 53], [93, 34, 67, 46, 95], [29, 59, 100, 69, 63], [105, 13, 73, 82, 14], [70, 21, 97, 3, 16], [94, 3, 2, 7, 86]], ![[0, 1], [84, 31, 59, 78, 42], [52, 10, 77, 109, 64], [82, 102, 80, 75, 43], [25, 56, 46, 76, 39], [110, 55, 37, 9, 55], [5, 93, 67, 66, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 1, 13, 102], [], [], []]
 b := ![[], [104, 14, 109, 4, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 5
  hpos := by decide
  P := [36, 54, 64, 65, 12, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-141907208, -149022366, -54749856, 141982692, 72937884]
  a := ![1, -4, 1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1255816, -1318782, -484512, 1256484, 645468]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -35, -42, 23, 49]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-17, -35, -42, 23, 49]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![102, 97, 13, 1, 0], ![71, 3, 6, 0, 1]] where
  M :=![![![-17, -35, -42, 23, 49], ![196, 137, -58, -182, 46], ![184, 322, 319, -208, -364], ![-826, -545, 294, 774, -231], ![-370, -567, -500, 421, 592]]]
  hmulB := by decide  
  f := ![![![-567, -157, 146, -51, 129]], ![![516, 95, -106, 34, -102]], ![![-408, 2, 61, -8, 68]], ![![-104, -54, 43, -16, 33]], ![![-325, -85, 82, -28, 73]]]
  g := ![![![-46, -19, -5, 23, 49], ![122, 139, 16, -182, 46], ![372, 170, 41, -208, -364], ![-499, -590, -66, 774, -231], ![-672, -340, -75, 421, 592]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [92, 83, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 61, 117], [60, 65, 10], [0, 1]]
 g := ![![[120], [103, 15, 72], [66, 22, 74], [87, 80, 100], [125, 63, 62], [1]], ![[3, 43, 62, 15], [4, 88, 73, 31], [3, 107, 54, 15], [71, 30, 96, 94], [122, 48, 62, 73], [102, 20, 100, 16]], ![[12, 20, 6, 112], [64, 65, 84, 55], [109, 9, 88, 43], [43, 0, 103, 106], [74, 56, 75, 108], [110, 114, 108, 111]]]
 h' := ![![[9, 61, 117], [49, 45], [24, 0, 31], [124, 98, 57], [57, 40, 10], [35, 44, 69], [0, 1]], ![[60, 65, 10], [73, 78, 58], [120, 56, 110], [60, 71, 58], [26, 0, 123], [108, 72, 108], [9, 61, 117]], ![[0, 1], [82, 4, 69], [6, 71, 113], [6, 85, 12], [30, 87, 121], [13, 11, 77], [60, 65, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96, 90], []]
 b := ![[], [63, 103, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [92, 83, 58, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-954038, -308894, 693604, 1144924, -349070]
  a := ![1, 18, -3, 17, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-731908, -868656, -95244, 1144924, -349070]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, 43, -13, 10, -4]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-41, 43, -13, 10, -4]] 
 ![![127, 0, 0, 0, 0], ![45, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![74, 0, 0, 1, 0], ![53, 0, 0, 0, 1]] where
  M :=![![![-41, 43, -13, 10, -4], ![-16, -70, 33, -18, 20], ![80, 97, -52, 26, -36], ![-64, -23, 19, -7, 16], ![72, 58, -34, 16, -25]]]
  hmulB := by decide  
  f := ![![![25, 3, -51, -6, 68]], ![![11, 3, -18, -4, 24]], ![![1, 2, 1, 0, 0]], ![![6, -5, -29, 5, 40]], ![![11, -1, -27, -2, 35]]]
  g := ![![![-19, 43, -13, 10, -4], ![25, -70, 33, -18, 20], ![-31, 97, -52, 26, -36], ![4, -23, 19, -7, 16], ![-17, 58, -34, 16, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 4, -1, 1, -1]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![7, 4, -1, 1, -1]] 
 ![![127, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![74, 0, 0, 0, 1]] where
  M :=![![![7, 4, -1, 1, -1], ![-4, 2, 3, 0, 2], ![8, 7, 2, 2, 0], ![2, 4, 1, 2, 1], ![6, 7, 2, 1, 2]]]
  hmulB := by decide  
  f := ![![![-47, -42, 21, -9, 23]], ![![-20, -18, 9, -4, 10]], ![![-15, -13, 7, -3, 7]], ![![-9, -8, 4, -1, 4]], ![![-28, -25, 12, -5, 14]]]
  g := ![![![-1, 4, -1, 1, -1], ![-3, 2, 3, 0, 2], ![-4, 7, 2, 2, 0], ![-3, 4, 1, 2, 1], ![-5, 7, 2, 1, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-17, -35, -42, 23, 49]] ![![-41, 43, -13, 10, -4]]
  ![![-47, -42, 21, -9, 23]] where
 M := ![![![-47, -42, 21, -9, 23]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![-47, -42, 21, -9, 23]] ![![7, 4, -1, 1, -1]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![595, 346, -282, 102, -210]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![595, 346, -282, 102, -210]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![19, 52, 50, 7, 1]] where
  M :=![![![595, 346, -282, 102, -210], ![-840, -527, 244, -144, 204], ![816, 220, -383, 80, -288], ![-156, -96, -52, -23, -22], ![364, -38, -228, 10, -167]]]
  hmulB := by decide  
  f := ![![![1, 2, 2, -2, -2]], ![![-8, -5, 4, 8, -4]], ![![-16, -20, -13, 16, 16]], ![![36, 20, -20, -33, 18]], ![![-7, -8, -4, 7, 5]]]
  g := ![![![35, 86, 78, 12, -210], ![-36, -85, -76, -12, 204], ![48, 116, 107, 16, -288], ![2, 8, 8, 1, -22], ![27, 66, 62, 9, -167]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 4 2 7 [8, 65, 7, 11, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [119, 103, 12, 71], [15, 126, 71, 79], [117, 32, 48, 112], [0, 1]]
 g := ![![[67, 49, 12, 13], [103, 98, 45, 74], [35, 120, 27], [115, 1, 100], [86, 2, 121], [1], []], ![[61, 25, 89, 49, 115, 51], [4, 50, 33, 22, 80, 127], [35, 42, 20], [24, 3, 39], [103, 16, 59], [15, 25, 74], [64, 94, 63]], ![[67, 10, 111, 40, 55, 6], [57, 86, 28, 106, 87, 128], [124, 112, 12], [17, 129, 1], [41, 98, 102], [104, 111, 75], [76, 76, 84]], ![[96, 89, 15, 26, 15, 81], [113, 103, 8, 27, 29, 74], [4, 106, 64], [101, 85, 105], [8, 58, 80], [58, 22, 107], [81, 100, 99]]]
 h' := ![![[119, 103, 12, 71], [93, 16, 130, 119], [91, 87, 69, 104], [41, 114, 7, 114], [31, 19, 17, 121], [123, 66, 124, 120], [0, 0, 1], [0, 1]], ![[15, 126, 71, 79], [121, 29, 92, 69], [46, 97, 72, 67], [123, 60, 0, 85], [61, 123, 34, 68], [112, 93, 99, 94], [25, 83, 115, 27], [119, 103, 12, 71]], ![[117, 32, 48, 112], [42, 67, 67, 43], [111, 46, 92, 53], [102, 30, 57, 55], [99, 91, 61, 130], [54, 91, 4, 87], [10, 66, 72, 72], [15, 126, 71, 79]], ![[0, 1], [46, 19, 104, 31], [111, 32, 29, 38], [55, 58, 67, 8], [83, 29, 19, 74], [4, 12, 35, 92], [72, 113, 74, 32], [117, 32, 48, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [39, 112, 22], []]
 b := ![[], [], [119, 11, 35, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 4
  hpos := by decide
  P := [8, 65, 7, 11, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![124544520, -45714040, -293915900, -88400450, 308953720]
  a := ![-1, 2, 5, 4, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-43859360, -122987080, -120164900, -17183790, 308953720]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 294499921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -2, -2, 2, 2]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-1, -2, -2, 2, 2]] 
 ![![131, 0, 0, 0, 0], ![117, 1, 0, 0, 0], ![66, 0, 1, 0, 0], ![76, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![-1, -2, -2, 2, 2], ![8, 5, -4, -8, 4], ![16, 20, 13, -16, -16], ![-36, -20, 20, 33, -18], ![-28, -34, -20, 30, 25]]]
  hmulB := by decide  
  f := ![![![-595, -346, 282, -102, 210]], ![![-525, -305, 250, -90, 186]], ![![-306, -176, 145, -52, 108]], ![![-344, -200, 164, -59, 122]], ![![-189, -108, 90, -32, 67]]]
  g := ![![![1, -2, -2, 2, 2], ![1, 5, -4, -8, 4], ![-10, 20, 13, -16, -16], ![-6, -20, 20, 33, -18], ![15, -34, -20, 30, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![595, 346, -282, 102, -210]] ![![-1, -2, -2, 2, 2]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![855, 214, -207, 71, -187]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![855, 214, -207, 71, -187]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![25, 53, 1, 0, 0], ![91, 47, 0, 1, 0], ![110, 128, 0, 0, 1]] where
  M :=![![![855, 214, -207, 71, -187], ![-748, -100, 143, -40, 142], ![568, -37, -60, 2, -80], ![214, 144, -91, 40, -69], ![146, -95, 22, -21, 0]]]
  hmulB := by decide  
  f := ![![![-49, -88, -27, -17, -33]], ![![-132, -208, -71, 12, -34]], ![![-61, -99, -34, 1, -19]], ![![-77, -130, -43, -9, -34]], ![![-164, -267, -88, -3, -60]]]
  g := ![![![147, 232, -207, 71, -187], ![-119, -175, 143, -40, 142], ![78, 97, -60, 2, -80], ![47, 87, -91, 40, -69], ![11, -2, 22, -21, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [65, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 136], [0, 1]]
 g := ![![[64, 78], [100], [100], [7, 36], [25], [34], [1]], ![[0, 59], [100], [100], [125, 101], [25], [34], [1]]]
 h' := ![![[87, 136], [7, 107], [94, 127], [93, 127], [112, 131], [97, 5], [72, 87], [0, 1]], ![[0, 1], [0, 30], [46, 10], [45, 10], [1, 6], [121, 132], [106, 50], [87, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [96, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [65, 50, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3905, 3340, 756, -5200, -424]
  a := ![0, -10, -2, -20, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3685, 1912, 756, -5200, -424]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-191, -24, 36, -10, 36]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-191, -24, 36, -10, 36]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![96, 63, 1, 0, 0], ![127, 119, 0, 1, 0], ![90, 114, 0, 0, 1]] where
  M :=![![![-191, -24, 36, -10, 36], ![144, -11, -14, 0, -20], ![-80, 50, -11, 12, 0], ![-72, -40, 26, -11, 22], ![4, 46, -20, 10, -11]]]
  hmulB := by decide  
  f := ![![![25, 56, 24, 18, 16]], ![![64, 113, 38, 16, 36]], ![![48, 93, 35, 20, 28]], ![![79, 151, 56, 31, 46]], ![![70, 132, 48, 26, 41]]]
  g := ![![![-41, -38, 36, -10, 36], ![24, 23, -14, 0, -20], ![-4, -5, -11, 12, 0], ![-23, -21, 26, -11, 22], ![12, 10, -20, 10, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P1 : CertificateIrreducibleZModOfList' 137 2 2 7 [87, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [95, 136], [0, 1]]
 g := ![![[43, 63], [9], [107], [116, 7], [22], [120], [1]], ![[0, 74], [9], [107], [96, 130], [22], [120], [1]]]
 h' := ![![[95, 136], [5, 36], [68, 134], [46, 92], [40, 125], [6, 76], [50, 95], [0, 1]], ![[0, 1], [0, 101], [57, 3], [18, 45], [133, 12], [102, 61], [33, 42], [95, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125]]
 b := ![[], [11, 131]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N1 : CertifiedPrimeIdeal' SI137N1 137 where
  n := 2
  hpos := by decide
  P := [87, 42, 1]
  hirr := P137P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1166, -660, -1867, 140, 1542]
  a := ![13, 0, 4, 1, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![174, -551, -1867, 140, 1542]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N1 B_one_repr
lemma NI137N1 : Nat.card (O ⧸ I137N1) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-157, -118, 56, -32, 44]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![-157, -118, 56, -32, 44]] 
 ![![137, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![107, 0, 1, 0, 0], ![99, 0, 0, 1, 0], ![110, 0, 0, 0, 1]] where
  M :=![![![-157, -118, 56, -32, 44], ![176, 75, -86, 24, -64], ![-256, -166, 51, -44, 48], ![8, -44, -18, -9, -12], ![-152, -112, 8, -28, 15]]]
  hmulB := by decide  
  f := ![![![739, 494, -252, -688, 196]], ![![119, 85, -30, -112, 20]], ![![537, 360, -181, -500, 140]], ![![505, 314, -218, -465, 184]], ![![658, 436, -232, -612, 183]]]
  g := ![![![-39, -118, 56, -32, 44], ![91, 75, -86, 24, -64], ![-23, -166, 51, -44, 48], ![37, -44, -18, -9, -12], ![18, -112, 8, -28, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![855, 214, -207, 71, -187]] ![![-191, -24, 36, -10, 36]]
  ![![-121789, -44666, 35647, -13685, 30119]] where
 M := ![![![-121789, -44666, 35647, -13685, 30119]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![-121789, -44666, 35647, -13685, 30119]] ![![-157, -118, 56, -32, 44]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-2553543, 2332562, -673629, 536629, -173031]]]
 hmul := by decide  
 g := ![![![![-18639, 17026, -4917, 3917, -1263]]]]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 167, -85, 44, -56]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![97, 167, -85, 44, -56]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![43, 11, 1, 0, 0], ![111, 31, 0, 1, 0], ![50, 99, 0, 0, 1]] where
  M :=![![![97, 167, -85, 44, -56], ![-224, -212, 123, -58, 88], ![352, 251, -154, 70, -116], ![-120, -27, 29, -9, 26], ![228, 132, -86, 38, -67]]]
  hmulB := by decide  
  f := ![![![27, 23, -7, -20, 12]], ![![48, 68, 43, -38, -40]], ![![11, 12, 2, -8, 0]], ![![31, 32, 3, -23, 2]], ![![46, 58, 27, -36, -23]]]
  g := ![![![12, 38, -85, 44, -56], ![-25, -61, 123, -58, 88], ![36, 81, -154, 70, -116], ![-12, -19, 29, -9, 26], ![22, 47, -86, 38, -67]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [51, 91, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 138], [0, 1]]
 g := ![![[89, 30], [94, 5], [11], [84, 127], [78], [80], [1]], ![[0, 109], [56, 134], [11], [64, 12], [78], [80], [1]]]
 h' := ![![[48, 138], [71, 13], [64, 127], [25, 17], [51, 31], [50, 56], [88, 48], [0, 1]], ![[0, 1], [0, 126], [44, 12], [7, 122], [10, 108], [97, 83], [29, 91], [48, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [31, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [51, 91, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![381, -78, -249, -909, 619]
  a := ![-1, -4, -1, -5, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![583, -219, -249, -909, 619]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 7, 0, 4]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![1, 1, 7, 0, 4]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![72, 26, 1, 0, 0], ![37, 46, 0, 1, 0], ![48, 59, 0, 0, 1]] where
  M :=![![![1, 1, 7, 0, 4], ![16, 24, 1, 6, 0], ![0, 17, 18, 2, 12], ![16, 21, 7, 3, 2], ![4, 24, 18, 6, 9]]]
  hmulB := by decide  
  f := ![![![27, 9, -3, 0, -8]], ![![-32, -8, 9, 10, 0]], ![![8, 3, 0, 2, -4]], ![![-3, 0, 2, 3, -2]], ![![-4, 0, 3, 4, -3]]]
  g := ![![![-5, -3, 7, 0, 4], ![-2, -2, 1, 6, 0], ![-14, -9, 18, 2, 12], ![-5, -3, 7, 3, 2], ![-14, -9, 18, 6, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P1 : CertificateIrreducibleZModOfList' 139 2 2 7 [57, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 138], [0, 1]]
 g := ![![[96, 100], [126, 31], [29], [25, 81], [35], [99], [1]], ![[0, 39], [74, 108], [29], [64, 58], [35], [99], [1]]]
 h' := ![![[88, 138], [46, 129], [128, 93], [104, 53], [78, 130], [108, 70], [82, 88], [0, 1]], ![[0, 1], [0, 10], [111, 46], [42, 86], [120, 9], [13, 69], [42, 51], [88, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [120, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N1 : CertifiedPrimeIdeal' SI139N1 139 where
  n := 2
  hpos := by decide
  P := [57, 51, 1]
  hirr := P139P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1115, 490, -118, -1478, 520]
  a := ![3, -4, 0, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![283, 294, -118, -1478, 520]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N1 B_one_repr
lemma NI139N1 : Nat.card (O ⧸ I139N1) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, -8, -4, 8]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![5, 0, -8, -4, 8]] 
 ![![139, 0, 0, 0, 0], ![102, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![129, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![5, 0, -8, -4, 8], ![32, 29, 4, -32, -8], ![-32, 4, 61, 24, -64], ![-144, -128, -12, 141, 28], ![40, -20, -104, -28, 109]]]
  hmulB := by decide  
  f := ![![![-3249, -2240, 1384, -628, 1048]], ![![-2354, -1627, 1004, -456, 760]], ![![-527, -356, 221, -100, 168]], ![![-3011, -2080, 1284, -583, 972]], ![![-814, -556, 344, -156, 261]]]
  g := ![![![3, 0, -8, -4, 8], ![10, 29, 4, -32, -8], ![-19, 4, 61, 24, -64], ![-43, -128, -12, 141, 28], ![30, -20, -104, -28, 109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![97, 167, -85, 44, -56]] ![![1, 1, 7, 0, 4]]
  ![![3249, 2240, -1384, 628, -1048]] where
 M := ![![![3249, 2240, -1384, 628, -1048]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![3249, 2240, -1384, 628, -1048]] ![![5, 0, -8, -4, 8]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 76, -26, 20, -22]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![97, 76, -26, 20, -22]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![134, 40, 1, 0, 0], ![2, 87, 0, 1, 0], ![49, 69, 0, 0, 1]] where
  M :=![![![97, 76, -26, 20, -22], ![-88, -17, 56, -8, 40], ![160, 128, -9, 32, -16], ![12, 52, 20, 11, 12], ![104, 104, 16, 24, 3]]]
  hmulB := by decide  
  f := ![![![-43, -36, -2, 36, 10]], ![![40, -5, -72, -24, 72]], ![![-26, -32, -21, 24, 28]], ![![22, -3, -40, -13, 40]], ![![1, -17, -34, 4, 37]]]
  g := ![![![31, 6, -26, 20, -22], ![-64, -29, 56, -8, 40], ![14, -8, -9, 32, -16], ![-22, -17, 20, 11, 12], ![-15, -19, 16, 24, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [64, 91, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 148], [0, 1]]
 g := ![![[41, 7], [112], [82, 7], [28], [49, 22], [86], [1]], ![[0, 142], [112], [41, 142], [28], [133, 127], [86], [1]]]
 h' := ![![[58, 148], [30, 56], [116, 75], [45, 56], [142, 112], [82, 97], [85, 58], [0, 1]], ![[0, 1], [0, 93], [145, 74], [15, 93], [82, 37], [46, 52], [22, 91], [58, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135]]
 b := ![[], [54, 142]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [64, 91, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![424, -306, -1447, -129, 2405]
  a := ![1, 0, -3, -1, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![515, -652, -1447, -129, 2405]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, -67, -89, 34, 100]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-25, -67, -89, 34, 100]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![114, 71, 1, 0, 0], ![125, 70, 0, 1, 0], ![90, 146, 0, 0, 1]] where
  M :=![![![-25, -67, -89, 34, 100], ![400, 286, -101, -378, 68], ![272, 571, 664, -338, -756], ![-1712, -1187, 505, 1609, -372], ![-608, -1062, -1066, 708, 1231]]]
  hmulB := by decide  
  f := ![![![2595, 255, -493, 118, -492]], ![![-1968, 134, 137, -2, 236]], ![![1054, 253, -311, 88, -264]], ![![1259, 280, -352, 99, -304]], ![![-362, 280, -162, 68, -65]]]
  g := ![![![-21, -72, -89, 34, 100], ![356, 161, -101, -378, 68], ![234, 587, 664, -338, -756], ![-1523, -640, 505, 1609, -372], ![-526, -1038, -1066, 708, 1231]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P1 : CertificateIrreducibleZModOfList' 149 2 2 7 [25, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 148], [0, 1]]
 g := ![![[86, 6], [16], [74, 119], [114], [134, 26], [73], [1]], ![[0, 143], [16], [57, 30], [114], [109, 123], [73], [1]]]
 h' := ![![[85, 148], [17, 119], [87, 4], [99, 87], [77, 76], [141, 18], [124, 85], [0, 1]], ![[0, 1], [0, 30], [129, 145], [44, 62], [130, 73], [32, 131], [48, 64], [85, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [41, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N1 : CertifiedPrimeIdeal' SI149N1 149 where
  n := 2
  hpos := by decide
  P := [25, 64, 1]
  hirr := P149P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![329, 106, 11, 106, -83]
  a := ![4, 1, 0, 2, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-45, 27, 11, 106, -83]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N1 B_one_repr
lemma NI149N1 : Nat.card (O ⧸ I149N1) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61, -35, 23, -10, 18]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![-61, -35, 23, -10, 18]] 
 ![![149, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-61, -35, 23, -10, 18], ![72, 34, -25, 10, -20], ![-80, -33, 24, -10, 20], ![4, -5, 1, -1, 0], ![-40, -14, 10, -4, 9]]]
  hmulB := by decide  
  f := ![![![39, 15, -21, -38, 2]], ![![10, 4, -5, -10, 0]], ![![10, 3, -6, -10, 0]], ![![-1, -2, -2, 1, 2]], ![![4, 2, -2, -4, 1]]]
  g := ![![![1, -35, 23, -10, 18], ![0, 34, -25, 10, -20], ![0, -33, 24, -10, 20], ![1, -5, 1, -1, 0], ![0, -14, 10, -4, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![97, 76, -26, 20, -22]] ![![-25, -67, -89, 34, 100]]
  ![![39, 15, -21, -38, 2]] where
 M := ![![![39, 15, -21, -38, 2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![39, 15, -21, -38, 2]] ![![-61, -35, 23, -10, 18]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![149, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61, -90, -26, -12, -8]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-61, -90, -26, -12, -8]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![102, 49, 41, 77, 1]] where
  M :=![![![-61, -90, -26, -12, -8], ![-32, -119, -78, -36, -24], ![-96, -206, -83, -108, -72], ![-128, -174, -10, 7, -96], ![-240, -364, -132, 32, -29]]]
  hmulB := by decide  
  f := ![![![29, 14, -10, 4, -8]], ![![-32, -13, 10, -4, 8]], ![![32, 10, -9, 4, -8]], ![![0, 2, -2, 1, 0]], ![![18, 9, -7, 3, -5]]]
  g := ![![![5, 2, 2, 4, -8], ![16, 7, 6, 12, -24], ![48, 22, 19, 36, -72], ![64, 30, 26, 49, -96], ![18, 7, 7, 15, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 4 2 7 [8, 130, 92, 65, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 97, 66, 143], [107, 141, 1, 131], [85, 63, 84, 28], [0, 1]]
 g := ![![[51, 139, 124, 144], [21, 99, 65, 21], [59, 32, 111, 34], [115, 99, 98], [92, 78, 75, 148], [1], []], ![[139, 52, 112, 132, 19, 56], [117, 1, 29, 104, 147, 142], [109, 14, 108, 72, 75, 24], [16, 31, 39], [93, 63, 49, 66, 149, 14], [120, 85, 100], [132, 69, 64]], ![[27, 57, 37, 11, 64, 24], [65, 20, 60, 6, 7, 66], [131, 14, 44, 121, 129, 79], [84, 32, 49], [41, 146, 72, 11, 32, 87], [79, 63, 78], [33, 83, 98]], ![[139, 17, 105, 97, 11, 146], [54, 59, 59, 88, 45, 27], [25, 34, 77, 84, 55, 113], [29, 88, 17], [70, 72, 79, 117, 105, 48], [123, 106, 110], [143, 101, 29]]]
 h' := ![![[45, 97, 66, 143], [134, 10, 83, 139], [132, 139, 62, 126], [45, 3, 42, 51], [19, 13, 90, 20], [143, 21, 59, 86], [0, 0, 1], [0, 1]], ![[107, 141, 1, 131], [143, 14, 60, 139], [66, 147, 123, 110], [121, 37, 132, 86], [20, 78, 140, 103], [140, 41, 142, 145], [63, 78, 65, 10], [45, 97, 66, 143]], ![[85, 63, 84, 28], [91, 118, 37, 28], [116, 103, 146, 93], [1, 39, 54, 143], [89, 91, 83, 144], [93, 13, 105, 107], [11, 3, 49, 57], [107, 141, 1, 131]], ![[0, 1], [124, 9, 122, 147], [134, 64, 122, 124], [19, 72, 74, 22], [141, 120, 140, 35], [93, 76, 147, 115], [41, 70, 36, 84], [85, 63, 84, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6, 38, 111], []]
 b := ![[], [], [80, 87, 53, 149], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 4
  hpos := by decide
  P := [8, 130, 92, 65, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31575054, -98499668, -139711206, 46224972, 156480962]
  a := ![7, 2, -1, 2, -21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-105911478, -51430906, -43413448, -79488802, 156480962]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 519885601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, -14, 10, -4, 8]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-29, -14, 10, -4, 8]] 
 ![![151, 0, 0, 0, 0], ![148, 1, 0, 0, 0], ![142, 0, 1, 0, 0], ![139, 0, 0, 1, 0], ![53, 0, 0, 0, 1]] where
  M :=![![![-29, -14, 10, -4, 8], ![32, 13, -10, 4, -8], ![-32, -10, 9, -4, 8], ![0, -2, 2, -1, 0], ![-16, -4, 4, 0, 3]]]
  hmulB := by decide  
  f := ![![![61, 90, 26, 12, 8]], ![![60, 89, 26, 12, 8]], ![![58, 86, 25, 12, 8]], ![![57, 84, 24, 11, 8]], ![![23, 34, 10, 4, 3]]]
  g := ![![![5, -14, 10, -4, 8], ![-4, 13, -10, 4, -8], ![2, -10, 9, -4, 8], ![1, -2, 2, -1, 0], ![-1, -4, 4, 0, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-61, -90, -26, -12, -8]] ![![-29, -14, 10, -4, 8]]
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


lemma PB171I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB171I3 : PrimesBelowBoundCertificateInterval O 103 151 171 where
  m := 9
  g := ![1, 2, 1, 3, 2, 3, 3, 3, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB171I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2]
    · exact ![I139N0, I139N1, I139N2]
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
    · exact ![14025517307]
    · exact ![141158161, 109]
    · exact ![18424351793]
    · exact ![2048383, 127, 127]
    · exact ![294499921, 131]
    · exact ![18769, 18769, 137]
    · exact ![19321, 19321, 139]
    · exact ![22201, 22201, 149]
    · exact ![519885601, 151]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I109N1, I127N1, I127N2, I131N1, I137N2, I139N2, I149N2, I151N1]
  Il := ![[], [I109N1], [], [I127N1, I127N2], [I131N1], [I137N2], [I139N2], [I149N2], [I151N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
