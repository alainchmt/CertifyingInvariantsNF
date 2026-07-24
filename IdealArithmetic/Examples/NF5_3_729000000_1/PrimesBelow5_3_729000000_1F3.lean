
import IdealArithmetic.Examples.NF5_3_729000000_1.RI5_3_729000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 134, 152, 52, -194]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![101, 134, 152, 52, -194]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![96, 103, 29, 24, 1]] where
  M :=![![![101, 134, 152, 52, -194], ![-1940, -1221, -216, 692, 118], ![1180, -1030, -3179, -2380, 4270], ![5240, 3598, 1146, -1579, -1060], ![20, -90, -150, -102, 183]]]
  hmulB := by decide  
  f := ![![![1407, 654, 108, 192, -338]], ![![-3380, -1579, -260, -464, 814]], ![![8140, 3810, 627, 1120, -1970]], ![![-280, -138, -22, -41, 68]], ![![196, 89, 15, 26, -49]]]
  g := ![![![175, 188, 54, 44, -194], ![-124, -125, -34, -20, 118], ![-3820, -4120, -1187, -980, 4270], ![1000, 1054, 298, 223, -1060], ![-164, -177, -51, -42, 183]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 4 2 6 [18, 70, 60, 104, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 54, 87, 97], [44, 96, 61, 4], [34, 63, 66, 6], [0, 1]]
 g := ![![[22, 39, 0, 57], [65, 98, 28, 25], [106, 33, 25], [49, 59, 95, 90], [56, 3, 1], []], ![[29, 34, 81, 68, 72, 78], [42, 81, 91, 31, 46, 78], [7, 69, 42], [70, 86, 27, 32, 78, 24], [4, 68, 35], [9, 68, 52, 71, 95, 70]], ![[7, 17, 100, 10, 23, 39], [13, 31, 38, 32, 37, 3], [51, 0, 11], [11, 105, 98, 87, 28, 19], [96, 51, 61], [71, 49, 4, 103, 17, 64]], ![[91, 47, 101, 94, 51, 43], [102, 24, 102, 12, 7, 45], [21, 68, 16], [14, 8, 88, 100, 77, 17], [2, 35, 57], [95, 6, 30, 29, 72, 2]]]
 h' := ![![[32, 54, 87, 97], [7, 28, 72, 59], [52, 2, 101, 102], [81, 101, 60, 5], [62, 92, 50, 25], [0, 0, 0, 1], [0, 1]], ![[44, 96, 61, 4], [15, 70, 17, 28], [23, 5, 48, 28], [91, 36, 72, 91], [20, 34, 69, 74], [78, 3, 79, 79], [32, 54, 87, 97]], ![[34, 63, 66, 6], [13, 83, 32, 25], [98, 95, 67, 9], [69, 63, 31, 15], [94, 74, 93, 37], [18, 24, 89, 75], [44, 96, 61, 4]], ![[0, 1], [39, 33, 93, 102], [42, 5, 105, 75], [62, 14, 51, 103], [49, 14, 2, 78], [37, 80, 46, 59], [34, 63, 66, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [54, 36, 102], []]
 b := ![[], [], [29, 24, 15, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 4
  hpos := by decide
  P := [18, 70, 60, 104, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14457026058, 19726792658, 1597111319, 5936644167, 7432633068]
  a := ![0, -9, 16, 2, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6533418210, -6970415078, -1999525679, -1611649995, 7432633068]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 131079601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1407, -654, -108, -192, 338]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-1407, -654, -108, -192, 338]] 
 ![![107, 0, 0, 0, 0], ![69, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![53, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![-1407, -654, -108, -192, 338], ![3380, 1579, 260, 464, -814], ![-8140, -3810, -627, -1120, 1970], ![280, 138, 22, 41, -68], ![-4700, -2198, -362, -646, 1139]]]
  hmulB := by decide  
  f := ![![![-101, -134, -152, -52, 194]], ![![-47, -75, -96, -40, 124]], ![![-62, -58, -47, -4, 58]], ![![-99, -100, -86, -11, 106]], ![![-37, -48, -54, -18, 69]]]
  g := ![![![435, -654, -108, -192, 338], ![-1051, 1579, 260, 464, -814], ![2534, -3810, -627, -1120, 1970], ![-93, 138, 22, 41, -68], ![1461, -2198, -362, -646, 1139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![101, 134, 152, 52, -194]] ![![-1407, -654, -108, -192, 338]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0, 0, 0]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]] where
  M :=![![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 5 2 6 [69, 25, 41, 85, 23, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 98, 3, 33, 75], [4, 51, 106, 39, 80], [51, 89, 101, 20, 71], [4, 88, 8, 17, 101], [0, 1]]
 g := ![![[47, 91, 88, 18, 4], [107, 58, 7, 94], [80, 18, 25, 65, 82], [84, 77, 70, 49, 64], [86, 1], []], ![[41, 40, 28, 108, 33, 71, 108, 46], [74, 52, 44, 105], [28, 52, 11, 23, 107, 51, 14, 20], [11, 67, 0, 99, 108, 8, 11, 78], [65, 6, 2, 93], [55, 32, 16, 5, 38, 104, 49, 45]], ![[100, 98, 62, 48, 85, 8, 93, 73], [88, 22, 98, 34], [25, 60, 27, 95, 62, 84, 76, 88], [65, 69, 89, 64, 14, 66, 104, 38], [79, 3, 0, 43], [68, 83, 77, 101, 15, 94, 3, 27]], ![[12, 39, 76, 70, 35, 108, 85, 36], [37, 75, 85, 5], [108, 51, 94, 60, 4, 15, 68, 1], [55, 48, 53, 29, 29, 104, 92, 16], [83, 21, 11, 100], [27, 1, 74, 13, 70, 62, 39, 64]], ![[59, 26, 56, 101, 43, 44, 27, 59], [84, 84, 38, 36], [101, 107, 107, 96, 99, 79, 77, 14], [74, 77, 62, 91, 36, 93, 103, 101], [48, 97, 13, 34], [28, 94, 65, 38, 105, 16, 107, 33]]]
 h' := ![![[27, 98, 3, 33, 75], [24, 12, 1, 82, 2], [39, 62, 8, 14, 58], [90, 14, 85, 98, 55], [61, 70, 46, 61, 8], [0, 0, 0, 1], [0, 1]], ![[4, 51, 106, 39, 80], [2, 44, 67, 103, 55], [51, 11, 76, 40, 43], [104, 42, 4, 91, 50], [6, 38, 77, 28, 7], [83, 46, 104, 11, 23], [27, 98, 3, 33, 75]], ![[51, 89, 101, 20, 71], [81, 37, 35, 26, 21], [102, 51, 104, 17, 90], [22, 63, 47, 102, 11], [101, 95, 94, 59, 5], [59, 35, 73, 68, 77], [4, 51, 106, 39, 80]], ![[4, 88, 8, 17, 101], [38, 104, 104, 26, 83], [56, 106, 29, 93, 21], [75, 28, 15, 96, 77], [85, 35, 30, 8, 90], [97, 47, 59, 97, 99], [51, 89, 101, 20, 71]], ![[0, 1], [8, 21, 11, 90, 57], [38, 97, 1, 54, 6], [12, 71, 67, 49, 25], [74, 89, 80, 62, 108], [94, 90, 91, 41, 19], [4, 88, 8, 17, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 33, 5, 44], [], [], []]
 b := ![[], [12, 20, 98, 100, 59], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 5
  hpos := by decide
  P := [69, 25, 41, 85, 23, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1205097661766635886, -1716692737611970059, -112027931677027827, -570530771218201329, -712535100685290426]
  a := ![3, -125, 119, -69, -298]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11055941851070054, -15749474656990551, -1027779189697503, -5234227258882581, -6537019272342114]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0, 0, 0]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]] where
  M :=![![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![0, 0, 0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 5 2 6 [29, 61, 61, 20, 35, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 10, 47, 79, 64], [94, 57, 21, 80, 45], [105, 84, 91, 68, 10], [4, 74, 67, 112, 107], [0, 1]]
 g := ![![[16, 58, 63, 84, 30], [102, 1, 98, 62], [85, 83, 52, 81], [96, 85, 2, 44], [75, 78, 1], []], ![[65, 21, 23, 30, 89, 70, 105, 105], [26, 18, 41, 63], [20, 1, 23, 57], [26, 61, 83, 77], [68, 38, 101, 5, 57, 55, 26, 88], [76, 106, 55, 19, 95, 11, 77, 97]], ![[33, 47, 78, 37, 62, 52, 10, 39], [51, 72, 36, 52], [58, 8, 9, 49], [27, 30, 96, 41], [8, 10, 26, 104, 27, 100, 70, 5], [66, 99, 105, 69, 96, 25, 37, 47]], ![[22, 67, 38, 28, 70, 94, 17, 27], [1, 20, 66, 1], [24, 22, 70, 22], [59, 10, 109, 14], [26, 0, 14, 63, 94, 33, 2, 55], [34, 60, 49, 67, 83, 38, 90, 96]], ![[33, 4, 65, 48, 14, 9, 54, 84], [1, 99, 51, 8], [42, 102, 59, 105], [102, 99, 24, 28], [37, 73, 46, 79, 95, 51, 82, 38], [13, 22, 53, 102, 109, 109, 107, 10]]]
 h' := ![![[101, 10, 47, 79, 64], [42, 33, 110, 99, 16], [47, 38, 36, 65, 47], [34, 69, 12, 16, 9], [85, 56, 17, 9, 48], [0, 0, 0, 1], [0, 1]], ![[94, 57, 21, 80, 45], [63, 69, 108, 79, 63], [34, 37, 65, 86, 17], [106, 5, 84, 69, 31], [42, 40, 98, 26, 23], [23, 0, 52, 18, 80], [101, 10, 47, 79, 64]], ![[105, 84, 91, 68, 10], [42, 58, 6, 56, 12], [39, 8, 90, 18, 39], [34, 19, 79, 6, 106], [34, 24, 5, 27, 43], [41, 29, 42, 56, 38], [94, 57, 21, 80, 45]], ![[4, 74, 67, 112, 107], [20, 32, 61, 87, 63], [7, 40, 86, 6, 112], [108, 57, 70, 34, 19], [89, 92, 59, 20, 63], [84, 110, 77, 73, 66], [105, 84, 91, 68, 10]], ![[0, 1], [95, 34, 54, 18, 72], [89, 103, 62, 51, 11], [8, 76, 94, 101, 61], [49, 14, 47, 31, 49], [26, 87, 55, 78, 42], [4, 74, 67, 112, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 108, 35, 27], [], [], []]
 b := ![[], [112, 57, 36, 76, 19], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 5
  hpos := by decide
  P := [29, 61, 61, 20, 35, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4193553995013, -5938031194512, -402637401598, -1947964130964, -2429432171976]
  a := ![1, -9, 11, -3, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-37111097301, -52548948624, -3563162846, -17238620628, -21499399752]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, -1, -2, 2]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![1, -1, -1, -2, 2]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![118, 94, 1, 0, 0], ![110, 5, 0, 1, 0], ![106, 115, 0, 0, 1]] where
  M :=![![![1, -1, -1, -2, 2], ![20, 16, 7, 0, -10], ![-100, -55, 6, 30, -10], ![-20, -23, -19, -1, 22], ![-20, -13, -1, -2, 3]]]
  hmulB := by decide  
  f := ![![![87, 17, 5, 4, -14]], ![![-140, -38, -9, -10, 10]], ![![-22, -13, -2, -4, -6]], ![![70, 13, 4, 3, -12]], ![![-54, -21, -4, -6, -3]]]
  g := ![![![1, -1, -1, -2, 2], ![2, 4, 7, 0, -10], ![-24, 3, 6, 30, -10], ![0, -6, -19, -1, 22], ![0, -2, -1, -2, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [86, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 126], [0, 1]]
 g := ![![[111, 62], [22, 121], [8, 107], [42, 52], [96, 41], [106, 1]], ![[79, 65], [21, 6], [47, 20], [93, 75], [124, 86], [85, 126]]]
 h' := ![![[106, 126], [13, 69], [74, 116], [71, 108], [126, 68], [28, 101], [0, 1]], ![[0, 1], [88, 58], [51, 11], [89, 19], [95, 59], [66, 26], [106, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [115, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [86, 21, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![351888, 433303, -35719, 90553, 273765]
  a := ![1, 45, -57, 10, 141]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-270970, -221613, -35719, 90553, 273765]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-283, -147, -23, -44, 76]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-283, -147, -23, -44, 76]] 
 ![![127, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![101, 0, 1, 0, 0], ![101, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![-283, -147, -23, -44, 76], ![760, 394, 61, 118, -188], ![-1880, -885, -148, -260, 520], ![140, 87, 11, 27, -10], ![-1060, -475, -83, -138, 315]]]
  hmulB := by decide  
  f := ![![![-309, -373, -365, -78, 452]], ![![-52, -84, -101, -36, 128]], ![![-247, -264, -227, -24, 276]], ![![-347, -364, -308, -29, 374]], ![![-116, -139, -135, -28, 167]]]
  g := ![![![64, -147, -23, -44, 76], ![-177, 394, 61, 118, -188], ![364, -885, -148, -260, 520], ![-50, 87, 11, 27, -10], ![183, -475, -83, -138, 315]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 1, 1, 0, -6]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![17, 1, 1, 0, -6]] 
 ![![127, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![77, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![17, 1, 1, 0, -6], ![-60, -44, -5, -14, -6], ![-60, -165, -8, -60, -90], ![-60, -93, -5, -31, -42], ![-100, -187, -11, -64, -89]]]
  hmulB := by decide  
  f := ![![![6071, 2863, 467, 838, -1470]], ![![2131, 1005, 164, 294, -516]], ![![3961, 1868, 305, 548, -960]], ![![993, 468, 76, 137, -240]], ![![2027, 956, 156, 280, -491]]]
  g := ![![![1, 1, 1, 0, -6], ![23, -44, -5, -14, -6], ![103, -165, -8, -60, -90], ![55, -93, -5, -31, -42], ![113, -187, -11, -64, -89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2

def I127N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 3, 7, 2, -8]] i)))

def SI127N3: IdealEqSpanCertificate' Table ![![-3, 3, 7, 2, -8]] 
 ![![127, 0, 0, 0, 0], ![77, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![98, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![-3, 3, 7, 2, -8], ![-80, -54, -11, 36, 4], ![40, -55, -158, -130, 220], ![260, 181, 61, -75, -58], ![-20, -13, -9, -8, 15]]]
  hmulB := by decide  
  f := ![![![-2189, -1115, -155, -336, 104]], ![![-1319, -693, -94, -210, 48]], ![![-840, -515, -62, -160, -20]], ![![-1746, -937, -125, -285, 50]], ![![-1119, -666, -82, -206, -13]]]
  g := ![![![-2, 3, 7, 2, -8], ![6, -54, -11, 36, 4], ![85, -55, -158, -130, 220], ![-43, 181, 61, -75, -58], ![10, -13, -9, -8, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N3 : Nat.card (O ⧸ I127N3) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N3)

lemma isPrimeI127N3 : Ideal.IsPrime I127N3 := prime_ideal_of_norm_prime hp127.out _ NI127N3
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![1, -1, -1, -2, 2]] ![![-283, -147, -23, -44, 76]]
  ![![-1563, -780, -124, -232, 394]] where
 M := ![![![-1563, -780, -124, -232, 394]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![-1563, -780, -124, -232, 394]] ![![17, 1, 1, 0, -6]]
  ![![2189, 1115, 155, 336, -104]] where
 M := ![![![2189, 1115, 155, 336, -104]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N2 : IdealMulLeCertificate' Table 
  ![![2189, 1115, 155, 336, -104]] ![![-3, 3, 7, 2, -8]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![-127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91061, -28244, -5898, -7568, 16238]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-91061, -28244, -5898, -7568, 16238]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![90, 35, 66, 126, 1]] where
  M :=![![![-91061, -28244, -5898, -7568, 16238], ![162380, 50499, 10698, 13540, -29170], ![-291700, -91460, -19291, -23240, 52070], ![-29120, -9112, -2316, -2909, 5848], ![-168020, -52212, -10904, -13838, 29937]]]
  hmulB := by decide  
  f := ![![![-2151, -996, -166, -292, 542]], ![![5420, 2689, 422, 800, -1210]], ![![-12100, -4980, -921, -1420, 3590]], ![![880, 792, 76, 257, 112]], ![![-5330, -1731, -396, -460, 1983]]]
  g := ![![![-11851, -4554, -8226, -15676, 16238], ![21280, 8179, 14778, 28160, -29170], ![-38000, -14610, -26381, -50260, 52070], ![-4240, -1632, -2964, -5647, 5848], ![-21850, -8397, -15166, -28900, 29937]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 4 2 7 [4, 115, 61, 61, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 48, 97, 102], [45, 5, 38, 5], [120, 77, 127, 24], [0, 1]]
 g := ![![[122, 53, 2, 102], [78, 24, 19, 99], [50, 71, 81], [66, 98, 16], [119, 17, 53], [1], []], ![[102, 4, 4, 114, 83, 35], [95, 94, 67, 95, 36, 16], [24, 122, 45], [61, 105, 123], [127, 5, 41], [29, 73, 20], [125, 58, 55]], ![[108, 17, 45, 96, 67, 100], [3, 88, 83, 35, 86, 89], [127, 9, 65], [8, 118, 36], [63, 94, 61], [10, 127, 41], [122, 34, 25]], ![[106, 109, 47, 36, 91, 97], [34, 47, 57, 107, 99, 69], [69, 120, 80], [87, 96, 20], [78, 120, 84], [2, 39, 84], [74, 42, 52]]]
 h' := ![![[36, 48, 97, 102], [81, 102, 96, 87], [103, 120, 75, 112], [33, 125, 100, 122], [64, 5, 95, 127], [127, 16, 70, 70], [0, 0, 1], [0, 1]], ![[45, 5, 38, 5], [73, 99, 90, 70], [73, 118, 54, 12], [118, 62, 77, 62], [10, 67, 96, 56], [115, 114, 97, 98], [10, 115, 13, 85], [36, 48, 97, 102]], ![[120, 77, 127, 24], [105, 110, 24, 46], [29, 104, 121, 31], [119, 57, 92, 117], [46, 114, 91, 125], [6, 66, 100, 42], [96, 39, 115, 98], [45, 5, 38, 5]], ![[0, 1], [105, 82, 52, 59], [11, 51, 12, 107], [126, 18, 124, 92], [9, 76, 111, 85], [94, 66, 126, 52], [87, 108, 2, 79], [120, 77, 127, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [113, 112, 46], []]
 b := ![[], [], [22, 37, 47, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 4
  hpos := by decide
  P := [4, 115, 61, 61, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17503530090, 24196093208, 3745483082, 7577129462, 6109421824]
  a := ![-1, -6, 21, 13, -50]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4063697970, -1447585272, -3049437842, -5818397102, 6109421824]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 294499921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2151, 996, 166, 292, -542]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![2151, 996, 166, 292, -542]] 
 ![![131, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![76, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![77, 0, 0, 0, 1]] where
  M :=![![![2151, 996, 166, 292, -542], ![-5420, -2689, -422, -800, 1210], ![12100, 4980, 921, 1420, -3590], ![-880, -792, -76, -257, -112], ![6620, 2348, 496, 642, -2291]]]
  hmulB := by decide  
  f := ![![![91061, 28244, 5898, 7568, -16238]], ![![18919, 5867, 1224, 1572, -3372]], ![![55056, 17084, 3569, 4568, -9818]], ![![9954, 3088, 648, 831, -1780]], ![![54807, 17000, 3550, 4554, -9773]]]
  g := ![![![-13, 996, 166, 292, -542], ![173, -2689, -422, -800, 1210], ![414, 4980, 921, 1420, -3590], ![306, -792, -76, -257, -112], ![521, 2348, 496, 642, -2291]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-91061, -28244, -5898, -7568, 16238]] ![![2151, 996, 166, 292, -542]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-413, -158, 6, 62, 2]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-413, -158, 6, 62, 2]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![67, 30, 32, 1, 0], ![114, 87, 107, 0, 1]] where
  M :=![![![-413, -158, 6, 62, 2], ![20, -299, -342, 6, 374], ![3740, 2430, 57, -1930, 410], ![400, 810, 1034, 411, -1304], ![-240, 6, -30, -112, 119]]]
  hmulB := by decide  
  f := ![![![-642189, -303714, -49694, -89454, 156302]], ![![1563020, 739209, 120950, 217722, -380422]], ![![-3804220, -1799150, -294379, -529910, 925910]], ![![-859319, -406402, -66496, -119699, 209150]], ![![-2529018, -1196061, -195701, -352280, 615539]]]
  g := ![![![-35, -16, -16, 62, 2], ![-314, -241, -296, 6, 374], ![630, 180, 131, -1930, 410], ![887, 744, 930, 411, -1304], ![-46, -51, -67, -112, 119]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [10, 115, 89, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [127, 48, 128], [58, 88, 9], [0, 1]]
 g := ![![[1, 97, 73], [123, 101], [84, 15], [62, 103, 77], [47, 9], [48, 1], []], ![[42, 136, 16, 63], [25, 74], [13, 99], [75, 111, 104, 63], [98, 72], [135, 72], [10, 81]], ![[107, 21, 75, 99], [68, 59], [4, 121], [9, 117, 30, 28], [102, 61], [51, 112], [129, 81]]]
 h' := ![![[127, 48, 128], [96, 93, 115], [97, 56, 52], [65, 78, 17], [44, 35, 25], [68, 87, 134], [0, 0, 1], [0, 1]], ![[58, 88, 9], [125, 67, 104], [85, 41, 99], [107, 136, 109], [105, 57, 104], [20, 58, 49], [0, 94, 88], [127, 48, 128]], ![[0, 1], [3, 114, 55], [86, 40, 123], [117, 60, 11], [83, 45, 8], [125, 129, 91], [19, 43, 48], [58, 88, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 128], []]
 b := ![[], [112, 5, 136], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [10, 115, 89, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9847050, 12121458, 6287290, 2391358, -4856948]
  a := ![0, -2, -18, -26, 44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2943928, 2649162, 3280710, 2391358, -4856948]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![413, 69, 25, 13, -113]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![413, 69, 25, 13, -113]] 
 ![![137, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![88, 0, 1, 0, 0], ![113, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![413, 69, 25, 13, -113], ![-1130, -692, -83, -215, -35], ![-350, -2145, -82, -755, -1325], ![-760, -1263, -79, -429, -568], ![-1060, -2473, -131, -852, -1275]]]
  hmulB := by decide  
  f := ![![![1629, 973, 59, -699, 79]], ![![89, 65, 26, -24, -26]], ![![746, 427, -12, -351, 91]], ![![1381, 794, -8, -626, 143]], ![![508, 303, 17, -220, 27]]]
  g := ![![![9, 69, 25, 13, -113], ![269, -692, -83, -215, -35], ![1208, -2145, -82, -755, -1325], ![646, -1263, -79, -429, -568], ![1315, -2473, -131, -852, -1275]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![377, 216, 30, 66, -60]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![377, 216, 30, 66, -60]] 
 ![![137, 0, 0, 0, 0], ![84, 1, 0, 0, 0], ![68, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![377, 216, 30, 66, -60], ![-600, -67, -42, -6, 336], ![3360, 2880, 287, 930, 300], ![600, 936, 60, 317, 420], ![2580, 2580, 228, 846, 551]]]
  hmulB := by decide  
  f := ![![![-1199, -792, -330, 210, 372]], ![![-708, -475, -210, 114, 240]], ![![-476, -288, -97, 90, 108]], ![![-239, -144, -30, 71, 24]], ![![-312, -204, -84, 54, 95]]]
  g := ![![![-137, 216, 30, 66, -60], ![-30, -67, -42, -6, 336], ![-2078, 2880, 287, 930, 300], ![-749, 936, 60, 317, 420], ![-1926, 2580, 228, 846, 551]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-413, -158, 6, 62, 2]] ![![413, 69, 25, 13, -113]]
  ![![-43369, -15283, -2863, -4231, 6483]] where
 M := ![![![-43369, -15283, -2863, -4231, 6483]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![-43369, -15283, -2863, -4231, 6483]] ![![377, 216, 30, 66, -60]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-2612453, -3823259, -256601, -1289855, -1596735]]]
 hmul := by decide  
 g := ![![![![-19069, -27907, -1873, -9415, -11655]]]]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39319, 12210, 2548, 3247, -7005]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![39319, 12210, 2548, 3247, -7005]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![112, 118, 17, 1, 0], ![135, 138, 50, 0, 1]] where
  M :=![![![39319, 12210, 2548, 3247, -7005], ![-70050, -21749, -4536, -5787, 12477], ![124770, 38730, 8089, 10335, -22245], ![12780, 3960, 816, 1051, -2262], ![72420, 22488, 4694, 5984, -12905]]]
  hmulB := by decide  
  f := ![![![181, 78, 14, 23, -51]], ![![-510, -287, -42, -87, 87]], ![![870, 150, 61, 15, -435]], ![![-182, -164, -17, -54, -21]], ![![-15, -156, -6, -59, -122]]]
  g := ![![![4470, 4286, 2141, 3247, -7005], ![-7959, -7631, -3813, -5787, 12477], ![14175, 13590, 6796, 10335, -22245], ![1442, 1382, 691, 1051, -2262], ![8233, 7894, 3944, 5984, -12905]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [100, 21, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [136, 68, 47], [77, 70, 92], [0, 1]]
 g := ![![[32, 81, 13], [110, 0, 34], [76, 83], [61, 82, 24], [38, 44], [74, 1], []], ![[94, 97, 67, 35], [1, 84, 17, 69], [34, 65], [108, 112, 66, 117], [94, 122], [68, 35], [0, 124]], ![[122, 64, 18, 123], [15, 88], [22, 79], [13, 23, 35, 17], [133, 57], [37, 37], [94, 124]]]
 h' := ![![[136, 68, 47], [120, 26, 98], [23, 26, 112], [16, 6, 120], [69, 133, 118], [106, 14, 34], [0, 0, 1], [0, 1]], ![[77, 70, 92], [90, 86, 20], [119, 84, 27], [105, 93, 64], [37, 12, 55], [92, 133, 119], [9, 119, 70], [136, 68, 47]], ![[0, 1], [12, 27, 21], [110, 29], [124, 40, 94], [79, 133, 105], [69, 131, 125], [4, 20, 68], [77, 70, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104, 81], []]
 b := ![[], [84, 22, 87], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [100, 21, 65, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19262535, -22669666, -2543867, -4107996, -6359999]
  a := ![13, -7, 18, 8, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9348438, 9638516, 2771885, -4107996, -6359999]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 78, 14, 23, -51]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![181, 78, 14, 23, -51]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![64, 108, 1, 0, 0], ![115, 22, 0, 1, 0], ![25, 98, 0, 0, 1]] where
  M :=![![![181, 78, 14, 23, -51], ![-510, -287, -42, -87, 87], ![870, 150, 61, 15, -435], ![-180, -216, -12, -71, -78], ![360, -108, 22, -50, -329]]]
  hmulB := by decide  
  f := ![![![39319, 12210, 2548, 3247, -7005]], ![![-70050, -21749, -4536, -5787, 12477]], ![![-35426, -10998, -2293, -2927, 6309]], ![![21535, 6688, 1396, 1778, -3837]], ![![-41795, -12976, -2706, -3453, 7444]]]
  g := ![![![-15, 22, 14, 23, -51], ![72, -17, -42, -87, 87], ![44, 258, 61, 15, -435], ![77, 74, -12, -71, -78], ![93, 222, 22, -50, -329]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P1 : CertificateIrreducibleZModOfList' 139 2 2 7 [72, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 138], [0, 1]]
 g := ![![[38, 28], [30, 100], [107], [129, 1], [113], [129], [1]], ![[19, 111], [121, 39], [107], [34, 138], [113], [129], [1]]]
 h' := ![![[44, 138], [64, 58], [10, 129], [25, 78], [112, 1], [66, 35], [67, 44], [0, 1]], ![[0, 1], [114, 81], [126, 10], [121, 61], [17, 138], [77, 104], [57, 95], [44, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [109, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N1 : CertifiedPrimeIdeal' SI139N1 139 where
  n := 2
  hpos := by decide
  P := [72, 95, 1]
  hirr := P139P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![758, 441, 185, -973, 185]
  a := ![-1, -3, -3, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![692, -117, 185, -973, 185]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N1 B_one_repr
lemma NI139N1 : Nat.card (O ⧸ I139N1) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![39319, 12210, 2548, 3247, -7005]] ![![181, 78, 14, 23, -51]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0, 0, 0]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![0, 0, 0, 0, 149]] where
  M :=![![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![0, 0, 0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 5 2 7 [112, 130, 44, 130, 19, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [95, 141, 15, 100, 146], [51, 109, 21, 41, 43], [4, 86, 121, 14, 118], [129, 110, 141, 143, 140], [0, 1]]
 g := ![![[67, 63, 119, 2, 127], [63, 0, 9, 112], [119, 25, 50, 113, 85], [110, 136, 66, 54], [76, 123, 82, 130, 1], [], []], ![[95, 70, 21, 140, 71, 8, 139, 32], [97, 55, 55, 25], [61, 28, 80, 66, 58, 143, 78, 98], [65, 68, 56, 20], [64, 52, 68, 105, 116, 33, 42, 18], [116, 78, 3, 86], [148, 145, 123, 9]], ![[118, 38, 145, 133, 30, 109, 109, 90], [32, 126, 105, 96], [126, 128, 134, 35, 47, 13, 100, 91], [94, 109, 138, 4], [27, 94, 135, 5, 98, 84, 5, 71], [147, 80, 17, 123], [98, 52, 132, 61]], ![[54, 49, 91, 109, 135, 23, 58, 107], [10, 29, 105, 47], [44, 140, 64, 73, 99, 66, 18, 28], [45, 91, 11, 113], [3, 49, 32, 144, 76, 133, 53, 121], [7, 122, 89, 142], [31, 78, 94, 67]], ![[37, 111, 62, 46, 43, 127, 41, 61], [4, 111, 31, 104], [5, 6, 139, 51, 92, 67, 61, 129], [2, 113, 99, 19], [146, 128, 69, 52, 86, 88, 47, 112], [138, 65, 123, 104], [105, 2, 59, 81]]]
 h' := ![![[95, 141, 15, 100, 146], [115, 133, 111, 27, 53], [82, 88, 61, 51, 75], [110, 130, 77, 133, 95], [130, 35, 90, 16, 90], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[51, 109, 21, 41, 43], [13, 4, 148, 85, 121], [0, 137, 129, 96, 144], [37, 59, 42, 89, 100], [4, 60, 51, 97, 13], [40, 35, 141, 127, 21], [48, 101, 132, 131, 58], [95, 141, 15, 100, 146]], ![[4, 86, 121, 14, 118], [9, 148, 51, 97, 43], [100, 107, 128, 5, 29], [26, 43, 12, 82, 34], [71, 144, 117, 21, 147], [142, 141, 137, 136, 99], [118, 4, 87, 136, 47], [51, 109, 21, 41, 43]], ![[129, 110, 141, 143, 140], [100, 43, 5, 115, 66], [112, 93, 50, 25, 14], [51, 0, 33, 6, 15], [144, 5, 134, 34, 115], [57, 103, 84, 30, 85], [120, 140, 40, 145, 80], [4, 86, 121, 14, 118]], ![[0, 1], [106, 119, 132, 123, 15], [16, 22, 79, 121, 36], [1, 66, 134, 137, 54], [134, 54, 55, 130, 82], [144, 19, 85, 5, 92], [113, 53, 38, 35, 113], [129, 110, 141, 143, 140]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 138, 65, 93], [], [], []]
 b := ![[], [69, 76, 91, 5, 31], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 5
  hpos := by decide
  P := [112, 130, 44, 130, 19, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![123115496248190, 179783141088660, 16478487063292, 63099720372310, 67527020755420]
  a := ![3, 10, -28, -15, 70]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![826278498310, 1206598262340, 110593872908, 423488056190, 453201481580]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-721, -400, 24, 325, -95]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-721, -400, 24, 325, -95]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![6, 36, 22, 84, 1]] where
  M :=![![![-721, -400, 24, 325, -95], ![-950, -1321, -1470, -465, 1855], ![18550, 11640, 1929, -6815, -935], ![-460, 1770, 3850, 2469, -5110], ![840, 510, 60, -320, -11]]]
  hmulB := by decide  
  f := ![![![-231, -60, -14, -15, 35]], ![![350, 69, 20, 15, -55]], ![![-550, -140, -31, -35, 35]], ![![-140, -70, -10, -21, 10]], ![![-86, -46, -6, -14, -1]]]
  g := ![![![-1, 20, 14, 55, -95], ![-80, -451, -280, -1035, 1855], ![160, 300, 149, 475, -935], ![200, 1230, 770, 2859, -5110], ![6, 6, 2, 4, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 4 2 7 [12, 117, 48, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 146, 111, 42], [100, 95, 68, 85], [55, 60, 123, 24], [0, 1]]
 g := ![![[139, 56, 106, 55], [87, 14, 20, 37], [124, 91, 49, 138], [18], [51, 130, 110, 9], [1], []], ![[57, 121, 65, 47, 49, 76], [143, 43, 61, 28, 33, 47], [128, 98, 86, 19, 146, 47], [69, 115, 138], [21, 121, 52, 110, 19, 144], [37, 96, 91], [146, 106, 103]], ![[142, 18, 120, 121, 78, 148], [136, 117, 33, 121, 93, 121], [46, 74, 5, 99, 48, 55], [63, 28, 88], [41, 88, 123, 97, 73, 78], [100, 80, 118], [128, 2, 128]], ![[143, 58, 99, 12, 83, 122], [91, 127, 149, 50, 64, 71], [131, 25, 75, 104, 42, 133], [6, 98, 91], [112, 64, 104, 6, 150, 52], [90, 66, 139], [30, 99, 123]]]
 h' := ![![[144, 146, 111, 42], [13, 103, 76, 120], [22, 105, 70, 43], [150, 54, 53, 134], [143, 16, 138], [139, 34, 103, 148], [0, 0, 1], [0, 1]], ![[100, 95, 68, 85], [48, 145, 99, 3], [72, 132, 76, 98], [52, 86, 91, 98], [124, 89, 131, 134], [112, 141, 76, 146], [109, 138, 22, 53], [144, 146, 111, 42]], ![[55, 60, 123, 24], [2, 113, 77, 109], [56, 20, 50, 107], [30, 55, 106, 27], [129, 105, 105, 115], [72, 0, 135, 74], [8, 74, 64, 119], [100, 95, 68, 85]], ![[0, 1], [1, 92, 50, 70], [83, 45, 106, 54], [113, 107, 52, 43], [51, 92, 79, 53], [68, 127, 139, 85], [98, 90, 64, 130], [55, 60, 123, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [50, 114, 37], []]
 b := ![[], [], [68, 30, 105, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 4
  hpos := by decide
  P := [12, 117, 48, 3, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3919537921, 5208602705, 623312725, 1467854669, 1577021596]
  a := ![1, 5, -13, -6, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-36705905, -341484601, -225636837, -867562645, 1577021596]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 519885601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![231, 60, 14, 15, -35]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![231, 60, 14, 15, -35]] 
 ![![151, 0, 0, 0, 0], ![99, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![129, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![231, 60, 14, 15, -35], ![-350, -69, -20, -15, 55], ![550, 140, 31, 35, -35], ![140, 70, 10, 21, -10], ![340, 110, 20, 30, -9]]]
  hmulB := by decide  
  f := ![![![721, 400, -24, -325, 95]], ![![479, 271, -6, -210, 50]], ![![-56, -40, -15, 15, 15]], ![![619, 330, -46, -294, 115]], ![![343, 190, -12, -155, 46]]]
  g := ![![![-35, 60, 14, 15, -35], ![31, -69, -20, -15, 55], ![-104, 140, 31, 35, -35], ![-59, 70, 10, 21, -10], ![-93, 110, 20, 30, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-721, -400, 24, 325, -95]] ![![231, 60, 14, 15, -35]]
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


lemma PB1321I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB1321I3 : PrimesBelowBoundCertificateInterval O 103 151 1321 where
  m := 9
  g := ![2, 1, 1, 4, 2, 3, 2, 1, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB1321I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N2, I127N3]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2]
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
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
    · exact ![131079601, 107]
    · exact ![15386239549]
    · exact ![18424351793]
    · exact ![16129, 127, 127, 127]
    · exact ![294499921, 131]
    · exact ![2571353, 137, 137]
    · exact ![2685619, 19321]
    · exact ![73439775749]
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I107N1, I127N1, I127N2, I127N3, I131N1, I137N1, I137N2, I151N1]
  Il := ![[I107N1], [], [], [I127N1, I127N2, I127N3], [I131N1], [I137N1, I137N2], [], [], [I151N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
