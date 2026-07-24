
import IdealArithmetic.Examples.NF5_3_1215000000_3.RI5_3_1215000000_3
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


def P107P0 : CertificateIrreducibleZModOfList' 107 5 2 6 [61, 104, 49, 72, 19, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 18, 23, 47, 21], [98, 61, 18, 75, 65], [84, 76, 29, 21, 11], [36, 58, 37, 71, 10], [0, 1]]
 g := ![![[53, 55, 18, 17, 101], [93, 1, 23, 75, 81], [86, 93, 75, 49], [71, 106, 33, 25, 61], [88, 1], []], ![[94, 27, 6, 83, 1, 85, 8, 80], [36, 73, 84, 82, 58, 62, 34, 91], [27, 49, 88, 100], [84, 53, 62, 103, 45, 84, 24, 45], [31, 50, 75, 23], [102, 77, 66, 104, 1, 94, 70, 59]], ![[75, 87, 1, 79, 92, 13, 53, 15], [54, 38, 36, 0, 36, 13, 76, 98], [97, 41, 4, 25], [69, 42, 46, 70, 62, 43, 68, 97], [29, 65, 97, 29], [82, 43, 64, 6, 103, 0, 17, 63]], ![[4, 47, 83, 84, 4, 103, 35, 23], [51, 4, 71, 80, 80, 81, 39, 90], [41, 81, 39, 81], [50, 70, 69, 31, 18, 83, 20, 29], [66, 106, 75, 62], [72, 50, 38, 50, 25, 77, 96, 47]], ![[105, 12, 100, 19, 56, 14, 53, 53], [10, 57, 42, 19, 100, 52, 36, 47], [72, 39, 56, 13], [16, 0, 95, 24, 62, 2, 103, 33], [52, 49], [14, 84, 9, 70, 103, 85, 53, 37]]]
 h' := ![![[84, 18, 23, 47, 21], [105, 48, 55, 37, 84], [30, 36, 31, 53, 98], [56, 63, 37, 26, 7], [89, 96, 78, 35, 75], [0, 0, 0, 1], [0, 1]], ![[98, 61, 18, 75, 65], [10, 5, 37, 94, 96], [50, 20, 69, 26, 19], [29, 80, 83, 78, 10], [46, 43, 50, 54, 72], [15, 100, 2, 34, 39], [84, 18, 23, 47, 21]], ![[84, 76, 29, 21, 11], [69, 28, 89, 91, 62], [25, 53, 71, 17, 47], [59, 89, 31, 27, 102], [12, 67, 76, 70, 24], [47, 34, 11, 2, 55], [98, 61, 18, 75, 65]], ![[36, 58, 37, 71, 10], [50, 5, 73, 82, 83], [77, 91, 23, 50, 73], [44, 57, 53, 52, 9], [74, 35, 9, 99, 32], [26, 78, 19, 77, 13], [84, 76, 29, 21, 11]], ![[0, 1], [94, 21, 67, 17, 103], [87, 14, 20, 68, 84], [29, 32, 10, 31, 86], [74, 80, 1, 63, 11], [6, 2, 75, 100], [36, 58, 37, 71, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 39, 5, 82], [], [], []]
 b := ![[], [56, 61, 44, 68, 98], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 5
  hpos := by decide
  P := [61, 104, 49, 72, 19, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2865552070825, 656219550144, -380774845619, -639071011318, -750657956119]
  a := ![0, 4, 9, -4, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![26780860475, 6132892992, -3558643417, -5972626274, -7015494917]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0, 0, 0]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]] where
  M :=![![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![0, 0, 0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 5 2 6 [77, 76, 52, 32, 67, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 88, 78, 65, 28], [101, 90, 84, 65, 68], [82, 90, 20, 61, 100], [89, 58, 36, 27, 22], [0, 1]]
 g := ![![[95, 26, 54, 58, 64], [20, 106, 44, 25], [106, 106, 99, 45, 97], [44, 10, 66, 94, 35], [42, 1], []], ![[21, 54, 33, 29, 87, 64, 59, 46], [1, 103, 108, 63], [98, 33, 23, 40, 91, 48, 4, 88], [12, 57, 28, 104, 60, 96, 70, 12], [18, 28, 90, 66], [47, 29, 57, 2, 25, 22, 15, 43]], ![[39, 50, 16, 46, 38, 92, 9, 37], [45, 60, 34, 48], [105, 95, 69, 47, 38, 98, 55, 32], [79, 104, 92, 47, 70, 37, 106, 32], [76, 108, 53, 63], [53, 82, 56, 96, 52, 71, 63, 76]], ![[37, 11, 39, 59, 12, 55, 52, 83], [35, 47, 46, 16], [71, 62, 49, 94, 64, 43, 6, 20], [14, 99, 74, 7, 21, 23, 42, 106], [13, 58, 79, 94], [65, 60, 19, 88, 75, 81, 10, 34]], ![[14, 71, 80, 42, 44, 5, 80, 64], [26, 24, 33, 31], [66, 60, 104, 49, 106, 20, 77, 43], [19, 50, 67, 51, 56, 69, 73, 12], [95, 65, 44, 74], [83, 31, 88, 60, 84, 92, 62, 75]]]
 h' := ![![[97, 88, 78, 65, 28], [46, 107, 29, 40, 8], [13, 104, 103, 57, 104], [100, 16, 8, 6, 73], [36, 1, 29, 21, 97], [0, 0, 0, 1], [0, 1]], ![[101, 90, 84, 65, 68], [23, 54, 81, 35, 5], [99, 82, 51, 50, 64], [35, 15, 10, 43, 9], [67, 55, 16, 64, 105], [103, 56, 63, 92, 34], [97, 88, 78, 65, 28]], ![[82, 90, 20, 61, 100], [8, 66, 55, 97, 85], [51, 41, 56, 59, 22], [89, 9, 23, 15, 92], [41, 19, 53, 27, 92], [94, 71, 50, 93, 64], [101, 90, 84, 65, 68]], ![[89, 58, 36, 27, 22], [31, 43, 71, 94, 61], [108, 0, 21, 58, 4], [101, 42, 55, 68, 26], [62, 4, 97, 77, 20], [55, 8, 82, 70, 51], [82, 90, 20, 61, 100]], ![[0, 1], [34, 57, 91, 61, 59], [69, 100, 96, 103, 24], [101, 27, 13, 86, 18], [106, 30, 23, 29, 13], [106, 83, 23, 71, 69], [89, 58, 36, 27, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 48, 68, 14], [], [], []]
 b := ![[], [54, 34, 43, 10, 54], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 5
  hpos := by decide
  P := [77, 76, 52, 32, 67, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![145633196435786135, 35739406816677668, -17159396098209132, -34189615078215734, -41183394730196932]
  a := ![3, -4, 59, -65, -178]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1336084370970515, 327884466208052, -157425652277148, -313666193378126, -377829309451348]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 5 2 6 [46, 104, 15, 54, 104, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 26, 13, 80, 101], [0, 24, 64, 44, 39], [71, 54, 27, 111, 93], [59, 8, 9, 104, 106], [0, 1]]
 g := ![![[10, 77, 3, 65, 62], [76, 98, 44, 60], [104, 9, 88, 95], [100, 52, 78, 7], [27, 9, 1], []], ![[89, 0, 80, 44, 54, 49, 99, 103], [22, 61, 111, 36], [27, 86, 62, 69], [94, 42, 41, 91], [103, 10, 47, 20, 84, 37, 64, 80], [74, 45, 104, 102, 69, 50, 24, 80]], ![[109, 110, 36, 14, 88, 61, 93, 92], [104, 17, 23, 57], [52, 11, 99, 98], [103, 15, 23, 72], [96, 59, 96, 2, 32, 62, 19, 58], [36, 69, 93, 87, 8, 16, 30, 107]], ![[109, 24, 98, 43, 16, 15, 53, 43], [38, 76, 34, 82], [8, 80, 2, 72], [4, 98, 16, 100], [46, 97, 40, 42, 96, 106, 22, 37], [98, 5, 50, 97, 20, 107, 67, 23]], ![[69, 53, 9, 69, 64, 43, 64, 51], [94, 72, 49, 63], [83, 32, 3, 15], [66, 70, 67, 14], [30, 48, 50, 88, 7, 100, 33, 51], [16, 88, 14, 110, 110, 37, 110, 109]]]
 h' := ![![[105, 26, 13, 80, 101], [38, 90, 42, 20, 47], [101, 110, 106, 28, 88], [34, 87, 38, 52, 35], [1, 55, 82, 111, 81], [0, 0, 0, 1], [0, 1]], ![[0, 24, 64, 44, 39], [5, 104, 36, 54, 78], [0, 8, 77, 67, 6], [98, 53, 110, 8, 71], [44, 81, 69, 93, 59], [39, 85, 106, 36, 12], [105, 26, 13, 80, 101]], ![[71, 54, 27, 111, 93], [26, 107, 53, 71, 71], [105, 10, 89, 48, 82], [89, 112, 28, 63, 18], [104, 76, 19, 71, 33], [39, 88, 97, 109, 103], [0, 24, 64, 44, 39]], ![[59, 8, 9, 104, 106], [9, 108, 8, 14, 25], [66, 23, 37, 101, 67], [35, 89, 48, 45, 33], [28, 31, 77, 112, 103], [52, 78, 3, 40, 106], [71, 54, 27, 111, 93]], ![[0, 1], [2, 43, 87, 67, 5], [22, 75, 30, 95, 96], [26, 111, 2, 58, 69], [89, 96, 92, 65, 63], [0, 88, 20, 40, 5], [59, 8, 9, 104, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 41, 64, 7], [], [], []]
 b := ![[], [7, 68, 19, 95, 10], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 5
  hpos := by decide
  P := [46, 104, 15, 54, 104, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![593505615492, 138323904324, -74518480314, -133633521342, -161214092844]
  a := ![1, 1, 6, -5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5252262084, 1224105348, -659455578, -1182597534, -1426673388]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10608988, -6336569, -960706, 631031, 1493833]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-10608988, -6336569, -960706, 631031, 1493833]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![82, 51, 99, 1, 0], ![5, 124, 33, 0, 1]] where
  M :=![![![-10608988, -6336569, -960706, 631031, 1493833], ![-17925996, -10706892, -1623299, 1066254, 2524124], ![-30289488, -18091425, -2742904, 1801650, 4265016], ![-16627098, -9931067, -1505681, 988985, 2341238], ![-26649957, -15917567, -2413298, 1585167, 3752524]]]
  hmulB := by decide  
  f := ![![![289598, -176207, -25344, -21269, 45315]], ![![-543780, 330838, 47591, 39942, -85076]], ![![1020912, -621207, -89350, -74970, 159768]], ![![759038, -461874, -66430, -55737, 118792]], ![![-248771, 151331, 21772, 18278, -38909]]]
  g := ![![![-549785, -1761846, -887632, 631031, 1493833], ![-928972, -2976986, -1499831, 1066254, 2524124], ![-1569684, -5030217, -2534266, 1801650, 4265016], ![-861654, -2761282, -1391150, 988985, 2341238], ![-1381073, -4425780, -2229749, 1585167, 3752524]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [22, 78, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 119, 1], [34, 7, 126], [0, 1]]
 g := ![![[98, 50, 4], [115, 100, 35], [85, 126, 25], [117, 75, 50], [108, 50, 99], [1]], ![[87, 92, 110, 15], [39, 119, 17, 35], [108, 29, 90, 31], [56, 123, 70, 79], [96, 42, 3, 122], [82, 96, 13, 1]], ![[25, 24, 80, 23], [96, 92], [97, 3, 47, 12], [94, 59, 64, 57], [91, 92, 95, 101], [76, 76, 111, 126]]]
 h' := ![![[3, 119, 1], [10, 88, 125], [35, 9, 110], [93, 118, 122], [37, 104, 80], [105, 49, 37], [0, 1]], ![[34, 7, 126], [37, 45, 74], [16, 8, 17], [45, 103, 83], [50, 69, 29], [1, 39, 54], [3, 119, 1]], ![[0, 1], [51, 121, 55], [86, 110], [93, 33, 49], [74, 81, 18], [40, 39, 36], [34, 7, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 89], []]
 b := ![[], [66, 36, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [22, 78, 90, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-606348502, -174140756, 81265053, 168275603, 163264266]
  a := ![1, -8, -30, 18, 87]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-119852514, -228354059, -172958586, 168275603, 163264266]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![289598, -176207, -25344, -21269, 45315]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![289598, -176207, -25344, -21269, 45315]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![109, 56, 1, 0, 0], ![123, 11, 0, 1, 0], ![104, 95, 0, 0, 1]] where
  M :=![![![289598, -176207, -25344, -21269, 45315], ![-543780, 330838, 47591, 39942, -85076], ![1020912, -621207, -89350, -74970, 159768], ![-686718, 417731, 60107, 50447, -107402], ![696717, -424009, -60970, -51147, 109062]]]
  hmulB := by decide  
  f := ![![![-10608988, -6336569, -960706, 631031, 1493833]], ![![-17925996, -10706892, -1623299, 1066254, 2524124]], ![![-17248228, -10302074, -1561926, 1025939, 2428691]], ![![-11958414, -7142558, -1082904, 711296, 1683843]], ![![-22306727, -13323429, -2020001, 1326823, 3140968]]]
  g := ![![![7523, -22267, -25344, -21269, 45315], ![-14143, 41800, 47591, 39942, -85076], ![26500, -78511, -89350, -74970, 159768], ![-17902, 52756, 60107, 50447, -107402], ![18040, -53606, -60970, -51147, 109062]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [20, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 126], [0, 1]]
 g := ![![[90, 64], [15, 34], [36, 62], [86, 81], [95, 31], [105, 1]], ![[79, 63], [29, 93], [69, 65], [82, 46], [48, 96], [83, 126]]]
 h' := ![![[105, 126], [81, 119], [42, 62], [58, 69], [5, 9], [59, 83], [0, 1]], ![[0, 1], [3, 8], [75, 65], [64, 58], [61, 118], [11, 44], [105, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [115, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [20, 22, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-41941, -5232, 15902, 6667, -2002]
  a := ![-1, 11, 13, 5, -34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18796, -6133, 15902, 6667, -2002]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-10608988, -6336569, -960706, 631031, 1493833]] ![![289598, -176207, -25344, -21269, 45315]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20, -57, -26, -5, -3]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-20, -57, -26, -5, -3]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![25, 128, 29, 1, 0], ![96, 24, 4, 0, 1]] where
  M :=![![![-20, -57, -26, -5, -3], ![36, -44, -59, -58, -20], ![240, 15, -8, -158, -232], ![1374, 101, -269, -211, -306], ![1047, 249, -194, -381, -332]]]
  hmulB := by decide  
  f := ![![![-60058, 36541, 5256, 4411, -9397]], ![![112764, -68610, -9869, -8282, 17644]], ![![-211728, 128821, 18530, 15550, -33128]], ![![52936, -32209, -4633, -3888, 8283]], ![![-30921, 18813, 2706, 2271, -4838]]]
  g := ![![![3, 5, 1, -5, -3], ![26, 60, 13, -58, -20], ![202, 197, 42, -158, -232], ![275, 263, 54, -211, -306], ![324, 435, 93, -381, -332]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [38, 120, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [114, 52, 28], [118, 78, 103], [0, 1]]
 g := ![![[128, 36, 74], [2, 99, 101], [8, 25], [43, 84], [61, 36], [101, 1], []], ![[103, 119, 10, 4], [17, 59, 99, 99], [15, 55], [22, 101], [41, 114], [98, 58], [90, 129]], ![[70, 28, 47, 23], [108, 14, 47, 96], [49, 52], [114, 34], [127, 117], [10, 84], [15, 129]]]
 h' := ![![[114, 52, 28], [55, 100, 27], [33, 39, 25], [59, 102, 5], [120, 104, 52], [92, 25, 125], [0, 0, 1], [0, 1]], ![[118, 78, 103], [16, 1, 59], [88, 67, 29], [93, 91, 102], [76, 82, 25], [113, 10, 101], [13, 84, 78], [114, 52, 28]], ![[0, 1], [111, 30, 45], [112, 25, 77], [3, 69, 24], [55, 76, 54], [77, 96, 36], [123, 47, 52], [118, 78, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 125], []]
 b := ![[], [18, 111, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [38, 120, 30, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11717030, -52032, -7501584, -1742832, 4984608]
  a := ![0, -16, -10, -18, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3230798, 789312, 176352, -1742832, 4984608]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-60058, 36541, 5256, 4411, -9397]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-60058, 36541, 5256, 4411, -9397]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![91, 73, 1, 0, 0], ![19, 67, 0, 1, 0], ![126, 30, 0, 0, 1]] where
  M :=![![![-60058, 36541, 5256, 4411, -9397], ![112764, -68610, -9869, -8282, 17644], ![-211728, 128821, 18530, 15550, -33128], ![142386, -86633, -12461, -10457, 22278], ![-144507, 87923, 12646, 10613, -22610]]]
  hmulB := by decide  
  f := ![![![-20, -57, -26, -5, -3]], ![![36, -44, -59, -58, -20]], ![![8, -64, -51, -37, -15]], ![![26, -30, -36, -32, -13]], ![![-3, -63, -40, -21, -10]]]
  g := ![![![4289, -2754, 5256, 4411, -9397], ![-8053, 5171, -9869, -8282, 17644], ![15120, -9709, 18530, 15550, -33128], ![-10168, 6529, -12461, -10457, 22278], ![10320, -6626, 12646, 10613, -22610]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [80, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 130], [0, 1]]
 g := ![![[0, 113], [], [], [], [], [], [1]], ![[0, 18], [], [], [], [], [], [1]]]
 h' := ![![[0, 130], [0, 84], [52], [107], [99], [112], [51], [0, 1]], ![[0, 1], [0, 47], [52], [107], [99], [112], [51], [0, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113]]
 b := ![[], [0, 122]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [80, 0, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-34314, -3818, 11450, 5077, 134]
  a := ![13, 8, 11, 2, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9081, -9037, 11450, 5077, 134]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-20, -57, -26, -5, -3]] ![![-60058, 36541, 5256, 4411, -9397]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-910, -466, -71, 55, 109]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-910, -466, -71, 55, 109]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![64, 41, 1, 0, 0], ![58, 14, 0, 1, 0], ![82, 131, 0, 0, 1]] where
  M :=![![![-910, -466, -71, 55, 109], ![-1308, -927, -140, 76, 220], ![-2640, -1304, -199, 160, 304], ![-1170, -884, -134, 67, 210], ![-2277, -1174, -179, 137, 274]]]
  hmulB := by decide  
  f := ![![![-92, 10, 53, 1, -31]], ![![372, -71, -116, 44, 4]], ![![68, -15, -11, 12, -12]], ![![-10, -2, 16, 5, -16]], ![![311, -63, -83, 43, -14]]]
  g := ![![![-62, -92, -71, 55, 109], ![-108, -183, -140, 76, 220], ![-176, -257, -199, 160, 304], ![-100, -174, -134, 67, 210], ![-155, -231, -179, 137, 274]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [87, 113, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 136], [0, 1]]
 g := ![![[132, 63], [17], [50], [93, 103], [76], [28], [1]], ![[0, 74], [17], [50], [99, 34], [76], [28], [1]]]
 h' := ![![[24, 136], [42, 101], [98, 90], [129, 18], [87, 69], [64, 58], [50, 24], [0, 1]], ![[0, 1], [0, 36], [66, 47], [13, 119], [99, 68], [86, 79], [78, 113], [24, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [65, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [87, 113, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![92, -784, 111, -183, 211]
  a := ![-1, -4, -2, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-100, -222, 111, -183, 211]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![45052, 26423, 3788, -2927, -6539]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![45052, 26423, 3788, -2927, -6539]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![81, 63, 1, 0, 0], ![120, 43, 0, 1, 0], ![26, 69, 0, 0, 1]] where
  M :=![![![45052, 26423, 3788, -2927, -6539], ![78468, 45228, 6121, -5502, -11708], ![140496, 78383, 9400, -11174, -22008], ![92814, 46917, 3289, -9857, -16494], ![139347, 72865, 6394, -13565, -23788]]]
  hmulB := by decide  
  f := ![![![741434, -451097, -64898, -54441, 116001]], ![![-1392012, 846978, 121789, 102206, -217764]], ![![-182682, 111172, 15967, 13411, -28571]], ![![199698, -121477, -17498, -14663, 31250]], ![![-547357, 333049, 47883, 40187, -85624]]]
  g := ![![![1894, 2663, 3788, -2927, -6539], ![3995, 5139, 6121, -5502, -11708], ![9432, 10841, 9400, -11174, -22008], ![10497, 10231, 3289, -9857, -16494], ![13633, 13830, 6394, -13565, -23788]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P1 : CertificateIrreducibleZModOfList' 137 2 2 7 [134, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 136], [0, 1]]
 g := ![![[126, 37], [119], [77], [130, 32], [130], [130], [1]], ![[1, 100], [119], [77], [33, 105], [130], [130], [1]]]
 h' := ![![[104, 136], [115, 41], [124, 16], [116, 112], [123, 124], [125, 33], [3, 104], [0, 1]], ![[0, 1], [132, 96], [7, 121], [119, 25], [4, 13], [132, 104], [133, 33], [104, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [103, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N1 : CertifiedPrimeIdeal' SI137N1 137 where
  n := 2
  hpos := by decide
  P := [134, 33, 1]
  hirr := P137P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-76450, -10661, 22041, 12044, 6660]
  a := ![3, -11, -14, -1, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-25403, -17348, 22041, 12044, 6660]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N1 B_one_repr
lemma NI137N1 : Nat.card (O ⧸ I137N1) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-189775, -113369, -17197, 11278, 26714]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![-189775, -113369, -17197, 11278, 26714]] 
 ![![137, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![-189775, -113369, -17197, 11278, 26714], ![-320568, -191536, -29069, 19034, 45112], ![-541344, -323559, -49156, 32086, 76136], ![-296532, -177457, -27059, 17463, 41616], ![-475662, -284523, -43325, 28080, 66809]]]
  hmulB := by decide  
  f := ![![![-715859, 435499, 62673, 52506, -111954]], ![![-162627, 98933, 14240, 11928, -25434]], ![![-54973, 33454, 4805, 4036, -8598]], ![![-13763, 8366, 1208, 1001, -2146]], ![![-216351, 131618, 18944, 15874, -33841]]]
  g := ![![![18785, -113369, -17197, 11278, 26714], ![31745, -191536, -29069, 19034, 45112], ![53653, -323559, -49156, 32086, 76136], ![29479, -177457, -27059, 17463, 41616], ![47233, -284523, -43325, 28080, 66809]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-910, -466, -71, 55, 109]] ![![45052, 26423, 3788, -2927, -6539]]
  ![![-67245031, -40163651, -6089025, 4000136, 9468924]] where
 M := ![![![-67245031, -40163651, -6089025, 4000136, 9468924]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![-67245031, -40163651, -6089025, 4000136, 9468924]] ![![-189775, -113369, -17197, 11278, 26714]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![23242688525353, 13882467019946, 2104761269602, -1382495088014, -3272761386154]]]
 hmul := by decide  
 g := ![![![![169654660769, 101331876058, 15363220946, -10091205022, -23888769242]]]]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2755, 1509, 247, 234, -346]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-2755, 1509, 247, 234, -346]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![56, 95, 136, 1, 0], ![84, 86, 123, 0, 1]] where
  M :=![![![-2755, 1509, 247, 234, -346], ![4152, -3088, -343, -198, 936], ![-11232, 4943, 1052, 1186, -792], ![2676, -4535, -127, 359, 1904], ![-10290, 2723, 1031, 1432, 197]]]
  hmulB := by decide  
  f := ![![![-109, 3, 19, -14, 6]], ![![-72, -70, 55, 50, -56]], ![![672, -123, -394, -2, 200]], ![![556, -165, -338, 25, 160]], ![![486, -152, -303, 22, 145]]]
  g := ![![![95, 65, 79, 234, -346], ![-456, -466, -637, -198, 936], ![-80, -285, -452, 1186, -792], ![-1276, -1456, -2037, 359, 1904], ![-770, -1081, -1568, 1432, 197]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [109, 61, 126, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 100, 120], [98, 38, 19], [0, 1]]
 g := ![![[113, 31, 77], [69, 20, 28], [55, 34], [85, 97, 71], [29, 127], [13, 1], []], ![[129, 75, 6, 29], [121, 104, 27, 63], [95, 34], [34, 79, 98, 107], [84, 69], [101, 54], [59, 83]], ![[6, 106, 19, 61], [41, 18, 43, 92], [22, 136], [95, 32, 115, 103], [9, 78], [51, 131], [21, 83]]]
 h' := ![![[54, 100, 120], [124, 96, 63], [62, 21, 58], [48, 123, 112], [70, 14, 40], [112, 71, 108], [0, 0, 1], [0, 1]], ![[98, 38, 19], [8, 54, 14], [127, 116, 137], [125, 9, 112], [60, 118, 3], [43, 108, 114], [99, 100, 38], [54, 100, 120]], ![[0, 1], [1, 128, 62], [77, 2, 83], [23, 7, 54], [57, 7, 96], [64, 99, 56], [87, 39, 100], [98, 38, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 58], []]
 b := ![[], [102, 80, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [109, 61, 126, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2566236, -1467266, 141865, 1270481, 1072897]
  a := ![1, -6, -8, -2, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1178680, -1542677, -2191438, 1270481, 1072897]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 8, -14, -10, 14]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![7, 8, -14, -10, 14]] 
 ![![139, 0, 0, 0, 0], ![61, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![7, 8, -14, -10, 14], ![-168, 17, 84, 0, -40], ![480, -124, -143, 88, 0], ![84, 116, -192, -143, 196], ![-390, 0, 246, 46, -153]]]
  hmulB := by decide  
  f := ![![![5041, -872, -118, -346, 246]], ![![2191, -343, -46, -150, 98]], ![![1280, -228, -31, -88, 64]], ![![1272, -180, -24, -87, 52]], ![![2737, -472, -64, -188, 133]]]
  g := ![![![-5, 8, -14, -10, 14], ![-7, 17, 84, 0, -40], ![68, -124, -143, 88, 0], ![-72, 116, -192, -143, 196], ![9, 0, 246, 46, -153]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-739, -441, -67, 44, 104]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![-739, -441, -67, 44, 104]] 
 ![![139, 0, 0, 0, 0], ![84, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![101, 0, 0, 1, 0], ![71, 0, 0, 0, 1]] where
  M :=![![![-739, -441, -67, 44, 104], ![-1248, -746, -113, 74, 176], ![-2112, -1259, -190, 126, 296], ![-1152, -693, -107, 69, 164], ![-1860, -1107, -167, 110, 261]]]
  hmulB := by decide  
  f := ![![![359, 129, -39, -92, -128]], ![![228, 80, -25, -58, -80]], ![![117, 40, -13, -30, -40]], ![![313, 106, -34, -79, -108]], ![![247, 82, -28, -62, -83]]]
  g := ![![![192, -441, -67, 44, 104], ![325, -746, -113, 74, 176], ![548, -1259, -190, 126, 296], ![302, -693, -107, 69, 164], ![482, -1107, -167, 110, 261]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-2755, 1509, 247, 234, -346]] ![![7, 8, -14, -10, 14]]
  ![![359, 129, -39, -92, -128]] where
 M := ![![![359, 129, -39, -92, -128]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![359, 129, -39, -92, -128]] ![![-739, -441, -67, 44, 104]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![172, -138, -13, -3, 41]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![172, -138, -13, -3, 41]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![122, 70, 82, 1, 0], ![64, 49, 82, 0, 1]] where
  M :=![![![172, -138, -13, -3, 41], ![-492, 203, 32, 56, -12], ![144, -528, 43, 40, 224], ![-1098, 84, 128, 239, 86], ![-309, -494, 17, 141, 348]]]
  hmulB := by decide  
  f := ![![![-22846, -13646, -2069, 1359, 3217]], ![![-38604, -23057, -3496, 2296, 5436]], ![![-65232, -38960, -5905, 3880, 9184]], ![![-72982, -43590, -6608, 4341, 10276]], ![![-58793, -35115, -5323, 3497, 8278]]]
  g := ![![![-14, -13, -21, -3, 41], ![-44, -21, -24, 56, -12], ![-128, -96, -145, 40, 224], ![-240, -140, -178, 239, 86], ![-267, -184, -269, 141, 348]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [93, 2, 141, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 51, 121], [78, 97, 28], [0, 1]]
 g := ![![[36, 122, 103], [25, 142], [51, 21, 53], [50, 121], [59, 101, 119], [8, 1], []], ![[3, 105, 54, 132], [117, 81], [49, 59, 49, 69], [13, 42], [103, 52, 10, 88], [7, 22], [138, 39]], ![[88, 98, 56, 33], [58, 24], [54, 53, 0, 25], [50, 22], [139, 34, 90, 123], [43, 68], [82, 39]]]
 h' := ![![[79, 51, 121], [88, 21, 111], [25, 48, 80], [49, 131, 65], [26, 26, 11], [1, 40, 62], [0, 0, 1], [0, 1]], ![[78, 97, 28], [24, 78, 47], [112, 45, 9], [96, 63, 104], [34, 96, 41], [122, 92, 126], [112, 132, 97], [79, 51, 121]], ![[0, 1], [126, 50, 140], [56, 56, 60], [33, 104, 129], [141, 27, 97], [46, 17, 110], [97, 17, 51], [78, 97, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129, 20], []]
 b := ![[], [99, 118, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [93, 2, 141, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-198939, -5256, 97384, 19402, -40012]
  a := ![4, 2, 2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-35, 4008, 11996, 19402, -40012]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22846, 13646, 2069, -1359, -3217]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![22846, 13646, 2069, -1359, -3217]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![81, 134, 1, 0, 0], ![86, 3, 0, 1, 0], ![17, 25, 0, 0, 1]] where
  M :=![![![22846, 13646, 2069, -1359, -3217], ![38604, 23057, 3496, -2296, -5436], ![65232, 38960, 5905, -3880, -9184], ![35802, 21388, 3244, -2131, -5042], ![57393, 34278, 5197, -3413, -8082]]]
  hmulB := by decide  
  f := ![![![-172, 138, 13, 3, -41]], ![![492, -203, -32, -56, 12]], ![![348, -104, -22, -49, -13]], ![![-82, 75, 6, -1, -24]], ![![65, -15, -4, -10, -5]]]
  g := ![![![180, -1202, 2069, -1359, -3217], ![304, -2031, 3496, -2296, -5436], ![515, -3430, 5905, -3880, -9184], ![282, -1885, 3244, -2131, -5042], ![452, -3019, 5197, -3413, -8082]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P1 : CertificateIrreducibleZModOfList' 149 2 2 7 [67, 112, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 148], [0, 1]]
 g := ![![[144, 129], [5], [114, 121], [46], [88, 69], [28], [1]], ![[0, 20], [5], [121, 28], [46], [108, 80], [28], [1]]]
 h' := ![![[37, 148], [143, 125], [110, 81], [120, 11], [64, 116], [80, 101], [82, 37], [0, 1]], ![[0, 1], [0, 24], [127, 68], [80, 138], [35, 33], [92, 48], [110, 112], [37, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [70, 113]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N1 : CertifiedPrimeIdeal' SI149N1 149 where
  n := 2
  hpos := by decide
  P := [67, 112, 1]
  hirr := P149P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1030716, -130006, 228532, 155937, 148150]
  a := ![7, 23, 45, -23, -136]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-238060, -234395, 228532, 155937, 148150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N1 B_one_repr
lemma NI149N1 : Nat.card (O ⧸ I149N1) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![172, -138, -13, -3, 41]] ![![22846, 13646, 2069, -1359, -3217]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0, 0, 0]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![0, 0, 0, 0, 151]] where
  M :=![![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![0, 0, 0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 5 2 7 [124, 136, 5, 80, 148, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 22, 35, 34, 12], [27, 70, 77, 67, 34], [56, 66, 88, 51, 56], [4, 143, 102, 150, 49], [0, 1]]
 g := ![![[64, 100, 15, 87, 45], [97, 54, 143, 116, 42], [43, 67, 92, 13, 74], [24, 146, 138, 16], [78, 146, 80, 3, 1], [], []], ![[64, 88, 86, 37, 56, 40, 50, 60], [95, 7, 149, 89, 141, 104, 101, 133], [28, 113, 47, 128, 144, 3, 130, 140], [77, 87, 28, 38], [42, 94, 57, 125, 100, 74, 66, 67], [133, 4, 65, 124], [70, 109, 40, 144]], ![[104, 5, 37, 143, 123, 7, 88, 94], [3, 0, 38, 140, 2, 85, 64, 32], [49, 107, 85, 12, 46, 101, 58, 74], [140, 67, 43, 55], [106, 105, 39, 2, 96, 53, 136, 18], [81, 54, 88, 62], [85, 56, 21, 99]], ![[32, 118, 1, 6, 134, 144, 68, 92], [56, 44, 27, 18, 36, 39, 31, 96], [83, 123, 15, 92, 140, 8, 142, 146], [0, 34, 64, 118], [125, 12, 30, 123, 65, 29, 4, 134], [130, 61, 50, 138], [41, 66, 20, 116]], ![[68, 45, 50, 79, 19, 64, 58, 21], [33, 19, 1, 147, 110, 39, 10, 22], [150, 108, 150, 97, 84, 71, 26, 84], [70, 81, 38, 64], [107, 128, 130, 138, 19, 82, 82, 118], [24, 11, 44, 105], [98, 47, 8, 136]]]
 h' := ![![[67, 22, 35, 34, 12], [52, 139, 5, 63, 14], [104, 75, 9, 65, 58], [108, 124, 149, 139, 15], [143, 129, 34, 49, 4], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[27, 70, 77, 67, 34], [80, 12, 85, 89, 55], [116, 35, 53, 111, 136], [133, 77, 63, 78, 106], [35, 74, 26, 65, 76], [128, 72, 59, 25, 12], [37, 146, 140, 60, 44], [67, 22, 35, 34, 12]], ![[56, 66, 88, 51, 56], [135, 99, 106, 66, 49], [46, 92, 144, 123, 125], [129, 32, 125, 79, 53], [44, 16, 138, 37, 31], [89, 94, 91, 101, 56], [4, 74, 74, 38, 106], [27, 70, 77, 67, 34]], ![[4, 143, 102, 150, 49], [116, 6, 29, 5, 51], [28, 65, 86, 12, 115], [20, 22, 5, 14, 92], [110, 103, 94, 104, 32], [111, 99, 150, 82, 65], [15, 125, 135, 87, 17], [56, 66, 88, 51, 56]], ![[0, 1], [121, 46, 77, 79, 133], [100, 35, 10, 142, 19], [30, 47, 111, 143, 36], [42, 131, 10, 47, 8], [9, 37, 2, 94, 17], [95, 108, 103, 117, 135], [4, 143, 102, 150, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 82, 14, 82], [], [], []]
 b := ![[], [143, 122, 37, 110, 119], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 5
  hpos := by decide
  P := [124, 136, 5, 80, 148, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11885140445474, 2690460340348, -1705502538498, -2648059509846, -2950261736596]
  a := ![1, 7, 12, -5, -35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![78709539374, 17817618148, -11294718798, -17536817946, -19538157196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 78502725751 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀



lemma PB1705I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB1705I3 : PrimesBelowBoundCertificateInterval O 103 151 1705 where
  m := 9
  g := ![1, 1, 1, 2, 2, 3, 3, 2, 1]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB1705I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2]
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
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
    · exact ![15386239549]
    · exact ![18424351793]
    · exact ![2048383, 16129]
    · exact ![2248091, 17161]
    · exact ![18769, 18769, 137]
    · exact ![2685619, 139, 139]
    · exact ![3307949, 22201]
    · exact ![78502725751]
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
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
  β := ![I137N2, I139N1, I139N2]
  Il := ![[], [], [], [], [], [I137N2], [I139N1, I139N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
