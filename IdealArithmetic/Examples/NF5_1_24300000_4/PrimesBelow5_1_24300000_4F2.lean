
import IdealArithmetic.Examples.NF5_1_24300000_4.RI5_1_24300000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17679, 8215, -9933, -4468, 8302]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-17679, 8215, -9933, -4468, 8302]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![11, 52, 21, 1, 0], ![37, 30, 54, 0, 1]] where
  M :=![![![-17679, 8215, -9933, -4468, 8302], ![33208, -23778, 24819, -3262, -8936], ![-35744, 45829, -41650, 31766, -6524], ![-29652, -14187, 3981, -46543, 36234], ![55864, -6101, 16731, 41846, -42075]]]
  hmulB := by decide  
  f := ![![![-1925, -2191, -1521, -1820, -1246]], ![![-4984, -6512, -4683, -5534, -3640]], ![![-14560, -18841, -13792, -16646, -11068]], ![![-9041, -11689, -8478, -10141, -6720]], ![![-15435, -19820, -14424, -17350, -11541]]]
  g := ![![![-4115, -127, -5439, -4468, 8302], ![5966, 6178, 8595, -3262, -8936], ![-2146, -21049, -5320, 31766, -6524], ![-12811, 19687, -14556, -46543, 36234], ![17199, -13729, 21045, 41846, -42075]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [66, 18, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 27, 59], [43, 39, 8], [0, 1]]
 g := ![![[39, 36, 39], [36, 51, 1], [64, 55], [59, 36], [15, 1], []], ![[45, 29, 51, 15], [53, 38, 40, 39], [42, 59], [44, 6], [29, 47], [59, 64]], ![[36, 37, 64, 5], [4, 55, 32, 31], [23, 40], [21, 65], [13, 59], [43, 64]]]
 h' := ![![[39, 27, 59], [36, 30, 21], [52, 18, 1], [16, 16, 16], [15, 66, 6], [0, 0, 1], [0, 1]], ![[43, 39, 8], [15, 25, 43], [56, 53, 29], [58, 3, 27], [9, 55, 41], [39, 36, 39], [39, 27, 59]], ![[0, 1], [54, 12, 3], [38, 63, 37], [22, 48, 24], [1, 13, 20], [16, 31, 27], [43, 39, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 31], []]
 b := ![[], [45, 46, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [66, 18, 52, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-441002, -560972, -419424, -481984, -350552]
  a := ![0, -8, -3, -4, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![266138, 522668, 427344, -481984, -350552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1925, -2191, -1521, -1820, -1246]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-1925, -2191, -1521, -1820, -1246]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![48, 25, 1, 0, 0], ![3, 47, 0, 1, 0], ![11, 51, 0, 0, 1]] where
  M :=![![![-1925, -2191, -1521, -1820, -1246], ![-4984, -6512, -4683, -5534, -3640], ![-14560, -18841, -13792, -16646, -11068], ![-19644, -24777, -18147, -22093, -14826], ![-27160, -34099, -24873, -30206, -20273]]]
  hmulB := by decide  
  f := ![![![-17679, 8215, -9933, -4468, 8302]], ![![33208, -23778, 24819, -3262, -8936]], ![![-808, -2303, 1523, -3944, 2516]], ![![22061, -16524, 17025, -3183, -5356]], ![![23209, -16842, 17511, -2592, -6067]]]
  g := ![![![1347, 2760, -1521, -1820, -1246], ![4126, 8303, -4683, -5534, -3640], ![12226, 24967, -13792, -16646, -11068], ![16131, 33185, -18147, -22093, -14826], ![22095, 45393, -24873, -30206, -20273]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [11, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 66], [0, 1]]
 g := ![![[46, 25], [60, 29], [25], [14], [29], [1]], ![[59, 42], [59, 38], [25], [14], [29], [1]]]
 h' := ![![[30, 66], [10, 5], [47, 37], [56, 5], [3, 9], [56, 30], [0, 1]], ![[0, 1], [26, 62], [18, 30], [5, 62], [5, 58], [18, 37], [30, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [65, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [11, 37, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10531, 34571, -1069, 12056, 25520]
  a := ![3, -61, 2, -65, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4121, -26968, -1069, 12056, 25520]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-17679, 8215, -9933, -4468, 8302]] ![![-1925, -2191, -1521, -1820, -1246]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0, 0, 0]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]] where
  M :=![![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 5 2 6 [24, 44, 61, 59, 49, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 25, 60, 23, 16], [6, 2, 35, 10, 45], [8, 13, 22, 9, 61], [56, 30, 25, 29, 20], [0, 1]]
 g := ![![[2, 40, 24, 25, 6], [70, 37, 38, 64, 57], [14, 26, 5, 53, 3], [39, 70, 22, 1], [], []], ![[67, 51, 56, 38, 56, 43, 61, 32], [35, 70, 4, 9, 9, 33, 15, 36], [48, 33, 58, 14, 20, 24, 35, 54], [58, 57, 55, 16], [4, 51, 60, 64], [17, 67, 49, 43]], ![[48, 14, 41, 0, 9, 16, 6, 36], [26, 27, 67, 51, 43, 61, 51, 15], [6, 63, 32, 13, 44, 19, 23, 3], [21, 15, 4, 50], [4, 36, 37, 45], [6, 9, 10, 37]], ![[49, 30, 65, 38, 57, 49, 52, 44], [32, 25, 69, 66, 20, 46, 16, 28], [44, 40, 12, 9, 0, 46, 45, 69], [33, 22, 53, 64], [27, 27, 41, 19], [10, 54, 32, 29]], ![[70, 50, 31, 33, 57, 23, 38, 3], [17, 43, 14, 42, 50, 5, 13, 60], [53, 47, 32, 20, 32, 59, 0, 43], [0, 58, 54, 54], [29, 16, 29, 1], [11, 52, 20, 45]]]
 h' := ![![[23, 25, 60, 23, 16], [24, 14, 62, 57, 52], [19, 65, 55, 33, 25], [58, 12, 48, 34, 28], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[6, 2, 35, 10, 45], [8, 56, 28, 35, 12], [19, 13, 24, 26, 37], [57, 70, 31, 64, 32], [61, 49, 20, 25, 4], [50, 1, 70, 40, 8], [23, 25, 60, 23, 16]], ![[8, 13, 22, 9, 61], [2, 46, 24, 60, 50], [25, 19, 43, 10, 38], [18, 51, 9, 19, 44], [66, 44, 60, 24, 60], [34, 41, 61, 17, 20], [6, 2, 35, 10, 45]], ![[56, 30, 25, 29, 20], [15, 44, 17, 37, 33], [36, 32, 42, 48, 14], [39, 58, 21, 23, 25], [11, 41, 63, 27, 63], [37, 34, 33, 53, 44], [8, 13, 22, 9, 61]], ![[0, 1], [39, 53, 11, 24, 66], [58, 13, 49, 25, 28], [19, 22, 33, 2, 13], [44, 8, 70, 66, 14], [32, 66, 48, 32, 70], [56, 30, 25, 29, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 28, 21, 15], [], [], []]
 b := ![[], [45, 33, 57, 52, 39], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 5
  hpos := by decide
  P := [24, 44, 61, 59, 49, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1350103482, -1708573536, -1246582074, -1508157718, -1007677440]
  a := ![1, -6, -1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19015542, -24064416, -17557494, -21241658, -14192640]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 1804229351 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1467, -675, 819, 380, -694]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![1467, -675, 819, 380, -694]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![66, 64, 41, 1, 0], ![68, 58, 30, 0, 1]] where
  M :=![![![1467, -675, 819, 380, -694], ![-2776, 1972, -2063, 250, 760], ![3040, -3829, 3492, -2606, 500], ![2388, 1227, -383, 3867, -2986], ![-4584, 457, -1341, -3494, 3487]]]
  hmulB := by decide  
  f := ![![![19, -47, -67, -100, -62]], ![![-248, -210, -171, -258, -200]], ![![-800, -877, -610, -742, -516]], ![![-662, -736, -565, -747, -530]], ![![-524, -593, -465, -622, -441]]]
  g := ![![![323, 209, 83, 380, -694], ![-972, -796, -481, 250, 760], ![1932, 1835, 1306, -2606, 500], ![-682, -1001, -950, 3867, -2986], ![-152, 299, 511, -3494, 3487]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [32, 55, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 68, 23], [47, 4, 50], [0, 1]]
 g := ![![[35, 67, 64], [43, 2], [4, 57], [3, 48, 8], [22, 1], []], ![[3, 61, 26, 48], [34, 70], [16, 27], [30, 49, 55, 55], [40, 16], [20, 18]], ![[14, 22, 29, 38], [11, 65], [15, 41], [51, 42, 43, 9], [14, 25], [66, 18]]]
 h' := ![![[48, 68, 23], [66, 61, 65], [36, 65, 32], [50, 70, 38], [26, 72, 64], [0, 0, 1], [0, 1]], ![[47, 4, 50], [48, 7, 57], [48, 33, 17], [66, 66, 10], [40, 64, 14], [58, 34, 4], [48, 68, 23]], ![[0, 1], [40, 5, 24], [63, 48, 24], [18, 10, 25], [55, 10, 68], [24, 39, 68], [47, 4, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 32], []]
 b := ![[], [15, 7, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [32, 55, 51, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5342131, 6706504, 4916949, 5944848, 3941930]
  a := ![1, 26, 4, 18, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8973549, -8251996, -4891503, 5944848, 3941930]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 47, 67, 100, 62]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-19, 47, 67, 100, 62]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![22, 64, 1, 0, 0], ![26, 44, 0, 1, 0], ![27, 29, 0, 0, 1]] where
  M :=![![![-19, 47, 67, 100, 62], ![248, 210, 171, 258, 200], ![800, 877, 610, 742, 516], ![908, 1229, 869, 997, 642], ![1160, 1603, 1171, 1382, 897]]]
  hmulB := by decide  
  f := ![![![-1467, 675, -819, -380, 694]], ![![2776, -1972, 2063, -250, -760]], ![![1950, -1473, 1514, -298, -464]], ![![1118, -965, 957, -339, -170]], ![![623, -540, 535, -192, -93]]]
  g := ![![![-79, -143, 67, 100, 62], ![-214, -382, 171, 258, 200], ![-628, -1175, 610, 742, 516], ![-842, -1601, 869, 997, 642], ![-1161, -2194, 1171, 1382, 897]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [35, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 72], [0, 1]]
 g := ![![[67, 48], [2], [67], [37, 19], [8], [1]], ![[0, 25], [2], [67], [12, 54], [8], [1]]]
 h' := ![![[64, 72], [26, 11], [60, 41], [19, 40], [69, 47], [38, 64], [0, 1]], ![[0, 1], [0, 62], [56, 32], [24, 33], [11, 26], [46, 9], [64, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [15, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [35, 9, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1237, 3600, 648, 3258, 920]
  a := ![-1, -6, -4, 5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1679, -2848, 648, 3258, 920]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![1467, -675, 819, 380, -694]] ![![-19, 47, 67, 100, 62]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![-73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1395, 1073, -1098, 240, 317]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-1395, 1073, -1098, 240, 317]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![27, 46, 8, 3, 1]] where
  M :=![![![-1395, 1073, -1098, 240, 317], ![1268, -1936, 1707, -1562, 480], ![1920, 1893, -976, 4374, -3124], ![-6882, 2065, -3031, -3319, 4134], ![7634, -3581, 4313, 1884, -3559]]]
  hmulB := by decide  
  f := ![![![37, 7, -8, -14, -5]], ![![-20, 10, -3, -26, -28]], ![![-112, -77, -46, -62, -52]], ![![-94, -141, -89, -85, -48]], ![![-15, -7, -14, -31, -26]]]
  g := ![![![-126, -171, -46, -9, 317], ![-148, -304, -27, -38, 480], ![1092, 1843, 304, 174, -3124], ![-1500, -2381, -457, -199, 4134], ![1313, 2027, 415, 159, -3559]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 4 2 6 [32, 68, 13, 14, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 65, 58, 40], [62, 78, 29, 59], [28, 14, 71, 59], [0, 1]]
 g := ![![[23, 0, 27, 42], [22, 63, 30, 11], [10, 21, 38, 16], [2, 60, 69, 38], [1], []], ![[50, 6, 31, 9, 3, 50], [7, 55, 4, 54, 16, 2], [53, 68, 56, 34, 33, 46], [52, 37, 27, 66, 0, 21], [5, 73, 25], [36, 15, 20]], ![[9, 15, 46, 76, 6, 70], [67, 20, 64, 62, 39, 12], [55, 5, 20, 70, 73, 34], [31, 73, 55, 35, 52, 47], [16, 33, 10], [24, 34, 5]], ![[54, 21, 35, 21, 1, 35], [4, 45, 56, 58, 30, 48], [7, 7, 32, 47, 71, 29], [54, 46, 28, 78, 77, 54], [12, 4, 52], [47, 13, 5]]]
 h' := ![![[54, 65, 58, 40], [7, 59, 10, 11], [75, 58, 78, 66], [15, 74, 13, 4], [47, 11, 66, 65], [0, 0, 1], [0, 1]], ![[62, 78, 29, 59], [41, 7, 67, 10], [10, 27, 64, 2], [56, 22, 56, 48], [42, 47, 71, 11], [26, 63, 66, 5], [54, 65, 58, 40]], ![[28, 14, 71, 59], [0, 20, 72, 6], [77, 21, 4, 30], [6, 5, 13, 38], [66, 68, 0, 72], [74, 0, 23, 57], [62, 78, 29, 59]], ![[0, 1], [28, 72, 9, 52], [46, 52, 12, 60], [2, 57, 76, 68], [13, 32, 21, 10], [70, 16, 68, 17], [28, 14, 71, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [75, 21, 15], []]
 b := ![[], [], [11, 78, 63, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 4
  hpos := by decide
  P := [32, 68, 13, 14, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22645016, -30017968, 17427300, -62559308, 43314068]
  a := ![0, -2, 4, -18, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15090188, -25600824, -4165636, -2436728, 43314068]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 38950081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, -7, 8, 14, 5]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-37, -7, 8, 14, 5]] 
 ![![79, 0, 0, 0, 0], ![73, 1, 0, 0, 0], ![43, 0, 1, 0, 0], ![53, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-37, -7, 8, 14, 5], ![20, -10, 3, 26, 28], ![112, 77, 46, 62, 52], ![94, 141, 89, 85, 48], ![86, 163, 117, 124, 71]]]
  hmulB := by decide  
  f := ![![![1395, -1073, 1098, -240, -317]], ![![1273, -967, 993, -202, -299]], ![![735, -608, 610, -186, -133]], ![![1023, -746, 775, -119, -265]], ![![-26, -9, 1, -36, 29]]]
  g := ![![![-8, -7, 8, 14, 5], ![-11, -10, 3, 26, 28], ![-139, 77, 46, 62, 52], ![-237, 141, 89, 85, 48], ![-300, 163, 117, 124, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-1395, 1073, -1098, 240, 317]] ![![-37, -7, 8, 14, 5]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11249, -4304, 5639, 4132, -6019]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![11249, -4304, 5639, 4132, -6019]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![67, 78, 1, 0, 0], ![43, 63, 0, 1, 0], ![6, 55, 0, 0, 1]] where
  M :=![![![11249, -4304, 5639, 4132, -6019], ![-24076, 15001, -16342, -760, 8264], ![33056, -32914, 31529, -16156, -1520], ![8998, 15954, -9806, 30389, -20288], ![-28538, -2854, -4140, -29714, 26257]]]
  hmulB := by decide  
  f := ![![![-2923, -2152, -883, -690, -577]], ![![-2308, -5073, -3306, -2920, -1380]], ![![-4595, -6624, -3914, -3414, -1833]], ![![-3393, -5107, -3077, -2721, -1451]], ![![-1936, -3731, -2410, -2182, -1095]]]
  g := ![![![-6122, -4499, 5639, 4132, -6019], ![12698, 10639, -16342, -760, 8264], ![-16573, -16756, 31529, -16156, -1520], ![-6253, -215, -9806, 30389, -20288], ![16494, 9011, -4140, -29714, 26257]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [31, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 82], [0, 1]]
 g := ![![[37, 75], [81, 61], [7], [77], [38, 59], [1]], ![[0, 8], [0, 22], [7], [77], [10, 24], [1]]]
 h' := ![![[15, 82], [62, 18], [14, 71], [27, 67], [67, 34], [52, 15], [0, 1]], ![[0, 1], [0, 65], [0, 12], [36, 16], [79, 49], [28, 68], [15, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [70, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [31, 68, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2314, 1736, 578, 2338, -442]
  a := ![13, -6, -3, 2, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1618, -2004, 578, 2338, -442]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-131853, -56006, 12477, -197076, 155473]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-131853, -56006, 12477, -197076, 155473]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![49, 27, 1, 0, 0], ![44, 34, 0, 1, 0], ![80, 20, 0, 0, 1]] where
  M :=![![![-131853, -56006, 12477, -197076, 155473], ![621892, -160979, 254940, 335900, -394152], ![-1576608, 818580, -949283, -278424, 671800], ![1032654, -985768, 953620, -445433, -81348], ![-473642, 810236, -701702, 704322, -248357]]]
  hmulB := by decide  
  f := ![![![12943, 32770, 23371, 23002, 11779]], ![![47116, 71095, 56328, 70300, 46004]], ![![25185, 45121, 34086, 38914, 23613]], ![![29266, 50238, 38142, 44227, 27278]], ![![27922, 53892, 39820, 43554, 25397]]]
  g := ![![![-54334, 38533, 12477, -197076, 155473], ![58824, -127493, 254940, 335900, -394152], ![41505, 270839, -949283, -278424, 671800], ![-235998, -120022, 953620, -445433, -81348], ![274556, 9354, -701702, 704322, -248357]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [58, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 82], [0, 1]]
 g := ![![[24, 37], [59, 65], [12], [38], [7, 29], [1]], ![[63, 46], [49, 18], [12], [38], [60, 54], [1]]]
 h' := ![![[19, 82], [64, 55], [31, 56], [35, 26], [9, 72], [25, 19], [0, 1]], ![[0, 1], [30, 28], [16, 27], [31, 57], [49, 11], [54, 64], [19, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [78, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [58, 64, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-175, 594, -55, 146, 582]
  a := ![-1, 0, 2, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-608, -175, -55, 146, 582]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-135, 116, -115, 40, 21]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![-135, 116, -115, 40, 21]] 
 ![![83, 0, 0, 0, 0], ![61, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![82, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-135, 116, -115, 40, 21], ![84, -189, 158, -188, 80], ![320, 134, -29, 476, -376], ![-794, 290, -388, -311, 436], ![830, -434, 502, 142, -351]]]
  hmulB := by decide  
  f := ![![![1373, 1604, 1231, 1602, 1119]], ![![1063, 1243, 951, 1234, 861]], ![![386, 466, 349, 440, 302]], ![![1556, 1842, 1404, 1809, 1256]], ![![274, 350, 256, 310, 207]]]
  g := ![![![-107, 116, -115, 40, 21], ![299, -189, 158, -188, 80], ![-560, 134, -29, 476, -376], ![150, 290, -388, -311, 436], ![104, -434, 502, 142, -351]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![11249, -4304, 5639, 4132, -6019]] ![![-131853, -56006, 12477, -197076, 155473]]
  ![![-5932552551, -4271189118, 1853987354, -11312497734, 8392357032]] where
 M := ![![![-5932552551, -4271189118, 1853987354, -11312497734, 8392357032]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![-5932552551, -4271189118, 1853987354, -11312497734, 8392357032]] ![![-135, 116, -115, 40, 21]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![16983170199109, -6555394341926, 8555842380311, 6158080926466, -9041344308371]]]
 hmul := by decide  
 g := ![![![![204616508423, -78980654722, 103082438317, 74193746102, -108931859137]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1385, -34953, -15601, 3384, 13030]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![1385, -34953, -15601, 3384, 13030]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![36, 60, 24, 5, 1]] where
  M :=![![![1385, -34953, -15601, 3384, 13030], ![52120, 2198, -8893, -5142, 6768], ![27072, 44853, 15734, -4250, -10284], ![-46628, 13037, 16589, 8021, -7634], ![-41328, -15925, 3331, 11526, 4637]]]
  hmulB := by decide  
  f := ![![![-13559, 7987, -8863, -1072, 5022]], ![![20088, -18472, 18031, -7682, -2144]], ![![-8576, 28293, -22760, 31774, -15364]], ![![-40772, 1773, -10233, -34283, 32846]], ![![4080, -1684, 2136, 1327, -2085]]]
  g := ![![![-5255, -9177, -3689, -694, 13030], ![-2152, -4538, -1925, -438, 6768], ![4464, 7437, 2950, 530, -10284], ![2564, 5293, 2245, 519, -7634], ![-2340, -3305, -1213, -131, 4637]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [61, 73, 5, 11, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 14, 1, 63], [86, 24, 52, 87], [42, 50, 36, 28], [0, 1]]
 g := ![![[30, 29, 17, 44], [33, 8, 25], [83, 54, 50], [60, 12, 87, 17], [78, 1], []], ![[22, 67, 38, 44, 17, 74], [50, 34, 20], [81, 36, 78], [67, 38, 66, 23, 43, 46], [59, 32, 17, 34, 22, 74], [30, 77, 53]], ![[10, 71, 34, 67, 14, 85], [2, 40, 5], [32, 38, 22], [42, 59, 86, 66, 21, 34], [57, 35, 30, 31, 30, 21], [20, 15, 4]], ![[29, 42, 78, 63, 51, 74], [36, 59, 42], [35, 17, 34], [45, 32, 53, 68, 33, 31], [77, 67, 44, 36, 66, 35], [62, 67, 72]]]
 h' := ![![[39, 14, 1, 63], [18, 30, 52, 69], [42, 2, 34, 84], [78, 40, 46, 53], [48, 30, 71, 27], [0, 0, 1], [0, 1]], ![[86, 24, 52, 87], [8, 15, 67, 87], [11, 6, 88, 51], [18, 40, 78, 16], [49, 22, 3, 63], [47, 79, 81, 2], [39, 14, 1, 63]], ![[42, 50, 36, 28], [51, 41, 85, 25], [23, 1, 47, 19], [62, 44, 86, 72], [57, 27, 44, 61], [35, 62, 71, 52], [86, 24, 52, 87]], ![[0, 1], [29, 3, 63, 86], [0, 80, 9, 24], [34, 54, 57, 37], [9, 10, 60, 27], [29, 37, 25, 35], [42, 50, 36, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [31, 12, 35], []]
 b := ![[], [], [7, 73, 75, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 4
  hpos := by decide
  P := [61, 73, 5, 11, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![840785695, 1113348182, 790200460, 960474384, 667869012]
  a := ![3, 10, 7, -1, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-260702233, -437739242, -171220852, -26728884, 667869012]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13559, 7987, -8863, -1072, 5022]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-13559, 7987, -8863, -1072, 5022]] 
 ![![89, 0, 0, 0, 0], ![79, 1, 0, 0, 0], ![78, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![-13559, 7987, -8863, -1072, 5022], ![20088, -18472, 18031, -7682, -2144], ![-8576, 28293, -22760, 31774, -15364], ![-40772, 1773, -10233, -34283, 32846], ![55648, -16985, 24717, 26454, -33211]]]
  hmulB := by decide  
  f := ![![![1385, -34953, -15601, 3384, 13030]], ![![1815, -31001, -13948, 2946, 11642]], ![![1518, -30129, -13496, 2918, 11304]], ![![83, -15170, -6650, 1573, 5624]], ![![-122, -8819, -3819, 966, 3273]]]
  g := ![![![-246, 7987, -8863, -1072, 5022], ![4716, -18472, 18031, -7682, -2144], ![-15389, 28293, -22760, 31774, -15364], ![13840, 1773, -10233, -34283, 32846], ![-9343, -16985, 24717, 26454, -33211]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![1385, -34953, -15601, 3384, 13030]] ![![-13559, 7987, -8863, -1072, 5022]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![175, -609, 487, -692, 338]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![175, -609, 487, -692, 338]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![45, 18, 31, 41, 1]] where
  M :=![![![175, -609, 487, -692, 338], ![1352, 308, 67, 1650, -1384], ![-5536, 1685, -2460, -2634, 3300], ![5924, -3819, 4109, 15, -1942], ![-4560, 3899, -3885, 1342, 707]]]
  hmulB := by decide  
  f := ![![![151, 115, 21, -28, -22]], ![![-88, 122, 71, -2, -56]], ![![-224, -75, 10, 30, -4]], ![![36, -155, -77, 7, 58]], ![![-1, -14, -7, -1, 3]]]
  g := ![![![-155, -69, -103, -150, 338], ![656, 260, 443, 602, -1384], ![-1588, -595, -1080, -1422, 3300], ![962, 321, 663, 821, -1942], ![-375, -91, -266, -285, 707]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [43, 37, 14, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 2, 12, 25], [46, 61, 20, 36], [11, 33, 65, 36], [0, 1]]
 g := ![![[15, 82, 8, 4], [5, 71, 94], [27, 84, 79], [15, 17, 47], [22, 91, 1], []], ![[63, 35, 44, 46, 70, 16], [82, 51, 70], [43], [56, 12, 73], [74, 14, 70], [69, 96, 22, 6, 45, 8]], ![[73, 66, 80, 90, 14, 65], [3, 1, 47], [36, 57, 4], [24, 76, 50], [83, 96, 79], [3, 91, 76, 26, 69, 96]], ![[91, 90, 83, 66, 87, 95], [8, 55, 25], [68, 13, 73], [45, 45, 3], [69, 17, 88], [84, 24, 32, 44, 41, 96]]]
 h' := ![![[34, 2, 12, 25], [3, 18, 89, 95], [11, 51, 29, 26], [28, 59, 63, 46], [24, 26, 65, 12], [0, 0, 0, 1], [0, 1]], ![[46, 61, 20, 36], [95, 52, 22, 59], [56, 48, 31, 78], [81, 67, 72], [8, 75, 35, 48], [59, 61, 88, 19], [34, 2, 12, 25]], ![[11, 33, 65, 36], [96, 74, 94, 21], [15, 27, 65, 85], [60, 56, 93, 2], [92, 25, 86, 27], [13, 54, 80, 46], [46, 61, 20, 36]], ![[0, 1], [87, 50, 86, 19], [72, 68, 69, 5], [38, 12, 63, 49], [18, 68, 8, 10], [47, 79, 26, 31], [11, 33, 65, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [84, 45, 81], []]
 b := ![[], [], [67, 75, 35, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [43, 37, 14, 6, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13440277, 19580946, 13053851, 16196954, 12009707]
  a := ![1, 4, 2, -2, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5432954, -2026740, -3703578, -4909289, 12009707]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 115, 21, -28, -22]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![151, 115, 21, -28, -22]] 
 ![![97, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![66, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![151, 115, 21, -28, -22], ![-88, 122, 71, -2, -56], ![-224, -75, 10, 30, -4], ![36, -155, -77, 7, 58], ![160, -49, -55, -18, 35]]]
  hmulB := by decide  
  f := ![![![175, -609, 487, -692, 338]], ![![41, -91, 76, -90, 38]], ![![62, -397, 306, -498, 264]], ![![117, -234, 198, -221, 88]], ![![45, -280, 216, -350, 185]]]
  g := ![![![-10, 115, 21, -28, -22], ![-38, 122, 71, -2, -56], ![-5, -75, 10, 30, -4], ![44, -155, -77, 7, 58], ![34, -49, -55, -18, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![175, -609, 487, -692, 338]] ![![151, 115, 21, -28, -22]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 50, 39, 48, 31]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![35, 50, 39, 48, 31]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![60, 33, 99, 1, 0], ![19, 45, 63, 0, 1]] where
  M :=![![![35, 50, 39, 48, 31], ![124, 153, 112, 140, 96], ![384, 472, 345, 416, 280], ![498, 636, 460, 555, 368], ![674, 864, 630, 758, 507]]]
  hmulB := by decide  
  f := ![![![1, -2, 7, 2, -5]], ![![-20, 5, -12, 4, 4]], ![![16, -24, 13, -16, 8]], ![![10, -23, 13, -13, 6]], ![![1, -13, 4, -8, 6]]]
  g := ![![![-34, -29, -66, 48, 31], ![-100, -87, -196, 140, 96], ![-296, -256, -579, 416, 280], ![-394, -339, -769, 555, 368], ![-539, -465, -1053, 758, 507]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [29, 60, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [100, 42, 63], [59, 58, 38], [0, 1]]
 g := ![![[7, 51, 100], [98, 52], [75, 78, 43], [69, 85], [90, 31], [1]], ![[20, 69, 92, 8], [39, 92], [54, 84, 20, 38], [47, 84], [34, 43], [95, 8, 78, 72]], ![[84, 8, 72, 53], [68, 1], [49, 69, 80, 10], [7, 19], [85, 96], [15, 87, 34, 29]]]
 h' := ![![[100, 42, 63], [74, 40, 91], [47, 21, 70], [97, 34, 12], [49, 9, 61], [72, 41, 58], [0, 1]], ![[59, 58, 38], [13, 35, 21], [72, 75, 30], [68, 69, 10], [57, 60, 65], [72, 52, 89], [100, 42, 63]], ![[0, 1], [12, 26, 90], [60, 5, 1], [20, 99, 79], [83, 32, 76], [15, 8, 55], [59, 58, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 25], []]
 b := ![[], [88, 0, 99], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [29, 60, 43, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2251, 3638, -3580, 2614, -862]
  a := ![4, -1, -1, 1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1413, -434, -2060, 2614, -862]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, -20, 23, 0, -11]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![33, -20, 23, 0, -11]] 
 ![![101, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![64, 0, 1, 0, 0], ![75, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![33, -20, 23, 0, -11], ![-44, 45, -42, 24, 0], ![0, -62, 45, -84, 48], ![118, -18, 38, 81, -84], ![-146, 54, -72, -58, 81]]]
  hmulB := by decide  
  f := ![![![-2061, -2644, -1917, -2298, -1527]], ![![-489, -627, -455, -546, -363]], ![![-1488, -1906, -1383, -1660, -1104]], ![![-1773, -2270, -1647, -1977, -1315]], ![![-536, -682, -496, -598, -399]]]
  g := ![![![-9, -20, 23, 0, -11], ![-1, 45, -42, 24, 0], ![42, -62, 45, -84, 48], ![-71, -18, 38, 81, -84], ![68, 54, -72, -58, 81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 2, 0, -2, -2]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![1, 2, 0, -2, -2]] 
 ![![101, 0, 0, 0, 0], ![84, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![1, 2, 0, -2, -2], ![-8, -3, -2, -4, -4], ![-16, -18, -11, -12, -8], ![-12, -22, -16, -17, -10], ![-16, -26, -20, -24, -15]]]
  hmulB := by decide  
  f := ![![![93, -58, 52, 14, -34]], ![![76, -47, 42, 12, -28]], ![![14, -10, 9, 0, -4]], ![![73, -44, 40, 13, -28]], ![![49, -32, 28, 6, -17]]]
  g := ![![![1, 2, 0, -2, -2], ![8, -3, -2, -4, -4], ![30, -18, -11, -12, -8], ![39, -22, -16, -17, -10], ![51, -26, -20, -24, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![35, 50, 39, 48, 31]] ![![33, -20, 23, 0, -11]]
  ![![93, -58, 52, 14, -34]] where
 M := ![![![93, -58, 52, 14, -34]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![93, -58, 52, 14, -34]] ![![1, 2, 0, -2, -2]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0, 0, 0]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]] where
  M :=![![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![0, 0, 0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 5 2 6 [91, 11, 9, 49, 24, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 77, 85, 44, 16], [19, 61, 16, 18, 33], [7, 63, 30, 89, 63], [33, 4, 75, 55, 94], [0, 1]]
 g := ![![[36, 64, 15, 91, 46], [41, 30, 35, 9, 63], [68, 51, 88, 91, 14], [87, 65, 38, 41], [79, 1], []], ![[41, 91, 45, 83, 24, 29, 82, 100], [69, 24, 45, 82, 16, 19, 42, 66], [48, 100, 8, 18, 34, 46, 87, 13], [12, 63, 46, 9], [38, 102, 96, 4], [54, 46, 41, 20, 11, 35, 69, 79]], ![[73, 39, 33, 49, 28, 65, 38, 16], [60, 70, 69, 77, 29, 96, 47, 26], [70, 102, 86, 89, 5, 16, 93, 2], [43, 31, 31, 76], [75, 67, 93, 32], [39, 33, 54, 11, 2, 39, 27, 93]], ![[99, 53, 10, 73, 18, 1, 19, 34], [61, 37, 3, 59, 73, 37, 99, 17], [13, 100, 93, 49, 10, 83, 57, 8], [6, 11, 53, 9], [89, 20, 51, 29], [39, 21, 40, 73, 3, 67, 20, 66]], ![[83, 36, 15, 91, 102, 98, 69, 90], [32, 57, 85, 91, 48, 75, 45, 74], [102, 2, 43, 48, 82, 7, 23, 45], [1, 57, 14, 38], [32, 79, 83, 92], [85, 28, 61, 14, 40, 90, 64, 95]]]
 h' := ![![[20, 77, 85, 44, 16], [80, 76, 20, 87, 56], [95, 65, 86, 74, 75], [43, 85, 5, 16, 23], [21, 70, 102, 34, 12], [0, 0, 0, 1], [0, 1]], ![[19, 61, 16, 18, 33], [41, 94, 52, 87, 49], [25, 6, 59, 49, 74], [36, 68, 102, 39, 41], [60, 40, 78, 78, 3], [99, 70, 23, 48, 2], [20, 77, 85, 44, 16]], ![[7, 63, 30, 89, 63], [12, 95, 34, 39, 83], [44, 67, 6, 63, 54], [31, 30, 92, 49, 87], [66, 72, 64, 91, 30], [14, 7, 81, 28, 54], [19, 61, 16, 18, 33]], ![[33, 4, 75, 55, 94], [12, 18, 9, 2, 32], [70, 20, 2, 58, 10], [73, 20, 43, 25, 12], [1, 80, 93, 62, 3], [90, 20, 4, 19, 82], [7, 63, 30, 89, 63]], ![[0, 1], [51, 26, 91, 94, 89], [11, 48, 53, 65, 96], [67, 3, 67, 77, 43], [63, 47, 75, 44, 55], [83, 6, 98, 7, 68], [33, 4, 75, 55, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 1, 73, 42], [], [], []]
 b := ![[], [37, 42, 27, 33, 36], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 5
  hpos := by decide
  P := [91, 11, 9, 49, 24, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-449406692666895, -568576519204272, -414984855717160, -501876903109990, -335424036482766]
  a := ![7, -46, -24, -23, -71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4363171773465, -5520160380624, -4028979181720, -4872591292330, -3256544043522]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 11592740743 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀



lemma PB307I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB307I2 : PrimesBelowBoundCertificateInterval O 61 103 307 where
  m := 9
  g := ![2, 1, 2, 2, 3, 2, 2, 3, 1]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB307I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
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
    · exact ![300763, 4489]
    · exact ![1804229351]
    · exact ![389017, 5329]
    · exact ![38950081, 79]
    · exact ![6889, 6889, 83]
    · exact ![62742241, 89]
    · exact ![88529281, 97]
    · exact ![1030301, 101, 101]
    · exact ![11592740743]
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
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
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
  β := ![I79N1, I83N2, I89N1, I97N1, I101N1, I101N2]
  Il := ![[], [], [], [I79N1], [I83N2], [I89N1], [I97N1], [I101N1, I101N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
