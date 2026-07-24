
import IdealArithmetic.Examples.NF5_1_27000000_1.RI5_1_27000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-207, 32, 165, -13, -127]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-207, 32, 165, -13, -127]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![36, 49, 21, 1, 0], ![66, 19, 53, 0, 1]] where
  M :=![![![-207, 32, 165, -13, -127], ![1016, 16, -164, 597, -26], ![-404, -171, -525, -735, 610], ![-2948, 177, 1256, -1066, -722], ![2026, 242, 460, 1840, -843]]]
  hmulB := by decide  
  f := ![![![301, 26, -103, -51, -77]], ![![616, 326, 0, -1, -102]], ![![100, 309, 225, 103, 50]], ![![636, 350, 19, 6, -98]], ![![548, 369, 83, 34, -63]]]
  g := ![![![129, 46, 107, -13, -127], ![-280, -429, -169, 597, -26], ![-212, 362, -260, -735, 610], ![1240, 987, 924, -1066, -722], ![-128, -1103, 97, 1840, -843]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [33, 5, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 32, 42], [45, 34, 25], [0, 1]]
 g := ![![[23, 59, 29], [1, 64, 60], [11, 40], [30, 10], [23, 1], []], ![[55, 53, 31, 27], [35, 63, 48, 43], [16, 37], [39, 14], [42, 17], [45, 22]], ![[5, 14, 57, 59], [41, 3, 35, 17], [8, 62], [28, 9], [60, 19], [62, 22]]]
 h' := ![![[45, 32, 42], [34, 28, 37], [1, 18, 23], [30, 2, 24], [45, 53, 55], [0, 0, 1], [0, 1]], ![[45, 34, 25], [35, 43, 22], [32, 53, 64], [15, 63, 29], [37, 55, 9], [4, 53, 34], [45, 32, 42]], ![[0, 1], [48, 63, 8], [60, 63, 47], [18, 2, 14], [2, 26, 3], [46, 14, 32], [45, 34, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 49], []]
 b := ![[], [61, 18, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [33, 5, 44, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2339361, -247528, -1082605, 803105, 545465]
  a := ![0, 8, 5, -1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-933927, -745724, -699365, 803105, 545465]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![301, 26, -103, -51, -77]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![301, 26, -103, -51, -77]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![30, 47, 1, 0, 0], ![64, 41, 0, 1, 0], ![38, 1, 0, 0, 1]] where
  M :=![![![301, 26, -103, -51, -77], ![616, 326, 0, -1, -102], ![100, 309, 225, 103, 50], ![-508, 51, 256, 124, 154], ![-154, 436, 434, 204, 149]]]
  hmulB := by decide  
  f := ![![![-207, 32, 165, -13, -127]], ![![1016, 16, -164, 597, -26]], ![![614, 23, -49, 402, -66]], ![![380, 43, 76, 337, -148]], ![![-72, 22, 98, 29, -85]]]
  g := ![![![143, 105, -103, -51, -77], ![68, 7, 0, -1, -102], ![-226, -217, 225, 103, 50], ![-328, -257, 256, 124, 154], ![-476, -425, 434, 204, 149]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [28, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 66], [0, 1]]
 g := ![![[22, 25], [1, 23], [49], [25], [35], [1]], ![[32, 42], [37, 44], [49], [25], [35], [1]]]
 h' := ![![[54, 66], [39, 62], [60, 36], [62, 60], [5, 5], [39, 54], [0, 1]], ![[0, 1], [37, 5], [61, 31], [19, 7], [7, 62], [7, 13], [54, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [8, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [28, 13, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-39484, -8709, -2206, -26623, 4234]
  a := ![3, -5, -3, -1, -52]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![23428, 17646, -2206, -26623, 4234]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-207, 32, 165, -13, -127]] ![![301, 26, -103, -51, -77]]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 5 2 6 [9, 3, 45, 41, 9, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 50, 54, 45, 30], [69, 66, 0, 26, 40], [13, 57, 67, 40, 33], [70, 39, 21, 31, 39], [0, 1]]
 g := ![![[10, 39, 23, 18, 1], [6, 57, 12, 12, 12], [54, 33, 33, 11, 10], [35, 40, 62, 1], [], []], ![[68, 46, 0, 70, 34, 27, 70, 58], [27, 39, 15, 56, 68, 13, 2, 10], [37, 47, 58, 15, 39, 64, 41, 18], [66, 60, 50, 20], [60, 22, 15, 32], [7, 67, 67, 48]], ![[9, 43, 43, 70, 57, 63, 69, 20], [64, 19, 31, 16, 39, 55, 9, 15], [2, 39, 17, 2, 2, 18, 43, 37], [18, 15, 45, 58], [69, 40, 23, 54], [17, 19, 34, 38]], ![[70, 46, 53, 9, 18, 4, 1, 53], [12, 50, 14, 54, 66, 20, 23, 21], [16, 36, 68, 41, 63, 18, 28, 35], [1, 69, 57, 19], [64, 13, 37, 57], [20, 49, 10, 24]], ![[67, 25, 60, 17, 65, 12, 24, 42], [43, 37, 37, 49, 8, 39, 5, 55], [60, 29, 40, 43, 48, 24, 60, 47], [54, 55, 47, 38], [4, 64, 6, 20], [55, 0, 18, 30]]]
 h' := ![![[52, 50, 54, 45, 30], [17, 16, 58, 22, 70], [11, 5, 18, 67, 56], [40, 32, 19, 49, 9], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[69, 66, 0, 26, 40], [3, 54, 6, 23, 14], [12, 25, 38, 17, 33], [24, 8, 19, 30, 61], [11, 21, 67, 18, 34], [14, 32, 39, 39, 23], [52, 50, 54, 45, 30]], ![[13, 57, 67, 40, 33], [33, 52, 41, 64, 65], [21, 6, 2, 28, 13], [67, 41, 6, 41, 33], [67, 60, 61, 21, 49], [64, 11, 33, 30, 57], [69, 66, 0, 26, 40]], ![[70, 39, 21, 31, 39], [48, 60, 29, 13, 8], [15, 63, 66, 21, 34], [51, 0, 44, 3, 25], [42, 48, 27, 20, 27], [60, 58, 20, 11, 25], [13, 57, 67, 40, 33]], ![[0, 1], [65, 31, 8, 20, 56], [51, 43, 18, 9, 6], [30, 61, 54, 19, 14], [44, 13, 58, 12, 31], [3, 41, 49, 62, 37], [70, 39, 21, 31, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 15, 49, 61], [], [], []]
 b := ![[], [3, 47, 51, 34, 24], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 5
  hpos := by decide
  P := [9, 3, 45, 41, 9, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4597159972, -274526399, -16645666, -3306458427, 881771649]
  a := ![1, 3, 2, -1, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-64748732, -3866569, -234446, -46569837, 12419319]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0, 0, 0]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]] where
  M :=![![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![0, 0, 0, 73, 0], ![0, 0, 0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 5 2 6 [23, 20, 50, 20, 27, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 51, 1, 27, 13], [50, 7, 50, 6, 3], [7, 2, 36, 61, 33], [17, 12, 59, 52, 24], [0, 1]]
 g := ![![[52, 6, 61, 52, 69], [14, 5, 4, 65], [13, 64, 59, 27], [2, 35, 52, 46, 1], [], []], ![[40, 34, 13, 66, 37, 21, 49, 11], [48, 41, 14, 69], [45, 69, 51, 35], [21, 2, 58, 39, 43, 68, 54, 34], [29, 0, 63, 72], [54, 6, 8, 23]], ![[60, 62, 7, 49, 19, 26, 10, 41], [36, 36, 49, 9], [3, 9, 53, 3], [12, 54, 67, 19, 66, 46, 65, 16], [54, 64, 42, 49], [35, 51, 12, 9]], ![[59, 59, 43, 60, 25, 42, 6, 68], [21, 60, 48, 49], [1, 58, 30, 67], [2, 72, 63, 3, 61, 34, 5, 21], [65, 21, 10, 41], [64, 13, 27, 67]], ![[68, 69, 14, 52, 61, 25, 16, 2], [48, 5, 70, 67], [23, 66, 34, 8], [22, 12, 10, 10, 14, 7, 60, 65], [45, 19, 72, 54], [38, 70, 11, 65]]]
 h' := ![![[45, 51, 1, 27, 13], [34, 22, 41, 13, 54], [65, 15, 47, 47, 49], [27, 31, 48, 54, 10], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[50, 7, 50, 6, 3], [45, 71, 71, 63, 38], [28, 17, 2, 14, 54], [48, 20, 36, 70, 53], [25, 28, 35, 26, 17], [53, 14, 52, 25, 27], [45, 51, 1, 27, 13]], ![[7, 2, 36, 61, 33], [0, 34, 63, 50, 29], [68, 17, 1, 0, 3], [65, 37, 48, 42, 52], [36, 62, 45, 22, 45], [16, 68, 32, 12, 66], [50, 7, 50, 6, 3]], ![[17, 12, 59, 52, 24], [26, 44, 56, 44, 65], [12, 16, 28, 51, 7], [53, 57, 2, 2, 40], [20, 24, 5, 66, 40], [37, 55, 4, 53, 25], [7, 2, 36, 61, 33]], ![[0, 1], [26, 48, 61, 49, 33], [20, 8, 68, 34, 33], [44, 1, 12, 51, 64], [61, 32, 61, 32, 43], [72, 9, 57, 56, 28], [17, 12, 59, 52, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 28, 2, 71], [], [], []]
 b := ![[], [32, 35, 35, 8, 17], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 5
  hpos := by decide
  P := [23, 20, 50, 20, 27, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3773427328433, 81380696307, -491019656253, 2300734252756, -211508162351]
  a := ![1, -11, -7, -1, 47]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![51690785321, 1114804059, -6726296661, 31516907572, -2897372087]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 2073071593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10015, 6062, -2671, 1743, -2089]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-10015, 6062, -2671, 1743, -2089]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![6, 71, 58, 1, 0], ![50, 13, 53, 0, 1]] where
  M :=![![![-10015, 6062, -2671, 1743, -2089], ![16712, -10110, 4460, -2907, 3486], ![-22300, 13493, -5947, 3881, -4650], ![10244, -6203, 2732, -1784, 2138], ![-9018, 5452, -2402, 1568, -1879]]]
  hmulB := by decide  
  f := ![![![1, 0, 1, -3, -7]], ![![56, 8, -8, 19, -6]], ![![-4, 5, -13, -21, 22]], ![![46, 11, -16, 1, 10]], ![![8, 5, -9, -12, 9]]]
  g := ![![![1063, -1146, 88, 1743, -2089], ![-1774, 1911, -148, -2907, 3486], ![2366, -2552, 195, 3881, -4650], ![-1088, 1173, -90, -1784, 2138], ![956, -1031, 79, 1568, -1879]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [14, 59, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 15, 54], [41, 63, 25], [0, 1]]
 g := ![![[39, 3, 16], [18, 1, 8], [71, 76, 11], [26, 0, 62], [48, 1], []], ![[37, 64, 5, 48], [49, 75, 46, 30], [28, 55, 25, 33], [74, 45, 33, 74], [60, 19], [20, 72]], ![[45, 3, 19, 51], [3, 30, 14, 16], [44, 64, 76, 49], [65, 52, 73, 11], [67, 67], [49, 72]]]
 h' := ![![[7, 15, 54], [64, 13, 4], [33, 53, 18], [31, 66, 66], [39, 77, 33], [0, 0, 1], [0, 1]], ![[41, 63, 25], [21, 25, 6], [38, 30, 46], [20, 2, 59], [65, 29, 75], [6, 76, 63], [7, 15, 54]], ![[0, 1], [74, 41, 69], [50, 75, 15], [72, 11, 33], [7, 52, 50], [47, 3, 15], [41, 63, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 57], []]
 b := ![[], [30, 1, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [14, 59, 31, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4524777, -409431, -2167491, 1447282, 1217770]
  a := ![-1, 13, 9, 2, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-823385, -1506297, -1906983, 1447282, 1217770]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 0, 1, -3, -7]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![1, 0, 1, -3, -7]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![54, 22, 1, 0, 0], ![76, 68, 0, 1, 0], ![54, 53, 0, 0, 1]] where
  M :=![![![1, 0, 1, -3, -7], ![56, 8, -8, 19, -6], ![-4, 5, -13, -21, 22], ![-116, 11, 52, -34, -18], ![66, 26, 32, 68, -27]]]
  hmulB := by decide  
  f := ![![![-10015, 6062, -2671, 1743, -2089]], ![![16712, -10110, 4460, -2907, 3486]], ![![-2474, 1499, -659, 431, -516]], ![![4880, -2949, 1304, -848, 1018]], ![![4252, -2570, 1136, -739, 887]]]
  g := ![![![7, 7, 1, -3, -7], ![-8, -10, -8, 19, -6], ![14, 7, -13, -21, 22], ![8, 27, 52, -34, -18], ![-68, -49, 32, 68, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [17, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 78], [0, 1]]
 g := ![![[29, 31], [77, 31], [29, 42], [2, 73], [45], [1]], ![[72, 48], [41, 48], [21, 37], [37, 6], [45], [1]]]
 h' := ![![[60, 78], [34, 30], [60, 49], [45, 68], [77, 28], [62, 60], [0, 1]], ![[0, 1], [17, 49], [77, 30], [17, 11], [19, 51], [28, 19], [60, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [18, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [17, 19, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2063, -118, 890, -1006, -336]
  a := ![0, -10, -6, -10, 8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![563, 842, 890, -1006, -336]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-10015, 6062, -2671, 1743, -2089]] ![![1, 0, 1, -3, -7]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0, 0, 0]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]] where
  M :=![![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![0, 0, 0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 5 2 6 [68, 71, 35, 26, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 5, 16, 8, 31], [80, 67, 82, 71, 65], [12, 21, 64, 17, 26], [20, 72, 4, 70, 44], [0, 1]]
 g := ![![[9, 49, 79, 19, 26], [32, 63, 1, 5, 38], [20, 48, 71, 10], [5, 22, 13, 4], [1], []], ![[21, 16, 67, 78, 35, 68], [59, 49, 55, 9, 73, 76, 68, 78], [59, 69, 17, 38], [71, 12, 72, 51], [59, 71, 24, 15, 20, 36, 18, 27], [15, 4, 68, 48]], ![[6, 48, 37, 19, 53, 38, 21, 28], [21, 74, 28, 73, 56, 54, 73, 48], [16, 58, 75, 21], [57, 51, 15, 16], [52, 5, 43, 42, 66, 76, 23, 65], [42, 73, 33, 75]], ![[57, 7, 62, 42, 2, 41, 75, 70], [50, 20, 60, 82, 13, 76, 18, 25], [41, 63, 53, 65], [31, 9, 20, 26], [66, 56, 68, 73, 39, 24, 2, 11], [60, 8, 30, 12]], ![[67, 45, 19, 39, 32, 38, 34, 31], [76, 32, 2, 1, 34, 66, 38, 64], [31, 60, 59, 49], [79, 81, 80, 3], [68, 56, 77, 72, 82, 3, 81, 12], [50, 57, 47, 27]]]
 h' := ![![[52, 5, 16, 8, 31], [65, 17, 64, 24, 62], [79, 21, 5, 15, 11], [51, 3, 42, 20, 50], [15, 12, 48, 57, 81], [0, 0, 1], [0, 1]], ![[80, 67, 82, 71, 65], [19, 46, 6, 28], [58, 23, 79, 47, 17], [13, 36, 58, 8, 11], [44, 0, 48, 46, 47], [24, 13, 74, 6, 45], [52, 5, 16, 8, 31]], ![[12, 21, 64, 17, 26], [62, 40, 81, 50, 48], [19, 25, 13, 75, 78], [32, 24, 13, 34, 42], [67, 16, 57, 37, 4], [58, 35, 80, 53, 82], [80, 67, 82, 71, 65]], ![[20, 72, 4, 70, 44], [52, 6, 49, 73, 37], [29, 66, 73, 70, 63], [59, 13, 39, 75, 56], [3, 56, 67, 61, 21], [48, 16, 8, 53, 50], [12, 21, 64, 17, 26]], ![[0, 1], [57, 57, 49, 74, 19], [45, 31, 79, 42, 80], [24, 7, 14, 29, 7], [82, 82, 29, 48, 13], [71, 19, 3, 54, 72], [20, 72, 4, 70, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 29, 41], [], [], []]
 b := ![[], [76, 40, 51, 79], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 5
  hpos := by decide
  P := [68, 71, 35, 26, 2, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-169634939267, -1847249826, 30156160090, -96392116732, 888991420]
  a := ![13, 10, 7, 1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2043794449, -22256022, 363327230, -1161350804, 10710740]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 3939040643 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63, -26, -106, -44, 94]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![63, -26, -106, -44, 94]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![81, 25, 40, 1, 0], ![49, 19, 46, 0, 1]] where
  M :=![![![63, -26, -106, -44, 94], ![-752, 19, 224, -356, -88], ![728, 92, 175, 668, -312], ![1624, -180, -1000, 331, 712], ![-2060, -88, 100, -1400, 287]]]
  hmulB := by decide  
  f := ![![![-1985, 1210, -526, 348, -414]], ![![3312, -1997, 896, -572, 696]], ![![-4440, 2676, -1177, 772, -920]], ![![-2849, 1729, -750, 499, -590]], ![![-2701, 1635, -712, 472, -559]]]
  g := ![![![-11, -8, -30, -44, 94], ![364, 119, 208, -356, -88], ![-428, -120, -137, 668, -312], ![-675, -247, -528, 331, 712], ![1093, 331, 482, -1400, 287]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [8, 4, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 68, 14], [56, 20, 75], [0, 1]]
 g := ![![[46, 38, 25], [18, 21], [24, 36], [86, 19, 49], [63, 44, 1], []], ![[28, 25, 54, 75], [17, 8], [23, 81], [80, 71, 75, 23], [11, 6, 84, 82], [26, 18]], ![[30, 33, 76, 63], [19, 22], [55, 9], [10, 75, 75, 82], [49, 1, 41, 56], [54, 18]]]
 h' := ![![[77, 68, 14], [17, 35, 84], [28, 51, 33], [24, 48, 6], [30, 19, 7], [0, 0, 1], [0, 1]], ![[56, 20, 75], [6, 32, 34], [63, 79, 39], [43, 83, 80], [66, 58, 50], [25, 78, 20], [77, 68, 14]], ![[0, 1], [27, 22, 60], [1, 48, 17], [68, 47, 3], [86, 12, 32], [34, 11, 68], [56, 20, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 46], []]
 b := ![[], [51, 48, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [8, 4, 45, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-164516, 3991, 51745, -79982, -22851]
  a := ![-1, -5, -3, -1, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![83525, 27390, 48339, -79982, -22851]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1985, 1210, -526, 348, -414]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-1985, 1210, -526, 348, -414]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![88, 50, 1, 0, 0], ![50, 17, 0, 1, 0], ![41, 42, 0, 0, 1]] where
  M :=![![![-1985, 1210, -526, 348, -414], ![3312, -1997, 896, -572, 696], ![-4440, 2676, -1177, 772, -920], ![2024, -1244, 536, -357, 424], ![-1812, 1072, -476, 312, -369]]]
  hmulB := by decide  
  f := ![![![63, -26, -106, -44, 94]], ![![-752, 19, 224, -356, -88]], ![![-352, -14, 23, -236, 40]], ![![-90, -13, -28, -89, 44]], ![![-349, -4, 58, -204, 5]]]
  g := ![![![493, 438, -526, 348, -414], ![-848, -745, 896, -572, 696], ![1104, 978, -1177, 772, -920], ![-502, -447, 536, -357, 424], ![445, 394, -476, 312, -369]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [7, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 88], [0, 1]]
 g := ![![[11, 5], [79], [87], [37, 8], [47, 55], [1]], ![[71, 84], [79], [87], [44, 81], [84, 34], [1]]]
 h' := ![![[12, 88], [13, 70], [78, 48], [8, 49], [27, 50], [82, 12], [0, 1]], ![[0, 1], [52, 19], [31, 41], [62, 40], [4, 39], [48, 77], [12, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [40, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [7, 77, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13809, -3524, -1678, -12326, 5144]
  a := ![3, -14, -7, -4, 34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6059, 830, -1678, -12326, 5144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![63, -26, -106, -44, 94]] ![![-1985, 1210, -526, 348, -414]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0, 0, 0]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]] where
  M :=![![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![0, 0, 0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 5 2 6 [68, 4, 64, 27, 89, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 36, 64, 60, 77], [63, 78, 41, 62, 15], [35, 84, 17, 70, 60], [49, 92, 72, 2, 42], [0, 1]]
 g := ![![[32, 9, 54, 80, 2], [21, 10, 43, 48], [72, 74, 54, 44], [75, 90, 29, 11], [8, 1], []], ![[74, 0, 91, 54, 65, 31, 11, 42], [13, 14, 84, 73], [29, 8, 44, 93], [73, 13, 80, 6], [48, 59, 20, 88], [81, 48, 29, 72, 55, 53, 46, 51]], ![[35, 78, 89, 40, 0, 87, 68, 57], [17, 40, 41, 2], [49, 13, 51, 43], [79, 78, 87, 70], [86, 85, 42, 65], [8, 8, 56, 80, 29, 51, 77, 77]], ![[77, 35, 56, 73, 37, 12, 9, 37], [9, 94, 90, 27], [93, 89, 50, 96], [8, 28, 62, 32], [47, 47, 30, 65], [16, 81, 12, 9, 67, 81, 24, 78]], ![[60, 94, 9, 18, 3, 69, 31, 46], [65, 26, 68, 43], [23, 19, 13, 94], [31, 80, 81, 8], [81, 32, 21, 88], [68, 51, 67, 36, 51, 54, 45, 77]]]
 h' := ![![[55, 36, 64, 60, 77], [0, 50, 32, 30, 14], [78, 96, 16, 37, 57], [30, 45, 27, 36, 74], [38, 94, 66, 11, 37], [0, 0, 0, 1], [0, 1]], ![[63, 78, 41, 62, 15], [50, 20, 82, 19, 30], [62, 2, 21, 82, 49], [71, 88, 64, 67, 44], [66, 86, 92, 47, 54], [41, 5, 40, 83, 66], [55, 36, 64, 60, 77]], ![[35, 84, 17, 70, 60], [43, 82, 31, 46, 81], [36, 21, 80, 58, 83], [78, 91, 33, 66, 72], [42, 83, 25, 82, 19], [19, 74, 37, 35, 68], [63, 78, 41, 62, 15]], ![[49, 92, 72, 2, 42], [32, 42, 92, 22, 22], [16, 87, 51, 27, 30], [36, 81, 4, 56, 75], [17, 85, 7, 0, 56], [77, 3, 68, 25, 29], [35, 84, 17, 70, 60]], ![[0, 1], [77, 0, 54, 77, 47], [61, 85, 26, 87, 72], [48, 83, 66, 66, 26], [33, 40, 4, 54, 28], [20, 15, 49, 50, 31], [49, 92, 72, 2, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 85, 95, 9], [], [], []]
 b := ![[], [84, 35, 63, 51, 15], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 5
  hpos := by decide
  P := [68, 4, 64, 27, 89, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24964324199, 2302187233, 3247197220, 20684741914, -7979240176]
  a := ![1, -7, -5, -1, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![257364167, 23733889, 33476260, 213244762, -82260208]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 8587340257 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4969, -4420, -1555, -709, 367]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-4969, -4420, -1555, -709, 367]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![18, 65, 1, 0, 0], ![42, 59, 0, 1, 0], ![88, 46, 0, 0, 1]] where
  M :=![![![-4969, -4420, -1555, -709, 367], ![-2936, -9526, -6688, -3135, -1418], ![7140, -1677, -4465, -2135, -2426], ![11172, 7397, 1376, 596, -1426], ![15494, 1872, -5090, -2468, -3961]]]
  hmulB := by decide  
  f := ![![![157, 182, 371, 531, -469]], ![![3752, -352, -1636, 1149, 1062]], ![![2382, -195, -983, 796, 606]], ![![2214, -119, -750, 903, 382]], ![![1974, -2, -452, 1054, 81]]]
  g := ![![![203, 1204, -1555, -709, 367], ![3702, 6687, -6688, -3135, -1418], ![3868, 5209, -4465, -2135, -2426], ![860, -511, 1376, 596, -1426], ![5538, 6540, -5090, -2468, -3961]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [95, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 100], [0, 1]]
 g := ![![[45, 84], [88], [31, 68], [81], [54], [68, 1]], ![[0, 17], [88], [9, 33], [81], [54], [35, 100]]]
 h' := ![![[68, 100], [77, 36], [85, 47], [37, 13], [37, 9], [4, 85], [0, 1]], ![[0, 1], [0, 65], [49, 54], [12, 88], [43, 92], [27, 16], [68, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [34, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [95, 33, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11, 57, 54, -133, -146]
  a := ![4, 2, 1, 1, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![173, 110, 54, -133, -146]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![843, -508, 226, -146, 176]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![843, -508, 226, -146, 176]] 
 ![![101, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![95, 0, 1, 0, 0], ![58, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![843, -508, 226, -146, 176], ![-1408, 853, -372, 246, -292], ![1872, -1136, 501, -326, 392], ![-864, 518, -232, 149, -180], ![752, -462, 202, -132, 159]]]
  hmulB := by decide  
  f := ![![![-145, 40, 186, 50, -168]], ![![9, 1, 2, 8, -4]], ![![-147, 36, 171, 36, -152]], ![![-114, 26, 124, 21, -108]], ![![-24, 18, 74, 44, -73]]]
  g := ![![![-175, -508, 226, -146, 176], ![285, 853, -372, 246, -292], ![-387, -1136, 501, -326, 392], ![180, 518, -232, 149, -180], ![-156, -462, 202, -132, 159]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4021, 912, -965, -473, -927]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![4021, 912, -965, -473, -927]] 
 ![![101, 0, 0, 0, 0], ![85, 1, 0, 0, 0], ![82, 0, 1, 0, 0], ![58, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![4021, 912, -965, -473, -927], ![7416, 4914, 916, 397, -946], ![76, 3769, 3113, 1465, 870], ![-7188, -443, 2716, 1312, 1938], ![-3854, 4692, 5570, 2640, 2205]]]
  hmulB := by decide  
  f := ![![![10383, -870, -5219, 3047, 3373]], ![![8471, -750, -4403, 2364, 2899]], ![![8322, -645, -3989, 2603, 2508]], ![![7018, -519, -3290, 2264, 2036]], ![![5308, -574, -3134, 1166, 2197]]]
  g := ![![![823, 912, -965, -473, -927], ![-4528, 4914, 916, 397, -946], ![-7005, 3769, 3113, 1465, 870], ![-3693, -443, 2716, 1312, 1938], ![-11204, 4692, 5570, 2640, 2205]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2

def I101N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 2, 1, 17, -5]] i)))

def SI101N3: IdealEqSpanCertificate' Table ![![23, 2, 1, 17, -5]] 
 ![![101, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![97, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![23, 2, 1, 17, -5], ![40, -8, -40, -5, 34], ![-156, 5, 51, -69, -22], ![68, 23, 72, 110, -86], ![262, -20, -126, 84, 79]]]
  hmulB := by decide  
  f := ![![![-20067, 12156, -5377, 3489, -4201]], ![![-16754, 10150, -4490, 2913, -3508]], ![![-19715, 11943, -5282, 3428, -4127]], ![![-5360, 3247, -1436, 932, -1122]], ![![-775, 470, -207, 135, -162]]]
  g := ![![![-7, 2, 1, 17, -5], ![46, -8, -40, -5, 34], ![-35, 5, 51, -69, -22], ![-116, 23, 72, 110, -86], ![115, -20, -126, 84, 79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N3 : Nat.card (O ⧸ I101N3) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N3)

lemma isPrimeI101N3 : Ideal.IsPrime I101N3 := prime_ideal_of_norm_prime hp101.out _ NI101N3
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-4969, -4420, -1555, -709, 367]] ![![843, -508, 226, -146, 176]]
  ![![12093, -16344, -19187, -9001, -7491]] where
 M := ![![![12093, -16344, -19187, -9001, -7491]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![12093, -16344, -19187, -9001, -7491]] ![![4021, 912, -965, -473, -927]]
  ![![19530139, -172761732, -152541566, -71903064, -46403070]] where
 M := ![![![19530139, -172761732, -152541566, -71903064, -46403070]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N2 : IdealMulLeCertificate' Table 
  ![![19530139, -172761732, -152541566, -71903064, -46403070]] ![![23, 2, 1, 17, -5]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![288195521, -67262768, -179854235, -86005843, -97814157]]]
 hmul := by decide  
 g := ![![![![2853421, -665968, -1780735, -851543, -968457]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2, I101N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
    exact isPrimeI101N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1 ⊙ MulI101N2)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55668341, -33684944, 14848602, -9686476, 11610664]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![55668341, -33684944, 14848602, -9686476, 11610664]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![23, 87, 56, 1, 0], ![11, 43, 68, 0, 1]] where
  M :=![![![55668341, -33684944, 14848602, -9686476, 11610664], ![-92885312, 56204951, -24775608, 16162352, -19372952], ![123934464, -74992812, 33057451, -21565008, 25848828], ![-56952656, 34462084, -15191172, 9909951, -11878532], ![50086952, -30307642, 13359858, -8715296, 10446561]]]
  hmulB := by decide  
  f := ![![![-213, -40, -42, -164, 80]], ![![-640, 33, 408, -80, -328]], ![![1632, -36, -419, 816, 84]], ![![299, -3, 98, 331, -204]], ![![759, -13, -100, 476, -79]]]
  g := ![![![1463495, 3007572, -2254698, -9686476, 11610664], ![-2441912, -5018279, 3762072, 16162352, -19372952], ![3258180, 6695760, -5019635, -21565008, 25848828], ![-1497259, -3076959, 2306716, 9909951, -11878532], ![1316763, 2706029, -2028638, -8715296, 10446561]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [44, 56, 99, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 87, 93], [61, 15, 10], [0, 1]]
 g := ![![[13, 27, 1], [83, 70, 36], [12, 78, 9], [45, 98], [28, 16], [1]], ![[59, 55, 26, 13], [63, 78, 60, 17], [49, 18, 49, 33], [34, 33], [51, 4], [6, 37, 58, 30]], ![[37, 53, 29, 57], [36, 15, 12, 3], [3, 72, 14, 102], [77, 52], [92, 36], [70, 63, 54, 73]]]
 h' := ![![[46, 87, 93], [56, 63, 1], [90, 11, 6], [60, 96, 100], [86, 81, 43], [59, 47, 4], [0, 1]], ![[61, 15, 10], [67, 77, 3], [63, 51, 83], [56, 50, 25], [78, 39, 41], [46, 86, 2], [46, 87, 93]], ![[0, 1], [98, 66, 99], [100, 41, 14], [15, 60, 81], [101, 86, 19], [82, 73, 97], [61, 15, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101, 30], []]
 b := ![[], [40, 96, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [44, 56, 99, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![396102774, -39886596, -185592760, 136154778, 98705854]
  a := ![7, 47, 23, 0, -140]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-37099238, -156599068, -140992800, 136154778, 98705854]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-213, -40, -42, -164, 80]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-213, -40, -42, -164, 80]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![72, 48, 1, 0, 0], ![46, 74, 0, 1, 0], ![20, 94, 0, 0, 1]] where
  M :=![![![-213, -40, -42, -164, 80], ![-640, 33, 408, -80, -328], ![1632, -36, -419, 816, 84], ![-16, -244, -972, -871, 980], ![-2936, 130, 1110, -1216, -625]]]
  hmulB := by decide  
  f := ![![![55668341, -33684944, 14848602, -9686476, 11610664]], ![![-92885312, 56204951, -24775608, 16162352, -19372952]], ![![-3169320, 1917756, -845363, 551472, -661020]], ![![-42424486, 25671078, -11316024, 7382001, -8848412]], ![![-73473452, 44458824, -19597818, 12784624, -15324249]]]
  g := ![![![85, 64, -42, -164, 80], ![-192, 167, 408, -80, -328], ![-72, -468, -419, 816, 84], ![878, 182, -972, -871, 980], ![-140, 928, 1110, -1216, -625]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [81, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 102], [0, 1]]
 g := ![![[63, 14], [96, 97], [1, 83], [8], [92], [47, 1]], ![[0, 89], [20, 6], [91, 20], [8], [92], [94, 102]]]
 h' := ![![[47, 102], [52, 23], [22, 32], [61, 17], [83, 27], [4, 68], [0, 1]], ![[0, 1], [0, 80], [84, 71], [36, 86], [13, 76], [7, 35], [47, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [58, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal' SI103N1 103 where
  n := 2
  hpos := by decide
  P := [81, 56, 1]
  hirr := P103P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17012, -3763, -4925, -18112, 3020]
  a := ![1, 15, 8, -1, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10780, 12515, -4925, -18112, 3020]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N1 B_one_repr
lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![55668341, -33684944, 14848602, -9686476, 11610664]] ![![-213, -40, -42, -164, 80]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)


lemma PB324I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB324I2 : PrimesBelowBoundCertificateInterval O 61 103 324 where
  m := 9
  g := ![2, 1, 1, 2, 1, 2, 1, 4, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB324I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0]
    · exact ![I79N0, I79N1]
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N2, I101N3]
    · exact ![I103N0, I103N1]
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
    · exact ![2073071593]
    · exact ![493039, 6241]
    · exact ![3939040643]
    · exact ![704969, 7921]
    · exact ![8587340257]
    · exact ![10201, 101, 101, 101]
    · exact ![1092727, 10609]
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
      exact NI101N3
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I101N1, I101N2, I101N3]
  Il := ![[], [], [], [], [], [], [], [I101N1, I101N2, I101N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
