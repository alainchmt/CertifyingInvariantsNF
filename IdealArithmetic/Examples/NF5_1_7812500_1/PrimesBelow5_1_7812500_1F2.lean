
import IdealArithmetic.Examples.NF5_1_7812500_1.RI5_1_7812500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, 65, 71, 30, -84]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-25, 65, 71, 30, -84]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![33, 8, 51, 14, 1]] where
  M :=![![![-25, 65, 71, 30, -84], ![-60, 89, 23, 5, 120], ![-10, -175, -186, -122, 690], ![244, -822, -701, -266, 1254], ![94, -365, -342, -153, 683]]]
  hmulB := by decide  
  f := ![![![-905, -42, 269, 181, -708]], ![![-362, -16, 107, 72, -282]], ![![-144, -8, 44, 29, -114]], ![![-58, -1, 17, 13, -48]], ![![-613, -29, 183, 123, -481]]]
  g := ![![![41, 11, 65, 18, -84], ![-60, -13, -91, -25, 120], ![-340, -85, -528, -146, 690], ![-614, -162, -965, -266, 1254], ![-335, -87, -525, -145, 683]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 4 2 6 [3, 27, 53, 9, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 44, 27, 53], [60, 3, 46, 59], [38, 19, 61, 22], [0, 1]]
 g := ![![[58, 56, 43, 19], [2, 33, 57, 37], [63, 56, 4], [59, 24, 14], [1], []], ![[47, 45, 65, 5, 17, 11], [65, 23, 58, 62, 54, 32], [52, 9, 56], [50, 66, 36], [8, 38, 4], [64, 26, 62]], ![[6, 10, 46, 55, 55, 21], [57, 5, 28, 15, 19, 29], [1], [66, 2, 4], [11, 35, 29], [32, 28, 64]], ![[6, 62, 4, 11, 15, 36], [31, 39, 38, 49, 51, 29], [55, 61, 55], [66, 13, 1], [64, 3, 47], [50, 3, 15]]]
 h' := ![![[27, 44, 27, 53], [61, 18, 49, 35], [29, 36, 21, 38], [33, 38, 44, 65], [64, 40, 14, 58], [0, 0, 1], [0, 1]], ![[60, 3, 46, 59], [0, 38, 19, 2], [38, 63, 54, 6], [44, 52, 31, 18], [44, 6, 66, 6], [1, 34, 52, 2], [27, 44, 27, 53]], ![[38, 19, 61, 22], [27, 7, 4, 49], [12, 20, 20, 51], [22, 30, 1], [32, 64, 43, 2], [20, 15, 4, 37], [60, 3, 46, 59]], ![[0, 1], [2, 4, 62, 48], [6, 15, 39, 39], [29, 14, 58, 51], [48, 24, 11, 1], [21, 18, 10, 28], [38, 19, 61, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [34, 29, 20], []]
 b := ![[], [], [24, 26, 7, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 4
  hpos := by decide
  P := [3, 27, 53, 9, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2018605, -1711242, 3071806, 2441606, -11643318]
  a := ![5, -3, 16, 11, -45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5764897, 1364706, 8908672, 2469374, -11643318]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 20151121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-905, -42, 269, 181, -708]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-905, -42, 269, 181, -708]] 
 ![![67, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![58, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![-905, -42, 269, 181, -708], ![-362, -16, 107, 72, -282], ![-144, -8, 44, 29, -114], ![-58, -1, 17, 13, -48], ![-154, -7, 46, 31, -121]]]
  hmulB := by decide  
  f := ![![![-25, 65, 71, 30, -84]], ![![-5, 12, 12, 5, -12]], ![![-5, 10, 11, 4, -6]], ![![-18, 44, 51, 22, -54]], ![![-18, 45, 50, 21, -55]]]
  g := ![![![334, -42, 269, 181, -708], ![133, -16, 107, 72, -282], ![54, -8, 44, 29, -114], ![22, -1, 17, 13, -48], ![57, -7, 46, 31, -121]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-25, 65, 71, 30, -84]] ![![-905, -42, 269, 181, -708]]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 5 2 6 [14, 31, 12, 45, 47, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 39, 8, 24, 39], [47, 70, 8, 13, 12], [29, 38, 12, 24, 62], [48, 65, 43, 10, 29], [0, 1]]
 g := ![![[68, 67, 39, 9, 20], [44, 53, 14, 51, 29], [0, 64, 42, 26, 8], [8, 34, 24, 1], [], []], ![[54, 54, 0, 16, 38, 56, 28, 11], [55, 46, 64, 38, 48, 18, 29, 14], [41, 51, 1, 37, 5, 35, 32, 11], [64, 41, 52, 3], [64, 24, 68, 25], [51, 4, 36, 30]], ![[18, 56, 44, 1, 59, 59, 36, 4], [63, 14, 18, 46, 32, 57, 62, 49], [70, 44, 44, 47, 32, 28, 50, 5], [5, 63, 2, 64], [32, 7, 49, 4], [18, 36, 5, 2]], ![[49, 22, 22, 7, 41, 19, 61, 53], [33, 29, 5, 25, 70, 61, 13, 66], [6, 21, 10, 19, 47, 65, 47, 46], [55, 70, 67, 8], [23, 52, 23, 54], [30, 59, 21, 10]], ![[39, 25, 52, 23, 55, 44, 7, 10], [57, 48, 14, 44, 40, 65, 14, 9], [60, 64, 40, 52, 5, 13, 12, 36], [19, 22, 52, 9], [58, 11, 43, 49], [40, 23, 32, 60]]]
 h' := ![![[42, 39, 8, 24, 39], [23, 24, 47, 15, 34], [0, 4, 67, 50, 61], [30, 57, 5, 36, 47], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[47, 70, 8, 13, 12], [22, 48, 44, 14, 8], [61, 70, 46, 44, 69], [57, 35, 6, 62, 63], [39, 56, 9, 25, 28], [56, 6, 30, 39, 66], [42, 39, 8, 24, 39]], ![[29, 38, 12, 24, 62], [3, 51, 41, 63, 33], [55, 35, 9, 35, 9], [44, 0, 58, 52, 39], [16, 8, 17, 16, 63], [40, 51, 61, 65, 69], [47, 70, 8, 13, 12]], ![[48, 65, 43, 10, 29], [18, 33, 56, 30, 59], [44, 28, 21, 45, 53], [38, 31, 69, 58, 22], [58, 43, 0, 10, 47], [66, 22, 12, 23, 14], [29, 38, 12, 24, 62]], ![[0, 1], [31, 57, 25, 20, 8], [70, 5, 70, 39, 21], [67, 19, 4, 5, 42], [7, 35, 45, 20, 3], [40, 63, 38, 15, 64], [48, 65, 43, 10, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 6, 3, 43], [], [], []]
 b := ![[], [39, 46, 48, 16, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 5
  hpos := by decide
  P := [14, 31, 12, 45, 47, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![60123526089310, -129702745193183, -68184924956688, -25486354065791, 24791718749862]
  a := ![59, -60, 177, 116, -528]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![846810226610, -1826799228073, -960351055728, -358962733321, 349179137322]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -36, 11, -43, 84]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![11, -36, 11, -43, 84]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![30, 41, 49, 1, 0], ![32, 11, 20, 0, 1]] where
  M :=![![![11, -36, 11, -43, 84], ![86, -116, 97, 142, -354], ![-284, 582, -402, -259, 786], ![518, -1329, 823, 107, -732], ![18, -65, 34, -27, 35]]]
  hmulB := by decide  
  f := ![![![-7, 21, 11, 2, 24]], ![![-4, -29, -41, -23, 156]], ![![46, -183, -180, -82, 366]], ![![28, -136, -144, -69, 348]], ![![10, -48, -53, -26, 137]]]
  g := ![![![-19, 11, 6, -43, 84], ![98, -28, 3, 142, -354], ![-242, 35, -47, -259, 786], ![284, 32, 140, 107, -732], ![-4, 9, 9, -27, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [35, 38, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 2, 60], [31, 70, 13], [0, 1]]
 g := ![![[44, 44, 41], [54, 71], [22, 67], [60, 11, 72], [24, 1], []], ![[32, 6, 3, 62], [], [47, 2], [44, 46, 33, 10], [5, 9], [62, 23]], ![[53, 69, 16, 59], [20, 71], [62, 64], [6, 21, 15, 53], [4, 4], [36, 23]]]
 h' := ![![[66, 2, 60], [32, 25, 25], [30, 59, 12], [17, 18, 33], [36, 2, 27], [0, 0, 1], [0, 1]], ![[31, 70, 13], [49, 41, 38], [7, 29], [51, 65, 32], [60, 41, 39], [69, 23, 70], [66, 2, 60]], ![[0, 1], [48, 7, 10], [23, 58, 61], [52, 63, 8], [55, 30, 7], [66, 50, 2], [31, 70, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 10], []]
 b := ![[], [64, 68, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [35, 38, 49, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25411, -21952, 51884, 28884, -157144]
  a := ![4, -3, 13, 8, -35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![57363, 7156, 24376, 28884, -157144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -21, -11, -2, -24]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![7, -21, -11, -2, -24]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![24, 24, 1, 0, 0], ![8, 32, 0, 1, 0], ![58, 45, 0, 0, 1]] where
  M :=![![![7, -21, -11, -2, -24], ![4, 29, 41, 23, -156], ![-46, 183, 180, 82, -366], ![-164, 402, 341, 136, -354], ![-78, 197, 170, 69, -197]]]
  hmulB := by decide  
  f := ![![![-11, 36, -11, 43, -84]], ![![-86, 116, -97, -142, 354]], ![![-28, 42, -30, -29, 78]], ![![-46, 73, -55, -59, 156]], ![![-62, 101, -69, -53, 151]]]
  g := ![![![23, 19, -11, -2, -24], ![108, 73, 41, 23, -156], ![222, 133, 180, 82, -366], ![152, 52, 341, 136, -354], ![92, 38, 170, 69, -197]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [60, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 72], [0, 1]]
 g := ![![[59, 41], [16], [37], [72, 16], [55], [1]], ![[43, 32], [16], [37], [7, 57], [55], [1]]]
 h' := ![![[37, 72], [38, 25], [66, 4], [60, 16], [8, 4], [13, 37], [0, 1]], ![[0, 1], [14, 48], [68, 69], [68, 57], [10, 69], [68, 36], [37, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [29, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [60, 36, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11722, -11054, 17666, 13581, -62533]
  a := ![-26, 23, -80, -56, 235]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![42548, 26635, 17666, 13581, -62533]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![11, -36, 11, -43, 84]] ![![7, -21, -11, -2, -24]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, -2, 8]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![7, 0, 0, -2, 8]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![66, 78, 52, 1, 0], ![47, 59, 13, 0, 1]] where
  M :=![![![7, 0, 0, -2, 8], ![4, -3, -2, 2, 4], ![-4, 2, -25, -16, 56], ![32, -76, 2, -1, -8], ![8, -18, -12, -6, 17]]]
  hmulB := by decide  
  f := ![![![9, 0, -4, -2, 8]], ![![4, -1, -2, -2, 4]], ![![4, -2, 5, 4, -16]], ![![14, -2, -2, -1, 0]], ![![9, -1, -3, -2, 5]]]
  g := ![![![-3, -4, 0, -2, 8], ![-4, -5, -2, 2, 4], ![-20, -26, 1, -16, 56], ![6, 6, 2, -1, -8], ![-5, -7, 1, -6, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [61, 63, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 7, 30], [73, 71, 49], [0, 1]]
 g := ![![[8, 59, 46], [40, 32, 22], [44, 14, 26], [36, 63, 46], [59, 1], []], ![[41, 25, 11, 43], [68, 61, 16, 68], [65, 62, 72, 58], [25, 38, 77, 35], [46, 64], [37, 31]], ![[15, 57, 43, 25], [70, 45, 73, 19], [29, 76, 30, 65], [15, 32, 36, 67], [42, 49], [18, 31]]]
 h' := ![![[65, 7, 30], [9, 35, 58], [2, 27, 38], [16, 12, 42], [35, 14, 21], [0, 0, 1], [0, 1]], ![[73, 71, 49], [61, 40, 33], [69, 22, 32], [28, 20, 24], [8, 66, 15], [72, 6, 71], [65, 7, 30]], ![[0, 1], [60, 4, 67], [11, 30, 9], [54, 47, 13], [6, 78, 43], [44, 73, 7], [73, 71, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 5], []]
 b := ![[], [21, 5, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [61, 63, 20, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![257763, -134965, 779550, 787409, -2224572]
  a := ![11, -6, 39, 29, -100]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![668907, 882239, -142358, 787409, -2224572]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 3, -1, 0, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-1, 3, -1, 0, 0]] 
 ![![79, 0, 0, 0, 0], ![48, 1, 0, 0, 0], ![66, 0, 1, 0, 0], ![71, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![-1, 3, -1, 0, 0], ![0, -1, 3, -1, 0], ![2, -1, 6, 8, -18], ![-16, 28, -21, -16, 54], ![-2, 3, -2, -1, 7]]]
  hmulB := by decide  
  f := ![![![1851, 88, -547, -369, 1440]], ![![1134, 54, -335, -226, 882]], ![![1550, 74, -458, -309, 1206]], ![![1665, 79, -492, -332, 1296]], ![![988, 47, -292, -197, 769]]]
  g := ![![![-1, 3, -1, 0, 0], ![-1, -1, 3, -1, 0], ![-2, -1, 6, 8, -18], ![-14, 28, -21, -16, 54], ![-3, 3, -2, -1, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![225, 10, -67, -45, 176]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![225, 10, -67, -45, 176]] 
 ![![79, 0, 0, 0, 0], ![58, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![61, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![225, 10, -67, -45, 176], ![90, 4, -27, -18, 70], ![36, 2, -10, -7, 26], ![14, 3, -1, -1, 4], ![38, 3, -10, -7, 27]]]
  hmulB := by decide  
  f := ![![![9, -11, 19, 24, -52]], ![![6, -7, 13, 17, -36]], ![![5, -8, 9, 10, -22]], ![![7, -7, 12, 20, -42]], ![![3, -4, 5, 7, -15]]]
  g := ![![![7, 10, -67, -45, 176], ![3, 4, -27, -18, 70], ![1, 2, -10, -7, 26], ![-2, 3, -1, -1, 4], ![0, 3, -10, -7, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0, -2, 8]] ![![-1, 3, -1, 0, 0]]
  ![![9, -11, 19, 24, -52]] where
 M := ![![![9, -11, 19, 24, -52]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![9, -11, 19, 24, -52]] ![![225, 10, -67, -45, 176]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 24, -44, -28, 106]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![107, 24, -44, -28, 106]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![66, 66, 45, 6, 1]] where
  M :=![![![107, 24, -44, -28, 106], ![56, -27, 8, -10, 26], ![20, 20, -9, 32, -50], ![-64, 102, -104, -119, 326], ![12, 12, -22, -14, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, -2]], ![![0, 3, 4, 2, -10]], ![![-4, 12, 9, 4, -14]], ![![-8, 14, 12, 3, 2]], ![![-2, 10, 9, 4, -17]]]
  g := ![![![-83, -84, -58, -8, 106], ![-20, -21, -14, -2, 26], ![40, 40, 27, 4, -50], ![-260, -258, -178, -25, 326], ![-42, -42, -29, -4, 53]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [26, 4, 74, 13, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 54, 40, 63], [17, 43, 19, 38], [5, 68, 24, 65], [0, 1]]
 g := ![![[62, 7, 61, 81], [63, 62, 6, 59], [25, 56, 77], [48, 38, 61], [70, 1], []], ![[5, 46, 13, 1, 70, 65], [49, 69, 2, 50, 80, 44], [30, 9, 26], [29, 11, 7], [7, 30, 24, 73, 39, 11], [57, 6, 68]], ![[36, 42, 36, 45, 37, 3], [13, 17, 80, 37, 45, 38], [57, 36, 3], [80, 37, 16], [16, 51, 58, 59, 74, 51], [27, 19, 33]], ![[55, 2, 4, 19, 80, 28], [16, 48, 42, 57, 57, 12], [20, 58, 21], [8, 78, 78], [10, 14, 65, 41, 9, 64], [51, 70, 75]]]
 h' := ![![[48, 54, 40, 63], [22, 40, 58, 74], [24, 3, 60, 68], [33, 45, 76, 49], [6, 26, 45, 12], [0, 0, 1], [0, 1]], ![[17, 43, 19, 38], [64, 54, 28, 15], [15, 15, 82, 60], [52, 65, 53, 62], [68, 37, 81, 16], [75, 69, 82, 30], [48, 54, 40, 63]], ![[5, 68, 24, 65], [30, 5, 35, 29], [16, 44, 15, 82], [2, 53, 38, 13], [67, 75, 42, 79], [2, 30, 61, 41], [17, 43, 19, 38]], ![[0, 1], [55, 67, 45, 48], [71, 21, 9, 39], [33, 3, 82, 42], [65, 28, 81, 59], [27, 67, 22, 12], [5, 68, 24, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [62, 38, 17], []]
 b := ![[], [], [81, 25, 36, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [26, 4, 74, 13, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-90455382, 185632664, -125834520, -76857320, 242580672]
  a := ![-4, 2, -12, -20, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-193985298, -190658936, -133035720, -18461944, 242580672]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 0, 0, 0, 2]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-1, 0, 0, 0, 2]] 
 ![![83, 0, 0, 0, 0], ![53, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![58, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![-1, 0, 0, 0, 2], ![0, -3, -4, -2, 10], ![4, -12, -9, -4, 14], ![8, -14, -12, -3, -2], ![4, -8, -6, -2, 1]]]
  hmulB := by decide  
  f := ![![![-107, -24, 44, 28, -106]], ![![-69, -15, 28, 18, -68]], ![![-17, -4, 7, 4, -16]], ![![-74, -18, 32, 21, -78]], ![![-53, -12, 22, 14, -53]]]
  g := ![![![-1, 0, 0, 0, 2], ![-1, -3, -4, -2, 10], ![5, -12, -9, -4, 14], ![14, -14, -12, -3, -2], ![7, -8, -6, -2, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![107, 24, -44, -28, 106]] ![![-1, 0, 0, 0, 2]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![-83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0, 0, 0]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]] where
  M :=![![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![0, 0, 0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 5 2 6 [8, 54, 0, 39, 87, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 43, 58, 1, 11], [70, 47, 0, 34, 8], [68, 25, 13, 55, 24], [12, 62, 18, 88, 46], [0, 1]]
 g := ![![[63, 52, 29, 28, 18], [63, 45, 57, 79], [9, 75, 58, 49], [0, 40, 1, 30, 4], [1], []], ![[86, 1, 86, 15, 84, 49, 76, 8], [5, 38, 15, 40], [34, 35, 47, 88], [88, 57, 12, 25, 57, 28, 26, 80], [78, 56, 59, 11, 45, 48, 83, 55], [68, 23, 86, 32]], ![[82, 18, 51, 56, 7, 18, 55, 69], [73, 37, 26, 87], [13, 78, 8, 22], [68, 16, 58, 34, 74, 18, 14, 69], [31, 69, 31, 56, 77, 33, 64, 39], [6, 4, 49, 64]], ![[38, 66, 81, 56, 61, 22, 30, 76], [62, 46, 73, 64], [86, 14, 62, 64], [48, 43, 30, 55, 23, 3, 47, 66], [45, 77, 86, 42, 61, 72, 24, 41], [45, 72, 54, 42]], ![[58, 41, 8, 39, 10, 82, 84, 23], [77, 14, 43, 50], [36, 11, 51, 8], [67, 53, 88, 69, 42, 87, 35, 86], [15, 26, 43, 18, 38, 43, 69, 35], [32, 37, 46, 69]]]
 h' := ![![[30, 43, 58, 1, 11], [52, 76, 88, 76, 14], [17, 71, 57, 11, 48], [0, 11, 31, 41, 82], [81, 35, 0, 50, 2], [0, 0, 1], [0, 1]], ![[70, 47, 0, 34, 8], [7, 85, 14, 61, 5], [15, 19, 46, 71, 29], [38, 48, 61, 32, 55], [88, 57, 8, 4, 28], [0, 59, 17, 77, 19], [30, 43, 58, 1, 11]], ![[68, 25, 13, 55, 24], [48, 77, 45, 70, 24], [3, 22, 72, 56, 40], [14, 10, 50, 22, 72], [43, 24, 71, 59, 24], [46, 83, 88, 33, 4], [70, 47, 0, 34, 8]], ![[12, 62, 18, 88, 46], [18, 31, 84, 10, 14], [46, 3, 39, 80, 8], [72, 4, 7, 7, 8], [76, 19, 38, 58, 84], [81, 38, 31, 8, 40], [68, 25, 13, 55, 24]], ![[0, 1], [86, 87, 36, 50, 32], [48, 63, 53, 49, 53], [46, 16, 29, 76, 50], [87, 43, 61, 7, 40], [66, 87, 41, 60, 26], [12, 62, 18, 88, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 44, 12, 48], [], [], []]
 b := ![[], [78, 13, 69, 86, 28], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 5
  hpos := by decide
  P := [8, 54, 0, 39, 87, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9428352772, -9653884735, -3512875301, 508938312, -29634031405]
  a := ![-4, 8, -7, -3, 49]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![105936548, -108470615, -39470509, 5718408, -332966645]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 5584059449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![901, 43, -268, -177, 700]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![901, 43, -268, -177, 700]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![66, 39, 75, 47, 1]] where
  M :=![![![901, 43, -268, -177, 700], ![354, 24, -118, -83, 314], ![166, -43, -23, -17, 76], ![34, 73, -76, -14, 74], ![156, 4, -52, -30, 117]]]
  hmulB := by decide  
  f := ![![![1, -3, -2, -1, 4]], ![![2, -4, -4, -1, 2]], ![![2, -1, -1, -1, -8]], ![![2, 9, 22, 12, -58]], ![![4, 0, 7, 4, -31]]]
  g := ![![![-467, -281, -544, -341, 700], ![-210, -126, -244, -153, 314], ![-50, -31, -59, -37, 76], ![-50, -29, -58, -36, 74], ![-78, -47, -91, -57, 117]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [55, 10, 60, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 47, 18, 66], [89, 45, 54, 90], [27, 4, 25, 38], [0, 1]]
 g := ![![[71, 55, 94, 72], [78, 85, 94], [94, 36, 89], [87, 13, 81], [73, 91, 1], []], ![[84, 21, 2, 53, 57, 12], [20, 77, 11], [30, 65, 2], [38, 1, 64], [89, 62, 95], [5, 93, 31, 30, 71, 85]], ![[50, 65, 89, 83, 4, 45], [55, 45, 49], [86, 74, 96], [96, 53, 73], [88, 34, 85], [78, 96, 78, 73, 5, 45]], ![[14, 13, 47, 28, 45, 21], [81, 40, 16], [81, 94, 4], [19, 59, 88], [52, 14, 65], [88, 7, 23, 61, 34, 67]]]
 h' := ![![[72, 47, 18, 66], [22, 20, 65, 13], [74, 56, 64, 71], [54, 6, 23, 63], [59, 85, 87, 9], [0, 0, 0, 1], [0, 1]], ![[89, 45, 54, 90], [73, 16, 89, 94], [94, 18, 95, 37], [17, 66, 27, 14], [19, 77, 18, 8], [8, 25, 67, 80], [72, 47, 18, 66]], ![[27, 4, 25, 38], [76, 1, 44, 7], [71, 50, 52, 90], [57, 59, 28, 22], [83, 5, 6, 49], [48, 58, 47, 45], [89, 45, 54, 90]], ![[0, 1], [38, 60, 93, 80], [15, 70, 80, 93], [28, 63, 19, 95], [54, 27, 83, 31], [2, 14, 80, 68], [27, 4, 25, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [96, 19, 68], []]
 b := ![[], [], [90, 6, 33, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [55, 10, 60, 6, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![733729, -1989656, -1799648, -718151, 2319407]
  a := ![2, -3, 6, 2, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1570589, -953057, -1811909, -1131240, 2319407]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -3, -2, -1, 4]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![1, -3, -2, -1, 4]] 
 ![![97, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![75, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![1, -3, -2, -1, 4], ![2, -4, -4, -1, 2], ![2, -1, -1, -1, -8], ![2, 9, 22, 12, -58], ![0, 6, 8, 4, -23]]]
  hmulB := by decide  
  f := ![![![901, 43, -268, -177, 700]], ![![208, 10, -62, -41, 162]], ![![11, 0, -3, -2, 8]], ![![697, 34, -208, -137, 542]], ![![336, 16, -100, -66, 261]]]
  g := ![![![0, -3, -2, -1, 4], ![1, -4, -4, -1, 2], ![4, -1, -1, -1, -8], ![10, 9, 22, 12, -58], ![4, 6, 8, 4, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![901, 43, -268, -177, 700]] ![![1, -3, -2, -1, 4]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -30, 35, 39, -110]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-21, -30, 35, 39, -110]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![65, 60, 18, 1, 0], ![82, 95, 18, 0, 1]] where
  M :=![![![-21, -30, 35, 39, -110], ![-78, 128, -83, -50, 152], ![100, -280, 174, 15, -140], ![-30, 255, -105, 239, -430], ![6, -13, 16, 31, -75]]]
  hmulB := by decide  
  f := ![![![-11, 35, 35, 16, -70]], ![![-32, 75, 63, 25, -62]], ![![-50, 55, 24, 0, 140]], ![![-35, 75, 62, 24, -50]], ![![-48, 108, 91, 36, -87]]]
  g := ![![![64, 80, 13, 39, -110], ![-92, -112, -19, -50, 152], ![105, 120, 24, 15, -140], ![195, 265, 33, 239, -430], ![41, 52, 8, 31, -75]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [11, 74, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 5, 97], [8, 95, 4], [0, 1]]
 g := ![![[61, 16, 4], [71, 76], [10, 40, 76], [93, 68], [94, 17], [1]], ![[80, 16, 87, 52], [36, 65], [59, 0, 71, 17], [20, 84], [73, 14], [53, 82, 50, 37]], ![[14, 55, 97, 9], [12, 100], [23, 5, 92, 13], [77, 24], [27, 19], [7, 50, 3, 64]]]
 h' := ![![[36, 5, 97], [7, 40, 99], [92, 41, 50], [3, 29, 51], [97, 40, 13], [90, 27, 44], [0, 1]], ![[8, 95, 4], [30, 33, 54], [27, 37, 41], [63, 10, 83], [92, 23, 65], [17, 72, 32], [36, 5, 97]], ![[0, 1], [87, 28, 49], [57, 23, 10], [93, 62, 68], [58, 38, 23], [31, 2, 25], [8, 95, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89, 13], []]
 b := ![[], [57, 34, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [11, 74, 57, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![56519, -96235, 63728, 65511, -187536]
  a := ![-3, 3, -2, -10, 30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![110656, 136525, 22378, 65511, -187536]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -1, 3, 2, -8]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-9, -1, 3, 2, -8]] 
 ![![101, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![56, 0, 0, 0, 1]] where
  M :=![![![-9, -1, 3, 2, -8], ![-4, 1, 1, 1, -4], ![-2, 1, 2, 0, -2], ![0, 0, 5, 4, -10], ![-2, 1, 2, 1, -3]]]
  hmulB := by decide  
  f := ![![![-11, 10, 19, 13, -40]], ![![-2, 2, 3, 2, -6]], ![![-5, 4, 9, 6, -18]], ![![-6, 5, 9, 7, -20]], ![![-6, 5, 10, 7, -21]]]
  g := ![![![2, -1, 3, 2, -8], ![1, 1, 1, 1, -4], ![0, 1, 2, 0, -2], ![1, 0, 5, 4, -10], ![0, 1, 2, 1, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 20, 16, 6, -10]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-9, 20, 16, 6, -10]] 
 ![![101, 0, 0, 0, 0], ![67, 1, 0, 0, 0], ![56, 0, 1, 0, 0], ![86, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![-9, 20, 16, 6, -10], ![-12, 7, -2, -4, 58], ![8, -74, -81, -40, 218], ![80, -250, -230, -99, 370], ![36, -118, -110, -48, 187]]]
  hmulB := by decide  
  f := ![![![459, -84, -48, -26, 158]], ![![305, -53, -34, -18, 108]], ![![256, -50, -25, -16, 90]], ![![394, -74, -38, -15, 118]], ![![292, -54, -30, -16, 99]]]
  g := ![![![-21, 20, 16, 6, -10], ![-37, 7, -2, -4, 58], ![-10, -74, -81, -40, 218], ![144, -250, -230, -99, 370], ![62, -118, -110, -48, 187]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-21, -30, 35, 39, -110]] ![![-9, -1, 3, 2, -8]]
  ![![459, -84, -48, -26, 158]] where
 M := ![![![459, -84, -48, -26, 158]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![459, -84, -48, -26, 158]] ![![-9, 20, 16, 6, -10]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 38, 60, 26, -160]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![1, 38, 60, 26, -160]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![56, 68, 64, 14, 1]] where
  M :=![![![1, 38, 60, 26, -160], ![-52, 187, 176, 90, -332], ![-180, 370, 221, 58, -40], ![-116, -82, 44, -29, 844], ![-96, 60, 8, -24, 425]]]
  hmulB := by decide  
  f := ![![![471, 22, -140, -94, 368]], ![![188, 9, -56, -38, 148]], ![![76, 2, -21, -14, 56]], ![![28, 6, -12, -7, 28]], ![![432, 20, -128, -86, 337]]]
  g := ![![![87, 106, 100, 22, -160], ![180, 221, 208, 46, -332], ![20, 30, 27, 6, -40], ![-460, -558, -524, -115, 844], ![-232, -280, -264, -58, 425]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 4 2 6 [101, 20, 29, 77, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 64, 10, 43], [11, 61, 25, 25], [17, 80, 68, 35], [0, 1]]
 g := ![![[102, 70, 94, 52], [64, 77, 36, 13], [80, 50, 99, 23], [51, 76, 91], [29, 26, 1], []], ![[47, 43, 12, 77, 34, 71], [11, 60, 71, 99, 18, 20], [6, 77, 69, 16, 75, 40], [101, 23, 66], [69, 7, 2], [45, 9, 62, 54, 28, 94]], ![[76, 84, 24, 97, 60, 76], [53, 13, 41, 96, 73, 14], [17, 9, 6, 87, 1, 34], [82, 38, 97], [53, 30, 29], [53, 68, 55, 34, 28, 72]], ![[27, 41, 59, 2, 62, 20], [39, 84, 99, 78, 13, 51], [27, 64, 89, 5, 75, 12], [39, 98, 2], [51, 32, 98], [85, 62, 56, 32, 3, 27]]]
 h' := ![![[101, 64, 10, 43], [25, 63, 97, 19], [57, 2, 60, 61], [67, 96, 79, 34], [58, 90, 83, 83], [0, 0, 0, 1], [0, 1]], ![[11, 61, 25, 25], [89, 48, 78, 53], [92, 24, 53, 31], [75, 43, 21, 45], [64, 23, 77, 90], [82, 92, 36, 38], [101, 64, 10, 43]], ![[17, 80, 68, 35], [81, 64, 19, 97], [44, 53, 17, 16], [21, 71, 93, 35], [28, 20, 71, 71], [98, 1, 22, 21], [11, 61, 25, 25]], ![[0, 1], [85, 31, 12, 37], [79, 24, 76, 98], [57, 99, 13, 92], [59, 73, 78, 65], [36, 10, 45, 43], [17, 80, 68, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [49, 55, 45], []]
 b := ![[], [], [9, 31, 67, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 4
  hpos := by decide
  P := [101, 20, 29, 77, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2603929, -1876059, 6164740, 7440150, -19472485]
  a := ![-8, 5, -28, -20, 73]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10612263, 12837407, 12159260, 2718980, -19472485]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 112550881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-471, -22, 140, 94, -368]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-471, -22, 140, 94, -368]] 
 ![![103, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![77, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![96, 0, 0, 0, 1]] where
  M :=![![![-471, -22, 140, 94, -368], ![-188, -9, 56, 38, -148], ![-76, -2, 21, 14, -56], ![-28, -6, 12, 7, -28], ![-80, -4, 24, 16, -63]]]
  hmulB := by decide  
  f := ![![![-1, -38, -60, -26, 160]], ![![0, -21, -32, -14, 84]], ![![1, -32, -47, -20, 120]], ![![1, -4, -8, -3, 12]], ![![0, -36, -56, -24, 145]]]
  g := ![![![233, -22, 140, 94, -368], ![94, -9, 56, 38, -148], ![35, -2, 21, 14, -56], ![19, -6, 12, 7, -28], ![40, -4, 24, 16, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![1, 38, 60, 26, -160]] ![![-471, -22, 140, 94, -368]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![-103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB175I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB175I2 : PrimesBelowBoundCertificateInterval O 61 103 175 where
  m := 9
  g := ![2, 1, 2, 3, 2, 1, 2, 3, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB175I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
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
    · exact ![20151121, 67]
    · exact ![1804229351]
    · exact ![389017, 5329]
    · exact ![493039, 79, 79]
    · exact ![47458321, 83]
    · exact ![5584059449]
    · exact ![88529281, 97]
    · exact ![1030301, 101, 101]
    · exact ![112550881, 103]
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
      exact NI79N2
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
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
      exact NI103N1
  β := ![I67N1, I79N1, I79N2, I83N1, I97N1, I101N1, I101N2, I103N1]
  Il := ![[I67N1], [], [], [I79N1, I79N2], [I83N1], [], [I97N1], [I101N1, I101N2], [I103N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
