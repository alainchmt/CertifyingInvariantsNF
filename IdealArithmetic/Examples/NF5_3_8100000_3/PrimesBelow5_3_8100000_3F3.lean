
import IdealArithmetic.Examples.NF5_3_8100000_3.RI5_3_8100000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1132, -61, 99, 41, 315]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-1132, -61, 99, 41, 315]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![46, 28, 37, 11, 1]] where
  M :=![![![-1132, -61, 99, 41, 315], ![945, 110, -61, 5, -233], ![-699, 63, 110, 105, 243], ![-351, 5, 41, 44, 111], ![342, 50, -18, 12, -67]]]
  hmulB := by decide  
  f := ![![![-2, -3, 1, -1, 3]], ![![9, 10, -3, -1, -5]], ![![-15, -15, 10, -9, 3]], ![![-3, -1, -1, 8, -1]], ![![-4, -4, 3, -3, 1]]]
  g := ![![![-146, -83, -108, -32, 315], ![109, 62, 80, 24, -233], ![-111, -63, -83, -24, 243], ![-51, -29, -38, -11, 111], ![32, 18, 23, 7, -67]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 4 2 6 [52, 86, 63, 16, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 44, 61, 61], [55, 46, 60, 61], [75, 16, 93, 92], [0, 1]]
 g := ![![[81, 4, 42, 14], [76, 89, 0, 36], [47, 47, 39], [77, 98, 56, 34], [86, 91, 1], []], ![[95, 87, 95, 7, 93, 64], [43, 8, 73, 78, 100, 41], [95, 102, 105], [12, 98, 83, 55, 34, 49], [36, 8, 87], [72, 74, 57, 45, 93, 34]], ![[25, 23, 28, 90, 42, 52], [27, 7, 20, 89, 77, 23], [95, 13, 49], [56, 65, 61, 32, 34, 19], [93, 13, 83], [96, 80, 13, 39, 58, 34]], ![[49, 12, 18, 90, 21, 89], [70, 50, 25, 78, 15, 9], [57, 64, 19], [97, 90, 70, 54, 88, 23], [4, 57, 48], [31, 46, 63, 104, 38, 49]]]
 h' := ![![[68, 44, 61, 61], [7, 45, 51, 11], [9, 58, 59, 101], [62, 1, 50, 57], [22, 70, 79, 81], [0, 0, 0, 1], [0, 1]], ![[55, 46, 60, 61], [69, 76, 24, 27], [105, 71, 16, 81], [4, 48, 61, 76], [49, 87, 106, 70], [67, 58, 89, 80], [68, 44, 61, 61]], ![[75, 16, 93, 92], [102, 38, 80, 99], [24, 80, 17, 69], [91, 22, 34, 7], [66, 66, 106, 9], [27, 39, 68, 61], [55, 46, 60, 61]], ![[0, 1], [11, 55, 59, 77], [68, 5, 15, 70], [101, 36, 69, 74], [25, 98, 30, 54], [74, 10, 57, 72], [75, 16, 93, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 66, 16], []]
 b := ![[], [], [73, 30, 74, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 4
  hpos := by decide
  P := [52, 86, 63, 16, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1305886, 3882200, 1672024, 3825008, 1644996]
  a := ![0, -2, -4, -10, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-694990, -394184, -553204, -133364, 1644996]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 131079601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -3, 1, -1, 3]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-2, -3, 1, -1, 3]] 
 ![![107, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![94, 0, 1, 0, 0], ![72, 0, 0, 1, 0], ![78, 0, 0, 0, 1]] where
  M :=![![![-2, -3, 1, -1, 3], ![9, 10, -3, -1, -5], ![-15, -15, 10, -9, 3], ![-3, -1, -1, 8, -1], ![0, -4, 0, -2, 9]]]
  hmulB := by decide  
  f := ![![![-1132, -61, 99, 41, 315]], ![![-901, -48, 79, 33, 251]], ![![-1001, -53, 88, 37, 279]], ![![-765, -41, 67, 28, 213]], ![![-822, -44, 72, 30, 229]]]
  g := ![![![0, -3, 1, -1, 3], ![-1, 10, -3, -1, -5], ![7, -15, 10, -9, 3], ![-3, -1, -1, 8, -1], ![-2, -4, 0, -2, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-1132, -61, 99, 41, 315]] ![![-2, -3, 1, -1, 3]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 5, 1, 2, -6]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![37, 5, 1, 2, -6]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![19, 34, 47, 1, 0], ![91, 65, 70, 0, 1]] where
  M :=![![![37, 5, 1, 2, -6], ![-18, 22, 5, 20, 10], ![30, 27, 22, 30, 30], ![24, 20, 2, 7, 0], ![-12, 5, 9, 6, 7]]]
  hmulB := by decide  
  f := ![![![1, -1, 1, 0, -2]], ![![-6, -2, -1, 10, 2]], ![![6, -3, -2, 0, 18]], ![![1, -2, -1, 3, 8]], ![![1, -4, -1, 6, 11]]]
  g := ![![![5, 3, 3, 2, -6], ![-12, -12, -15, 20, 10], ![-30, -27, -32, 30, 30], ![-1, -2, -3, 7, 0], ![-7, -6, -7, 6, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [88, 85, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 72, 31], [77, 36, 78], [0, 1]]
 g := ![![[40, 63, 60], [103, 82], [85, 46, 49], [47, 88, 27], [90, 63], [1]], ![[26, 101, 20, 81], [25, 1], [61, 44, 89, 28], [77, 46, 24, 25], [42, 66], [106, 34, 44, 34]], ![[99, 46, 104, 78], [74, 84], [51, 50, 5, 31], [37, 27, 92, 46], [2, 12], [62, 106, 16, 75]]]
 h' := ![![[77, 72, 31], [29, 104, 13], [41, 99, 54], [6, 53, 102], [42, 22, 71], [21, 24, 45], [0, 1]], ![[77, 36, 78], [23, 62, 95], [32, 10, 108], [26, 84, 83], [58, 57, 77], [87, 11, 75], [77, 72, 31]], ![[0, 1], [54, 52, 1], [35, 0, 56], [68, 81, 33], [68, 30, 70], [35, 74, 98], [77, 36, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 27], []]
 b := ![[], [48, 41, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [88, 85, 64, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-92670050, -281130766, -121296154, -286456968, -123477356]
  a := ![3, -65, -62, -191, -186]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![152169282, 160407654, 201702718, -286456968, -123477356]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, 1, 0, -2]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![1, -1, 1, 0, -2]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![80, 45, 1, 0, 0], ![54, 76, 0, 1, 0], ![94, 23, 0, 0, 1]] where
  M :=![![![1, -1, 1, 0, -2], ![-6, -2, -1, 10, 2], ![6, -3, -2, 0, 18], ![12, 10, 0, -13, -4], ![-12, -5, 5, 4, -9]]]
  hmulB := by decide  
  f := ![![![37, 5, 1, 2, -6]], ![![-18, 22, 5, 20, 10]], ![![20, 13, 3, 10, 0]], ![![6, 18, 4, 15, 4]], ![![28, 9, 2, 6, -3]]]
  g := ![![![1, 0, 1, 0, -2], ![-6, -7, -1, 10, 2], ![-14, -3, -2, 0, 18], ![10, 10, 0, -13, -4], ![2, -3, 5, 4, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [42, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 108], [0, 1]]
 g := ![![[41, 82], [63], [18, 27], [1, 102], [36], [22, 1]], ![[101, 27], [63], [67, 82], [65, 7], [36], [44, 108]]]
 h' := ![![[22, 108], [19, 54], [7, 45], [67, 38], [102, 59], [57, 6], [0, 1]], ![[0, 1], [8, 55], [16, 64], [31, 71], [92, 50], [80, 103], [22, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [107, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where
  n := 2
  hpos := by decide
  P := [42, 87, 1]
  hirr := P109P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![247, 338, 20, 67, -497]
  a := ![1, -4, -4, -13, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![383, 53, 20, 67, -497]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![37, 5, 1, 2, -6]] ![![1, -1, 1, 0, -2]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -5, -3, 16, 4]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![13, -5, -3, 16, 4]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![59, 32, 61, 1, 0], ![78, 12, 66, 0, 1]] where
  M :=![![![13, -5, -3, 16, 4], ![12, 16, -5, -10, 28], ![84, 81, 16, -96, -48], ![-30, -10, 16, 21, -38], ![-42, -43, -13, 86, 59]]]
  hmulB := by decide  
  f := ![![![41, 45, -19, 18, -28]], ![![-84, -100, 45, -40, 64]], ![![192, 243, -100, 102, -144]], ![![101, 126, -51, 53, -74]], ![![132, 163, -67, 68, -97]]]
  g := ![![![-11, -5, -11, 16, 4], ![-14, 0, -11, -10, 28], ![84, 33, 80, -96, -48], ![15, -2, 11, 21, -38], ![-86, -31, -81, 86, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [15, 7, 68, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 12, 102], [106, 100, 11], [0, 1]]
 g := ![![[102, 106, 1], [22, 7], [20, 87], [97, 82], [99, 95, 104], [1]], ![[10, 69, 37, 109], [17, 52], [62, 41], [37, 28], [2, 15, 38, 82], [40, 16, 57, 25]], ![[91, 77, 46, 32], [35, 49], [96, 31], [42, 98], [32, 38, 59, 88], [24, 18, 32, 88]]]
 h' := ![![[52, 12, 102], [100, 87, 1], [54, 89, 32], [44, 20, 58], [97, 28, 67], [98, 106, 45], [0, 1]], ![[106, 100, 11], [12, 31, 47], [43, 66, 74], [42, 20, 43], [22, 39, 64], [1, 96, 57], [52, 12, 102]], ![[0, 1], [12, 108, 65], [57, 71, 7], [64, 73, 12], [4, 46, 95], [88, 24, 11], [106, 100, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82, 51], []]
 b := ![[], [22, 50, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [15, 7, 68, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3731716, 12958703, 6067437, 15917163, 7889741]
  a := ![1, 18, 23, 62, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13723723, -5230685, -13146924, 15917163, 7889741]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -45, 19, -18, 28]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-41, -45, 19, -18, 28]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![88, 86, 1, 0, 0], ![57, 82, 0, 1, 0], ![36, 21, 0, 0, 1]] where
  M :=![![![-41, -45, 19, -18, 28], ![84, 100, -45, 40, -64], ![-192, -243, 100, -102, 144], ![30, 40, -18, 15, -26], ![-54, -71, 29, -28, 41]]]
  hmulB := by decide  
  f := ![![![-13, 5, 3, -16, -4]], ![![-12, -16, 5, 10, -28]], ![![-20, -9, 6, -4, -24]], ![![-15, -9, 5, -1, -22]], ![![-6, -1, 2, -4, -7]]]
  g := ![![![-15, -7, 19, -18, 28], ![36, 18, -45, 40, -64], ![-74, -31, 100, -102, 144], ![15, 8, -18, 15, -26], ![-22, -10, 29, -28, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [59, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 112], [0, 1]]
 g := ![![[37, 52], [111], [15], [98], [110, 36], [77, 1]], ![[86, 61], [111], [15], [98], [57, 77], [41, 112]]]
 h' := ![![[77, 112], [61, 74], [100, 26], [9, 44], [64, 95], [90, 107], [0, 1]], ![[0, 1], [109, 39], [68, 87], [7, 69], [34, 18], [80, 6], [77, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [78, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [59, 36, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![48, 33, 49, 385, 606]
  a := ![-1, 2, -4, -5, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-425, -429, 49, 385, 606]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![13, -5, -3, 16, 4]] ![![-41, -45, 19, -18, 28]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -13, -21, 18, 56]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![13, -13, -21, 18, 56]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![57, 104, 6, 1, 0], ![25, 82, 68, 0, 1]] where
  M :=![![![13, -13, -21, 18, 56], ![168, 118, -13, -220, -20], ![-60, 69, 118, -258, -420], ![-294, -220, 18, 325, -6], ![138, -19, -119, 60, 331]]]
  hmulB := by decide  
  f := ![![![-305, -73, 45, -16, 104]], ![![312, 142, -73, 46, -136]], ![![-408, -315, 142, -120, 228]], ![![99, 69, -33, 25, -54]], ![![-77, -92, 38, -38, 55]]]
  g := ![![![-19, -51, -31, 18, 56], ![104, 194, 21, -220, -20], ![198, 483, 238, -258, -420], ![-147, -264, -12, 325, -6], ![-91, -263, -181, 60, 331]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [31, 100, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 85, 116], [68, 41, 11], [0, 1]]
 g := ![![[38, 119, 79], [115, 55, 64], [63, 27, 88], [20, 118, 64], [19, 0, 73], [1]], ![[71, 21, 81, 23], [80, 57, 7, 67], [27, 49, 29, 123], [5, 109, 21, 39], [26, 52, 74, 53], [77, 1, 13, 66]], ![[49, 10, 43, 26], [14, 88, 92, 49], [118, 24, 116, 94], [106, 24, 111, 74], [2, 85, 102, 72], [98, 54, 5, 61]]]
 h' := ![![[92, 85, 116], [118, 21, 98], [79, 73, 119], [15, 14, 56], [46, 77, 119], [96, 27, 33], [0, 1]], ![[68, 41, 11], [74, 25, 104], [5, 22, 12], [65, 21, 110], [86, 108, 95], [77, 98, 40], [92, 85, 116]], ![[0, 1], [93, 81, 52], [22, 32, 123], [46, 92, 88], [7, 69, 40], [117, 2, 54], [68, 41, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 20], []]
 b := ![[], [83, 89, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [31, 100, 94, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-67841, -118440, 93248, -211624, 72368]
  a := ![0, -10, 4, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![80201, 125640, -28016, -211624, 72368]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 1, -2, -4]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![1, 1, 1, -2, -4]] 
 ![![127, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![106, 0, 1, 0, 0], ![69, 0, 0, 1, 0], ![61, 0, 0, 0, 1]] where
  M :=![![![1, 1, 1, -2, -4], ![-12, -8, 1, 12, 0], ![0, -9, -8, 18, 24], ![18, 12, -2, -19, 2], ![-6, 3, 7, -8, -21]]]
  hmulB := by decide  
  f := ![![![139, 41, -57, -4, -92]], ![![23, 5, -10, -2, -16]], ![![118, 35, -50, -4, -80]], ![![75, 21, -31, -3, -50]], ![![67, 20, -28, -2, -45]]]
  g := ![![![2, 1, 1, -2, -4], ![-6, -8, 1, 12, 0], ![-13, -9, -8, 18, 24], ![9, 12, -2, -19, 2], ![8, 3, 7, -8, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -5, 1, 8, -2]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![-7, -5, 1, 8, -2]] 
 ![![127, 0, 0, 0, 0], ![68, 1, 0, 0, 0], ![75, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-7, -5, 1, 8, -2], ![-6, -10, -5, 18, 18], ![54, 33, -10, -48, 18], ![12, 18, 8, -33, -28], ![-48, -33, 5, 52, -5]]]
  hmulB := by decide  
  f := ![![![287, 251, 43, 166, 14]], ![![154, 138, 25, 92, 10]], ![![177, 162, 29, 108, 12]], ![![13, 13, 3, 9, 2]], ![![42, 39, 7, 26, 3]]]
  g := ![![![2, -5, 1, 8, -2], ![5, -10, -5, 18, 18], ![-12, 33, -10, -48, 18], ![-9, 18, 8, -33, -28], ![13, -33, 5, 52, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![13, -13, -21, 18, 56]] ![![1, 1, 1, -2, -4]]
  ![![157, 690, 524, -1350, -1696]] where
 M := ![![![157, 690, 524, -1350, -1696]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![157, 690, 524, -1350, -1696]] ![![-7, -5, 1, 8, -2]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![88265, 41275, -27813, -55118, 67818]]]
 hmul := by decide  
 g := ![![![![695, 325, -219, -434, 534]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0, 0, 0]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]] where
  M :=![![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 5 2 7 [101, 40, 128, 38, 59, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 66, 70, 59, 40], [27, 65, 55, 31, 94], [121, 5, 45, 2, 102], [29, 125, 92, 39, 26], [0, 1]]
 g := ![![[62, 76, 45, 117, 44], [35, 86, 111, 38, 38], [96, 114, 83, 94], [30, 32, 19, 109], [62, 37, 72, 1], [], []], ![[96, 84, 78, 105, 6, 69, 13, 10], [48, 33, 93, 51, 34, 26, 77, 103], [80, 62, 124, 94], [119, 33, 63, 59], [38, 52, 106, 9], [22, 59, 107, 89], [108, 56, 55, 28]], ![[125, 113, 38, 68, 44, 31, 125, 64], [39, 91, 99, 32, 105, 17, 9, 3], [54, 14, 24, 11], [102, 0, 53, 46], [71, 6, 92, 5], [118, 123, 37, 7], [72, 14, 120, 59]], ![[27, 92, 109, 72, 26, 0, 47, 81], [106, 2, 38, 103, 19, 107, 10, 1], [28, 20, 107, 41], [126, 74, 19, 89], [94, 89, 127, 61], [104, 48, 78, 12], [16, 116, 45, 55]], ![[0, 83, 12, 113, 125, 124, 123, 30], [40, 16, 25, 129, 104, 65, 36, 22], [50, 27, 5, 77], [7, 34, 100, 94], [69, 92, 11, 27], [116, 35, 127, 5], [62, 90, 3, 21]]]
 h' := ![![[26, 66, 70, 59, 40], [2, 66, 111, 67, 31], [14, 79, 76, 3, 118], [4, 46, 66, 61, 15], [26, 71, 80, 14, 90], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[27, 65, 55, 31, 94], [36, 78, 26, 86, 65], [83, 58, 125, 108, 22], [98, 86, 79, 73, 116], [14, 119, 2, 30, 94], [70, 67, 7, 3, 128], [117, 6, 1, 69, 73], [26, 66, 70, 59, 40]], ![[121, 5, 45, 2, 102], [127, 78, 69, 84, 113], [68, 43, 118, 115, 20], [85, 39, 117, 102, 81], [118, 28, 23, 120, 35], [52, 46, 72, 40, 108], [7, 2, 102, 87, 111], [27, 65, 55, 31, 94]], ![[29, 125, 92, 39, 26], [14, 119, 24, 50, 104], [32, 85, 7, 120, 128], [41, 124, 17, 57, 98], [45, 56, 27, 129, 58], [99, 109, 83, 35, 42], [56, 120, 75, 0, 55], [121, 5, 45, 2, 102]], ![[0, 1], [0, 52, 32, 106, 80], [53, 128, 67, 47, 105], [115, 98, 114, 100, 83], [125, 119, 130, 100, 116], [85, 40, 100, 53, 114], [81, 3, 83, 106, 23], [29, 125, 92, 39, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 30, 112, 105], [], [], []]
 b := ![[], [39, 38, 87, 21, 112], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 5
  hpos := by decide
  P := [101, 40, 128, 38, 59, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4089034, -19004301, -12595257, -15892265, 14787935]
  a := ![13, 0, -4, -8, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![31214, -145071, -96147, -121315, 112885]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 38579489651 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, -23, 7, -11, 9]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-10, -23, 7, -11, 9]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![17, 41, 1, 0, 0], ![135, 20, 0, 1, 0], ![105, 127, 0, 0, 1]] where
  M :=![![![-10, -23, 7, -11, 9], ![27, 38, -23, 13, -31], ![-93, -135, 38, -63, 57], ![15, 13, -11, 2, -15], ![-30, -38, 12, -18, 17]]]
  hmulB := by decide  
  f := ![![![4, -7, 3, 9, -17]], ![![-51, -38, -7, 61, 35]], ![![-14, -12, -2, 19, 9]], ![![-3, -12, 2, 17, -12]], ![![-45, -41, -4, 64, 19]]]
  g := ![![![3, -9, 7, -11, 9], ![14, 34, -23, 13, -31], ![13, -56, 38, -63, 57], ![11, 17, -11, 2, -15], ![3, -17, 12, -18, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [116, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 136], [0, 1]]
 g := ![![[128, 93], [100], [61], [125, 17], [74], [101], [1]], ![[87, 44], [100], [61], [63, 120], [74], [101], [1]]]
 h' := ![![[85, 136], [27, 97], [121, 10], [22, 91], [84, 90], [96, 99], [21, 85], [0, 1]], ![[0, 1], [52, 40], [12, 127], [85, 46], [62, 47], [17, 38], [122, 52], [85, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [56, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [116, 52, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![98, -31, 42, -211, -96]
  a := ![-1, -4, -1, -8, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![277, 107, 42, -211, -96]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 1, -1, 0, -4]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![13, 1, -1, 0, -4]] 
 ![![137, 0, 0, 0, 0], ![51, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![13, 1, -1, 0, -4], ![-12, -2, 1, 2, 4], ![12, 3, -2, 0, 0], ![6, 2, 0, -3, -2], ![-6, -1, 1, 2, -1]]]
  hmulB := by decide  
  f := ![![![41, 51, -1, 26, -12]], ![![15, 19, 0, 10, -4]], ![![2, 3, 0, 2, 0]], ![![8, 10, 0, 5, -2]], ![![3, 4, 0, 2, -1]]]
  g := ![![![0, 1, -1, 0, -4], ![0, -2, 1, 2, 4], ![-1, 3, -2, 0, 0], ![0, 2, 0, -3, -2], ![0, -1, 1, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 4, 2, -7, -7]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![2, 4, 2, -7, -7]] 
 ![![137, 0, 0, 0, 0], ![79, 1, 0, 0, 0], ![61, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![96, 0, 0, 0, 1]] where
  M :=![![![2, 4, 2, -7, -7], ![-21, -13, 4, 19, -7], ![-21, -30, -13, 57, 45], ![33, 19, -7, -28, 15], ![6, 19, 13, -36, -43]]]
  hmulB := by decide  
  f := ![![![-980, 14, 90, 79, 279]], ![![-559, 9, 52, 46, 160]], ![![-439, 10, 41, 38, 126]], ![![-181, 3, 17, 15, 52]], ![![-684, 11, 63, 56, 195]]]
  g := ![![![3, 4, 2, -7, -7], ![7, -13, 4, 19, -7], ![-19, -30, -13, 57, 45], ![-13, 19, -7, -28, 15], ![20, 19, 13, -36, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2

def I137N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 4, 0, 2, -2]] i)))

def SI137N3: IdealEqSpanCertificate' Table ![![13, 4, 0, 2, -2]] 
 ![![137, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![77, 0, 1, 0, 0], ![88, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![13, 4, 0, 2, -2], ![-6, 7, 4, 6, 6], ![18, 24, 7, 18, 6], ![6, 6, 2, 5, 2], ![0, 6, 2, 4, 3]]]
  hmulB := by decide  
  f := ![![![17, 4, -16, 38, 10]], ![![13, 3, -12, 28, 8]], ![![11, 4, -9, 20, 4]], ![![10, 2, -10, 25, 6]], ![![10, 2, -10, 24, 7]]]
  g := ![![![-3, 4, 0, 2, -2], ![-15, 7, 4, 6, 6], ![-37, 24, 7, 18, 6], ![-10, 6, 2, 5, 2], ![-10, 6, 2, 4, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N3 : Nat.card (O ⧸ I137N3) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N3)

lemma isPrimeI137N3 : Ideal.IsPrime I137N3 := prime_ideal_of_norm_prime hp137.out _ NI137N3
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-10, -23, 7, -11, 9]] ![![13, 1, -1, 0, -4]]
  ![![110, 26, -18, 5, -39]] where
 M := ![![![110, 26, -18, 5, -39]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![110, 26, -18, 5, -39]] ![![2, 4, 2, -7, -7]]
  ![![-17, -4, 16, -38, -10]] where
 M := ![![![-17, -4, 16, -38, -10]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N2 : IdealMulLeCertificate' Table 
  ![![-17, -4, 16, -38, -10]] ![![13, 4, 0, 2, -2]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2, I137N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
    exact isPrimeI137N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1 ⊙ MulI137N2)
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


def P139P0 : CertificateIrreducibleZModOfList' 139 5 2 7 [90, 43, 1, 120, 53, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 48, 8, 95, 71], [67, 67, 64, 122, 62], [73, 45, 124, 37, 99], [93, 117, 82, 24, 46], [0, 1]]
 g := ![![[136, 48, 95, 69, 86], [131, 56, 108, 112, 29], [41, 58, 37, 112], [67, 9, 58, 120, 1], [62, 48, 86, 1], [], []], ![[122, 60, 8, 84, 60, 59, 130, 7], [123, 43, 85, 6, 39, 67, 49, 120], [92, 115, 2, 131], [49, 49, 117, 104, 126, 87, 5, 113], [77, 107, 22, 55], [111, 64, 135, 117], [77, 29, 131, 37]], ![[86, 107, 54, 5, 19, 86, 131, 104], [31, 12, 87, 61, 25, 66, 59, 75], [86, 109, 96, 78], [16, 21, 100, 135, 93, 94, 17, 53], [37, 47, 41, 52], [12, 100, 102, 11], [85, 51, 19, 91]], ![[19, 11, 44, 131, 112, 46, 129, 16], [102, 107, 73, 87, 129, 51, 36, 69], [138, 132, 52, 63], [16, 64, 11, 47, 44, 88, 126, 67], [80, 19, 34, 131], [23, 84, 102, 89], [11, 88, 88, 71]], ![[66, 104, 43, 37, 96, 73, 101, 41], [11, 43, 113, 19, 133, 6, 105, 35], [133, 73, 113, 127], [134, 112, 137, 96, 95, 78, 51, 127], [131, 23, 38, 112], [59, 76, 85, 25], [131, 31, 9, 31]]]
 h' := ![![[131, 48, 8, 95, 71], [25, 15, 122, 45, 124], [92, 62, 25, 130, 86], [86, 45, 75, 127, 116], [119, 103, 3, 122, 138], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[67, 67, 64, 122, 62], [42, 66, 41, 59, 32], [138, 61, 76, 127, 91], [83, 7, 117, 66, 100], [106, 85, 52, 123, 86], [124, 94, 6, 137, 65], [84, 122, 43, 59, 16], [131, 48, 8, 95, 71]], ![[73, 45, 124, 37, 99], [34, 0, 21, 57, 107], [49, 76, 138, 27, 44], [127, 129, 94, 64, 83], [97, 65, 104, 0, 13], [77, 31, 11, 16, 57], [36, 38, 42, 106, 17], [67, 67, 64, 122, 62]], ![[93, 117, 82, 24, 46], [37, 127, 57, 138, 19], [57, 47, 51, 54, 84], [84, 127, 119, 81, 87], [56, 72, 66, 53, 35], [81, 82, 82, 134, 39], [30, 123, 74, 115, 111], [73, 45, 124, 37, 99]], ![[0, 1], [81, 70, 37, 118, 135], [4, 32, 127, 79, 112], [24, 109, 12, 79, 31], [23, 92, 53, 119, 6], [50, 71, 40, 130, 116], [56, 134, 118, 137, 134], [93, 117, 82, 24, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87, 21, 120, 21], [], [], []]
 b := ![[], [23, 5, 84, 111, 125], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 5
  hpos := by decide
  P := [90, 43, 1, 120, 53, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-374378430, -345585831, 427757071, -62925022, 573208478]
  a := ![3, -4, 7, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2693370, -2486229, 3077389, -452698, 4123802]
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



lemma PB140I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 139 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 139 (by omega)

def PB140I3 : PrimesBelowBoundCertificateInterval O 103 139 140 where
  m := 7
  g := ![2, 2, 2, 3, 1, 4, 1]
  P := ![107, 109, 113, 127, 131, 137, 139]
  hP := PB140I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0]
    · exact ![I137N0, I137N1, I137N2, I137N3]
    · exact ![I139N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![131079601, 107]
    · exact ![1295029, 11881]
    · exact ![1442897, 12769]
    · exact ![2048383, 127, 127]
    · exact ![38579489651]
    · exact ![18769, 137, 137, 137]
    · exact ![51888844699]
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
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
      exact NI137N3
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
  β := ![I107N1, I127N1, I127N2, I137N1, I137N2, I137N3]
  Il := ![[I107N1], [], [], [I127N1, I127N2], [], [I137N1, I137N2, I137N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
