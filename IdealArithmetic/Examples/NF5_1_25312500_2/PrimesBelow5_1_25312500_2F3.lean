
import IdealArithmetic.Examples.NF5_1_25312500_2.RI5_1_25312500_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-115, 70, -7, -5, -11]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-115, 70, -7, -5, -11]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![98, 52, 59, 88, 1]] where
  M :=![![![-115, 70, -7, -5, -11], ![98, -55, 59, -19, 1], ![-34, 30, -110, 59, -20], ![164, -44, -17, -58, 65], ![-338, 122, 266, -24, -117]]]
  hmulB := by decide  
  f := ![![![-11, -8, 5, 7, 4]], ![![-28, -23, 11, 17, 10]], ![![-22, -18, 6, 11, 7]], ![![-46, -38, 13, 22, 14]], ![![-74, -60, 24, 39, 24]]]
  g := ![![![9, 6, 6, 9, -11], ![0, -1, 0, -1, 1], ![18, 10, 10, 17, -20], ![-58, -32, -36, -54, 65], ![104, 58, 67, 96, -117]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 4 2 6 [50, 26, 8, 64, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 60, 29, 45], [18, 0, 62, 61], [84, 46, 16, 1], [0, 1]]
 g := ![![[29, 20, 65, 61], [42, 86, 97, 52], [33, 60, 76], [19, 6, 60, 76], [22, 43, 1], []], ![[22, 52, 21, 49, 78, 20], [88, 64, 82, 39, 89, 68], [60, 91, 4], [94, 4, 65, 34, 62, 72], [90, 75, 89], [79, 93, 32, 96, 88, 68]], ![[64, 65, 46, 89, 17, 12], [34, 0, 12, 25, 46, 69], [4, 89, 92], [47, 16, 79, 11, 100, 27], [94, 9, 16], [81, 88, 12, 39, 101, 34]], ![[10, 55, 56, 1, 37, 52], [61, 30, 86, 43, 86, 99], [27, 16, 23], [92, 46, 85, 97, 55, 49], [56, 83, 14], [79, 46, 27, 103, 91, 1]]]
 h' := ![![[48, 60, 29, 45], [40, 33, 50, 75], [17, 75, 93, 42], [13, 106, 47, 41], [77, 60, 47, 41], [0, 0, 0, 1], [0, 1]], ![[18, 0, 62, 61], [1, 77, 104, 35], [37, 68, 58, 62], [83, 63, 47, 105], [79, 85, 104, 68], [70, 25, 80, 14], [48, 60, 29, 45]], ![[84, 46, 16, 1], [103, 25, 15, 39], [15, 32, 14, 65], [1, 46, 68, 29], [93, 46, 105, 5], [70, 21, 18, 103], [18, 0, 62, 61]], ![[0, 1], [13, 79, 45, 65], [102, 39, 49, 45], [32, 106, 52, 39], [84, 23, 65, 100], [40, 61, 9, 96], [84, 46, 16, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [41, 27, 55], []]
 b := ![[], [], [11, 15, 68, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 4
  hpos := by decide
  P := [50, 26, 8, 64, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3287032246, -715317621, -3329986286, -113048340, 1581489704]
  a := ![-16, 11, 7, -17, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1417747278, -775259647, -903157746, -1301720956, 1581489704]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 131079601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -8, 5, 7, 4]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-11, -8, 5, 7, 4]] 
 ![![107, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![76, 0, 1, 0, 0], ![74, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![-11, -8, 5, 7, 4], ![-28, -23, 11, 17, 10], ![-22, -18, 6, 11, 7], ![-46, -38, 13, 22, 14], ![-38, -34, 8, 18, 11]]]
  hmulB := by decide  
  f := ![![![-115, 70, -7, -5, -11]], ![![-41, 25, -2, -2, -4]], ![![-82, 50, -6, -3, -8]], ![![-78, 48, -5, -4, -7]], ![![-44, 26, 0, -2, -5]]]
  g := ![![![-7, -8, 5, 7, 4], ![-15, -23, 11, 17, 10], ![-8, -18, 6, 11, 7], ![-16, -38, 13, 22, 14], ![-10, -34, 8, 18, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-115, 70, -7, -5, -11]] ![![-11, -8, 5, 7, 4]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -18, 2, 20, -14]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![9, -18, 2, 20, -14]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![80, 54, 30, 1, 0], ![28, 94, 105, 0, 1]] where
  M :=![![![9, -18, 2, 20, -14], ![162, -59, -150, 24, 54], ![-414, 198, 307, -150, -30], ![98, -138, 2, 159, -116], ![688, -168, -680, 4, 309]]]
  hmulB := by decide  
  f := ![![![125, -66, -2, -8, 14]], ![![-150, 97, -18, -12, -30]], ![![210, -90, -5, -18, 18]], ![![74, -24, -12, -17, 0]], ![![106, -20, -21, -30, -5]]]
  g := ![![![-11, 2, 8, 20, -14], ![-30, -59, -60, 24, 54], ![114, 102, 73, -150, -30], ![-86, 20, 68, 159, -116], ![-76, -270, -305, 4, 309]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [39, 70, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 68, 3], [70, 40, 106], [0, 1]]
 g := ![![[25, 68, 97], [33, 93], [87, 32, 83], [15, 50, 82], [75, 108], [1]], ![[0, 37, 9, 7], [32, 84], [58, 56, 96, 22], [23, 19, 41, 48], [73, 16], [74, 92, 73, 27]], ![[88, 82, 75, 84], [61, 28], [93, 101, 42, 105], [7, 108, 52, 21], [88, 61], [87, 92, 9, 82]]]
 h' := ![![[6, 68, 3], [108, 56, 36], [95, 39, 23], [69, 3, 44], [13, 31, 55], [70, 39, 76], [0, 1]], ![[70, 40, 106], [22, 30, 82], [17, 99, 56], [92, 7, 25], [69, 36, 4], [55, 102, 105], [6, 68, 3]], ![[0, 1], [28, 23, 100], [3, 80, 30], [65, 99, 40], [8, 42, 50], [72, 77, 37], [70, 40, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 70], []]
 b := ![[], [17, 65, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [39, 70, 33, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3388733987, 3328475922, 1844367902, -3085471630, 1064153820]
  a := ![-121, 61, 62, -122, -243]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1960116417, 641408118, -158969122, -3085471630, 1064153820]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 8, -6, -6, -3]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![13, 8, -6, -6, -3]] 
 ![![109, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![83, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![13, 8, -6, -6, -3], ![18, 27, -2, -18, -9], ![26, 10, -7, -2, -9], ![56, 28, -24, -15, -5], ![-20, 52, 34, -30, -13]]]
  hmulB := by decide  
  f := ![![![70261, -38012, 1860, -1588, 9425]], ![![37169, -20109, 984, -840, 4986]], ![![54509, -29490, 1443, -1232, 7312]], ![![12613, -6824, 334, -285, 1692]], ![![35134, -19008, 930, -794, 4713]]]
  g := ![![![3, 8, -6, -6, -3], ![-5, 27, -2, -18, -9], ![5, 10, -7, -2, -9], ![9, 28, -24, -15, -5], ![-42, 52, 34, -30, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-147413, 79742, -3898, 3336, -19771]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-147413, 79742, -3898, 3336, -19771]] 
 ![![109, 0, 0, 0, 0], ![99, 1, 0, 0, 0], ![64, 0, 1, 0, 0], ![75, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-147413, 79742, -3898, 3336, -19771], ![197148, -106651, 5214, -4460, 26443], ![-230412, 124640, -6093, 5214, -30903], ![211150, -114226, 5584, -4777, 28321], ![-74496, 40296, -1970, 1686, -9991]]]
  hmulB := by decide  
  f := ![![![-1245, 562, 988, -386, -199]], ![![-1107, 495, 884, -336, -186]], ![![-716, 336, 557, -240, -97]], ![![-949, 428, 754, -293, -152]], ![![94, -64, -50, 62, -25]]]
  g := ![![![-72697, 79742, -3898, 3336, -19771], ![97227, -106651, 5214, -4460, 26443], ![-113628, 124640, -6093, 5214, -30903], ![104133, -114226, 5584, -4777, 28321], ![-36736, 40296, -1970, 1686, -9991]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![9, -18, 2, 20, -14]] ![![13, 8, -6, -6, -3]]
  ![![1245, -562, -988, 386, 199]] where
 M := ![![![1245, -562, -988, 386, 199]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![1245, -562, -988, 386, 199]] ![![-147413, 79742, -3898, 3336, -19771]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![-109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5489, -2980, 146, -122, 739]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![5489, -2980, 146, -122, 739]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![63, 2, 7, 1, 0], ![40, 70, 59, 0, 1]] where
  M :=![![![5489, -2980, 146, -122, 739], ![-7366, 3963, -194, 170, -983], ![8586, -4654, 225, -194, 1153], ![-7884, 4248, -212, 177, -1055], ![2772, -1508, 70, -66, 371]]]
  hmulB := by decide  
  f := ![![![-19, 8, 12, -8, -1]], ![![14, -17, -4, 16, -15]], ![![74, -14, -73, -4, 31]], ![![-7, 4, 3, -5, 1]], ![![42, -16, -37, 6, 6]]]
  g := ![![![-145, -482, -377, -122, 739], ![188, 641, 501, 170, -983], ![-224, -752, -588, -194, 1153], ![205, 688, 538, 177, -1055], ![-70, -242, -189, -66, 371]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [63, 84, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 107, 33], [32, 5, 80], [0, 1]]
 g := ![![[82, 105, 32], [89, 52], [85, 9], [25, 104], [65, 80, 28], [1]], ![[91, 93, 56, 90], [110, 99], [18, 109], [8, 72], [100, 54, 33, 67], [78, 23, 26, 3]], ![[72, 15, 27, 48], [102, 4], [110, 51], [38, 31], [92, 44, 64, 33], [8, 49, 97, 110]]]
 h' := ![![[32, 107, 33], [84, 57, 91], [43, 14, 74], [58, 50, 3], [86, 23, 45], [50, 29, 64], [0, 1]], ![[32, 5, 80], [85, 93, 76], [110, 4, 41], [1, 67, 83], [36, 56, 80], [56, 9, 34], [32, 107, 33]], ![[0, 1], [31, 76, 59], [4, 95, 111], [70, 109, 27], [54, 34, 101], [59, 75, 15], [32, 5, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 109], []]
 b := ![[], [79, 61, 96], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [63, 84, 49, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2977865, 2592088, 1622266, -2405200, 920002]
  a := ![-12, 8, 6, -13, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![988935, -504404, -317004, -2405200, 920002]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 8, 12, -8, -1]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-19, 8, 12, -8, -1]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![44, 50, 1, 0, 0], ![26, 1, 0, 1, 0], ![0, 19, 0, 0, 1]] where
  M :=![![![-19, 8, 12, -8, -1], ![14, -17, -4, 16, -15], ![74, -14, -73, -4, 31], ![-140, 80, 102, -65, -11], ![160, -112, -74, 114, -61]]]
  hmulB := by decide  
  f := ![![![5489, -2980, 146, -122, 739]], ![![-7366, 3963, -194, 170, -983]], ![![-1046, 552, -27, 26, -137]], ![![1128, -613, 30, -25, 152]], ![![-1214, 653, -32, 28, -162]]]
  g := ![![![-3, -5, 12, -8, -1], ![-2, 4, -4, 16, -15], ![30, 27, -73, -4, 31], ![-26, -42, 102, -65, -11], ![4, 41, -74, 114, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [84, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 112], [0, 1]]
 g := ![![[16, 1], [8], [50], [100], [97, 97], [12, 1]], ![[28, 112], [8], [50], [100], [18, 16], [24, 112]]]
 h' := ![![[12, 112], [2, 1], [30, 102], [106, 84], [101, 103], [9, 60], [0, 1]], ![[0, 1], [14, 112], [11, 11], [97, 29], [94, 10], [51, 53], [12, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [7, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [84, 101, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-438544, 96336, 318055, -55993, -11813]
  a := ![51, -28, -25, 50, 103]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-114842, -137398, 318055, -55993, -11813]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![5489, -2980, 146, -122, 739]] ![![-19, 8, 12, -8, -1]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, -20, -1, -1, 7]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![33, -20, -1, -1, 7]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![45, 122, 81, 1, 0], ![120, 69, 84, 0, 1]] where
  M :=![![![33, -20, -1, -1, 7], ![-72, 29, 17, -3, -9], ![88, -52, -24, 17, 6], ![-42, 26, -19, -8, 9], ![-90, 26, 90, -20, -25]]]
  hmulB := by decide  
  f := ![![![1, -2, -5, -5, -2]], ![![10, 5, -15, -15, -8]], ![![20, 12, -12, -15, -7]], ![![23, 12, -24, -26, -13]], ![![20, 9, -21, -23, -11]]]
  g := ![![![-6, -3, -4, -1, 7], ![9, 8, 8, -3, -9], ![-11, -20, -15, 17, 6], ![-6, 3, -1, -8, 9], ![30, 33, 30, -20, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [121, 34, 123, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 50, 89], [93, 76, 38], [0, 1]]
 g := ![![[91, 63, 50], [112, 102, 74], [79, 125, 76], [115, 121, 68], [82, 46, 16], [1]], ![[121, 3, 122, 14], [65, 66, 104, 29], [75, 107, 29, 27], [25, 67, 114, 105], [0, 13, 105, 112], [15, 35, 33, 119]], ![[126, 91, 37, 72], [92, 84, 38, 32], [52, 50, 60, 35], [76, 94, 34, 8], [58, 99, 39, 32], [2, 49, 80, 8]]]
 h' := ![![[38, 50, 89], [37, 119, 80], [93, 73, 70], [55, 120, 40], [111, 64, 103], [6, 93, 4], [0, 1]], ![[93, 76, 38], [108, 71, 34], [36, 14, 6], [40, 76, 4], [81, 125, 62], [98, 19, 72], [38, 50, 89]], ![[0, 1], [92, 64, 13], [104, 40, 51], [121, 58, 83], [121, 65, 89], [78, 15, 51], [93, 76, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 31], []]
 b := ![[], [35, 49, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [121, 34, 123, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10476531, 5971578, 6910000, -5079610, 797679]
  a := ![-12, 9, 7, -10, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![963657, 4493261, 2766562, -5079610, 797679]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -2, -5, -5, -2]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![1, -2, -5, -5, -2]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![68, 110, 1, 0, 0], ![111, 45, 0, 1, 0], ![60, 58, 0, 0, 1]] where
  M :=![![![1, -2, -5, -5, -2], ![10, 5, -15, -15, -8], ![20, 12, -12, -15, -7], ![36, 32, -21, -32, -18], ![50, 30, -24, -26, -17]]]
  hmulB := by decide  
  f := ![![![33, -20, -1, -1, 7]], ![![-72, 29, 17, -3, -9]], ![![-44, 14, 14, -3, -4]], ![![3, -7, 5, -2, 3]], ![![-18, 4, 8, -2, -1]]]
  g := ![![![8, 7, -5, -5, -2], ![25, 22, -15, -15, -8], ![23, 19, -12, -15, -7], ![48, 38, -21, -32, -18], ![44, 38, -24, -26, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [98, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 126], [0, 1]]
 g := ![![[0, 35], [0, 87], [0, 99], [0, 25], [0, 79], [0, 1]], ![[0, 92], [0, 40], [0, 28], [0, 102], [0, 48], [0, 126]]]
 h' := ![![[0, 126], [0, 110], [0, 77], [0, 90], [0, 5], [0, 29], [0, 1]], ![[0, 1], [0, 17], [0, 50], [0, 37], [0, 122], [0, 98], [0, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [0, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [98, 0, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2502, -3972, -128, 2884, 3332]
  a := ![-16, 10, 4, -26, -12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4046, -2464, -128, 2884, 3332]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![33, -20, -1, -1, 7]] ![![1, -2, -5, -5, -2]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0, 0, 0]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]] where
  M :=![![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 5 2 7 [121, 86, 79, 85, 88, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 42, 83, 67, 98], [5, 33, 101, 51, 101], [77, 61, 99, 4, 120], [51, 125, 110, 9, 74], [0, 1]]
 g := ![![[122, 15, 26, 35, 11], [85, 9, 94, 78, 1], [96, 9, 95, 33], [62, 114, 112, 7], [68, 61, 43, 1], [], []], ![[102, 26, 9, 89, 61, 43, 91, 93], [117, 51, 41, 71, 59, 98, 87, 18], [20, 124, 25, 4], [54, 56, 98, 25], [118, 7], [81, 21, 25, 100], [38, 6, 92, 41]], ![[100, 7, 29, 105, 82, 118, 37, 80], [80, 61, 13, 82, 106, 107, 101, 7], [102, 33, 115, 101], [34, 60, 35, 60], [39, 128, 128, 101], [103, 84, 102, 41], [55, 33, 8, 114]], ![[55, 64, 71, 120, 21, 68, 25, 116], [51, 102, 82, 104, 96, 88, 19, 97], [103, 107, 38, 61], [18, 65, 19, 129], [111, 17, 120, 84], [24, 88, 25, 62], [127, 125, 6, 121]], ![[88, 127, 122, 52, 35, 19, 36, 28], [97, 42, 38, 42, 7, 103, 111, 53], [8, 76, 79, 112], [65, 93, 12, 64], [125, 15, 64, 21], [99, 117, 46, 53], [64, 1, 83, 105]]]
 h' := ![![[41, 42, 83, 67, 98], [64, 128, 129, 124, 50], [76, 56, 77, 83, 1], [66, 100, 105, 117, 66], [25, 2, 30, 123, 20], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[5, 33, 101, 51, 101], [129, 28, 45, 36, 26], [80, 16, 97, 49, 37], [50, 115, 7, 127, 2], [54, 125, 42, 125, 5], [70, 42, 38, 20], [96, 105, 77, 81, 10], [41, 42, 83, 67, 98]], ![[77, 61, 99, 4, 120], [126, 70, 59, 18, 98], [25, 66, 62, 121, 27], [70, 72, 48, 15, 25], [56, 129, 72, 21, 86], [94, 103, 118, 86, 25], [51, 122, 105, 84, 33], [5, 33, 101, 51, 101]], ![[51, 125, 110, 9, 74], [19, 30, 107, 99, 7], [15, 76, 15, 49, 88], [65, 127, 72, 76, 89], [127, 52, 33, 51, 28], [14, 56, 62, 89, 79], [125, 115, 78, 54, 18], [77, 61, 99, 4, 120]], ![[0, 1], [50, 6, 53, 116, 81], [83, 48, 11, 91, 109], [38, 110, 30, 58, 80], [82, 85, 85, 73, 123], [50, 61, 44, 67, 26], [97, 51, 1, 43, 70], [51, 125, 110, 9, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84, 42, 37, 112], [], [], []]
 b := ![[], [94, 34, 46, 78, 55], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 5
  hpos := by decide
  P := [121, 86, 79, 85, 88, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![48323274236, -1587462847, -57008616942, -14117971263, 36486563173]
  a := ![1, 9, 7, 2, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![368879956, -12118037, -435180282, -107770773, 278523383]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-117, 12, 44, -36, 25]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-117, 12, 44, -36, 25]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![83, 132, 73, 15, 1]] where
  M :=![![![-117, 12, 44, -36, 25], ![-242, -63, 180, 52, -97], ![722, -334, -631, 180, 149], ![-672, 364, 330, -407, 119], ![-360, -216, 578, 374, -587]]]
  hmulB := by decide  
  f := ![![![-977, 528, -26, 22, -131]], ![![1306, -707, 34, -30, 175]], ![![-1526, 826, -41, 34, -205]], ![![1400, -756, 36, -33, 187]], ![![3, -2, -1, -1, 0]]]
  g := ![![![-16, -24, -13, -3, 25], ![57, 93, 53, 11, -97], ![-85, -146, -84, -15, 149], ![-77, -112, -61, -16, 119], ![353, 564, 317, 67, -587]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 4 2 7 [28, 122, 58, 51, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 132, 123, 12], [80, 97, 33, 99], [90, 44, 118, 26], [0, 1]]
 g := ![![[3, 93, 63, 121], [82, 1, 38], [118, 60, 136], [113, 70, 76, 39], [131, 127, 135], [1], []], ![[130, 106, 76, 98, 83, 75], [17, 83, 65], [7, 108, 37], [80, 101, 61, 30, 60, 131], [131, 36, 69], [109, 34, 76], [78, 129, 7]], ![[77, 56, 36, 51, 104, 50], [64, 67, 37], [6, 15, 77], [31, 14, 112, 117, 45, 50], [119, 84, 68], [97, 90, 135], [50, 20, 74]], ![[21, 13, 4, 22, 36, 31], [36, 72, 103], [110, 33, 19], [51, 80, 47, 128, 130, 127], [98, 51, 37], [99, 133, 99], [10, 19, 128]]]
 h' := ![![[53, 132, 123, 12], [15, 77, 28, 126], [16, 89, 106, 77], [124, 58, 98, 100], [130, 35, 28, 54], [109, 15, 79, 86], [0, 0, 1], [0, 1]], ![[80, 97, 33, 99], [87, 49, 86, 71], [17, 22, 6, 32], [58, 10, 26, 41], [31, 135, 96, 43], [0, 27, 40, 53], [77, 42, 3, 58], [53, 132, 123, 12]], ![[90, 44, 118, 26], [127, 11, 24, 30], [1, 121, 43, 96], [124, 9, 35, 25], [56, 105, 117, 107], [127, 76, 118, 94], [68, 92, 16, 51], [80, 97, 33, 99]], ![[0, 1], [92, 0, 136, 47], [135, 42, 119, 69], [8, 60, 115, 108], [108, 136, 33, 70], [89, 19, 37, 41], [11, 3, 117, 28], [90, 44, 118, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [122, 82, 115], []]
 b := ![[], [], [120, 18, 93, 122], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 4
  hpos := by decide
  P := [28, 122, 58, 51, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1118698, -297426, -792450, 203168, 29948]
  a := ![-3, 0, 1, -4, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9978, -31026, -21742, -1796, 29948]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 352275361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![977, -528, 26, -22, 131]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![977, -528, 26, -22, 131]] 
 ![![137, 0, 0, 0, 0], ![108, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![61, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![977, -528, 26, -22, 131], ![-1306, 707, -34, 30, -175], ![1526, -826, 41, -34, 205], ![-1400, 756, -36, 33, -187], ![492, -268, 14, -10, 67]]]
  hmulB := by decide  
  f := ![![![117, -12, -44, 36, -25]], ![![94, -9, -36, 28, -19]], ![![-1, 2, 3, 0, -2]], ![![57, -8, -22, 19, -12]], ![![18, 0, -10, 2, 1]]]
  g := ![![![415, -528, 26, -22, 131], ![-556, 707, -34, 30, -175], ![649, -826, 41, -34, 205], ![-595, 756, -36, 33, -187], ![210, -268, 14, -10, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-117, 12, 44, -36, 25]] ![![977, -528, 26, -22, 131]]
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


def P139P0 : CertificateIrreducibleZModOfList' 139 5 2 7 [77, 42, 42, 12, 82, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 42, 20, 70, 44], [136, 120, 48, 106, 116], [88, 58, 87, 90, 15], [90, 57, 123, 12, 103], [0, 1]]
 g := ![![[25, 69, 31, 126, 42], [7, 10, 89, 32, 113], [98, 112, 106, 5], [124, 138, 98, 70, 54], [25, 40, 57, 1], [], []], ![[131, 90, 91, 81, 75, 61, 25, 49], [136, 23, 84, 3, 111, 79, 117, 52], [82, 7, 81, 1], [67, 131, 63, 18, 59, 37, 137, 83], [11, 96, 20, 25], [102, 106, 104, 16], [94, 11, 30, 129]], ![[85, 4, 102, 51, 110, 19, 62, 11], [52, 116, 98, 1, 48, 17, 24, 89], [71, 32, 110, 107], [130, 15, 103, 24, 101, 45, 102, 54], [27, 11, 110, 25], [132, 76, 129, 37], [84, 93, 118, 112]], ![[102, 39, 41, 122, 113, 66, 22, 26], [121, 127, 93, 71, 121, 43, 128, 119], [28, 18, 77, 117], [131, 49, 120, 34, 22, 46, 80, 109], [134, 39, 45, 30], [15, 57, 14, 64], [69, 138, 96, 86]], ![[48, 0, 99, 24, 20, 25, 108, 98], [104, 26, 105, 124, 63, 89, 63, 62], [11, 27, 84, 51], [96, 24, 42, 82, 10, 118, 58, 3], [47, 26, 29, 5], [10, 36, 124, 41], [87, 135, 33, 45]]]
 h' := ![![[21, 42, 20, 70, 44], [17, 52, 5, 49, 96], [2, 86, 83, 109, 35], [43, 36, 88, 91, 12], [21, 40, 109, 136, 38], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[136, 120, 48, 106, 116], [85, 72, 21, 22, 102], [18, 58, 25, 102, 76], [76, 97, 131, 12, 1], [17, 16, 110, 47, 21], [126, 125, 92, 71, 134], [14, 27, 54, 38, 4], [21, 42, 20, 70, 44]], ![[88, 58, 87, 90, 15], [98, 30, 10, 75, 109], [25, 68, 2, 49, 123], [40, 128, 49, 32, 78], [60, 99, 67, 104, 121], [38, 42, 90, 77, 5], [74, 128, 94, 35, 71], [136, 120, 48, 106, 116]], ![[90, 57, 123, 12, 103], [64, 131, 119, 122, 122], [36, 7, 22, 26, 103], [78, 53, 45, 72, 16], [4, 53, 91, 20, 89], [133, 64, 65, 48, 126], [68, 20, 88, 36, 131], [88, 58, 87, 90, 15]], ![[0, 1], [2, 132, 123, 10, 127], [28, 59, 7, 131, 80], [72, 103, 104, 71, 32], [26, 70, 40, 110, 9], [46, 47, 31, 82, 12], [11, 103, 41, 30, 72], [90, 57, 123, 12, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 19, 122, 61], [], [], []]
 b := ![[], [15, 47, 51, 101, 46], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 5
  hpos := by decide
  P := [77, 42, 42, 12, 82, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2411833822357, 907734753150, 2047276817661, -500085608688, -574725554163]
  a := ![12, -6, -3, 8, 29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17351322463, 6530465850, 14728610199, -3597738192, -4134716217]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, 8, 37, -1, -16]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-41, 8, 37, -1, -16]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![11, 118, 104, 1, 0], ![95, 48, 75, 0, 1]] where
  M :=![![![-41, 8, 37, -1, -16], ![196, -101, -149, 73, 14], ![-206, 150, 104, -149, 59], ![-302, 74, 293, -8, -134], ![1082, -482, -848, 330, 141]]]
  hmulB := by decide  
  f := ![![![-163, 74, -5, 5, -19]], ![![190, -127, 1, -5, 29]], ![![-242, 126, -12, 1, -34]], ![![-29, -8, -8, -3, -2]], ![![-165, 70, -9, 2, -20]]]
  g := ![![![10, 6, 9, -1, -16], ![-13, -63, -59, 73, 14], ![-28, 100, 75, -149, 59], ![84, 50, 75, -8, -134], ![-107, -310, -307, 330, 141]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [110, 51, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 21, 42], [21, 127, 107], [0, 1]]
 g := ![![[86, 138, 54], [112, 144], [84, 98, 85], [148, 103], [68, 148, 96], [97, 1], []], ![[131, 133, 99, 125], [83, 114], [126, 12, 49, 73], [106, 88], [15, 69, 37, 73], [122, 37], [32, 125]], ![[78, 6, 126, 31], [113, 73], [15, 98, 20, 76], [49, 49], [27, 16, 45, 4], [30, 143], [116, 125]]]
 h' := ![![[76, 21, 42], [51, 78, 59], [147, 31, 137], [116, 132, 95], [119, 6, 111], [58, 9, 120], [0, 0, 1], [0, 1]], ![[21, 127, 107], [66, 12, 41], [16, 17, 76], [74, 68, 27], [75, 105, 45], [133, 122, 122], [21, 28, 127], [76, 21, 42]], ![[0, 1], [51, 59, 49], [73, 101, 85], [147, 98, 27], [60, 38, 142], [47, 18, 56], [48, 121, 21], [21, 127, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 78], []]
 b := ![[], [111, 121, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [110, 51, 52, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1269726, -1483892, -629641, 1403693, -506198]
  a := ![9, -6, -5, 8, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![227637, -958538, -729187, 1403693, -506198]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, -4, -15, 1, 5]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![17, -4, -15, 1, 5]] 
 ![![149, 0, 0, 0, 0], ![44, 1, 0, 0, 0], ![53, 0, 1, 0, 0], ![75, 0, 0, 1, 0], ![123, 0, 0, 0, 1]] where
  M :=![![![17, -4, -15, 1, 5], ![-64, 37, 47, -29, -3], ![56, -44, -22, 47, -26], ![130, -34, -117, 10, 43], ![-374, 182, 286, -132, -37]]]
  hmulB := by decide  
  f := ![![![-49681, 26822, -1297, 1147, -6644]], ![![-14226, 7679, -371, 329, -1902]], ![![-18193, 9822, -475, 420, -2433]], ![![-24531, 13242, -640, 567, -3280]], ![![-41181, 22232, -1075, 951, -5507]]]
  g := ![![![2, -4, -15, 1, 5], ![-11, 37, 47, -29, -3], ![19, -44, -22, 47, -26], ![12, -34, -117, 10, 43], ![-61, 182, 286, -132, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![95473, -51638, 2522, -2164, 12802]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![95473, -51638, 2522, -2164, 12802]] 
 ![![149, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![111, 0, 1, 0, 0], ![59, 0, 0, 1, 0], ![127, 0, 0, 0, 1]] where
  M :=![![![95473, -51638, 2522, -2164, 12802], ![-127662, 69081, -3382, 2880, -17130], ![149230, -80710, 3943, -3382, 20010], ![-136722, 73994, -3622, 3083, -18348], ![48264, -26080, 1272, -1100, 6465]]]
  hmulB := by decide  
  f := ![![![6717, -4046, -4282, 3568, -642]], ![![2112, -1235, -1382, 1068, -146]], ![![4677, -2896, -2907, 2598, -564]], ![![3033, -1824, -1936, 1607, -286]], ![![5671, -3250, -3774, 2772, -293]]]
  g := ![![![4649, -51638, 2522, -2164, 12802], ![-6204, 69081, -3382, 2880, -17130], ![7265, -80710, 3943, -3382, 20010], ![-6645, 73994, -3622, 3083, -18348], ![2353, -26080, 1272, -1100, 6465]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-41, 8, 37, -1, -16]] ![![17, -4, -15, 1, 5]]
  ![![6717, -4046, -4282, 3568, -642]] where
 M := ![![![6717, -4046, -4282, 3568, -642]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![6717, -4046, -4282, 3568, -642]] ![![95473, -51638, 2522, -2164, 12802]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, 6, -1, 1, -1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-15, 6, -1, 1, -1]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![16, 97, 1, 0, 0], ![42, 133, 0, 1, 0], ![41, 30, 0, 0, 1]] where
  M :=![![![-15, 6, -1, 1, -1], ![10, -11, 5, -1, 3], ![-18, 6, -4, 5, -4], ![24, -16, -7, 0, 7], ![-38, 14, 22, -8, -5]]]
  hmulB := by decide  
  f := ![![![1, 4, -9, -11, -6]], ![![40, 13, -31, -29, -16]], ![![26, 9, -21, -20, -11]], ![![36, 13, -30, -29, -16]], ![![9, 4, -9, -9, -5]]]
  g := ![![![0, 0, -1, 1, -1], ![-1, -3, 5, -1, 3], ![0, -1, -4, 5, -4], ![-1, 3, -7, 0, 7], ![1, -6, 22, -8, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [31, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [127, 150], [0, 1]]
 g := ![![[30, 39], [70, 91], [80, 43], [94], [6, 2], [123], [1]], ![[0, 112], [0, 60], [105, 108], [94], [109, 149], [123], [1]]]
 h' := ![![[127, 150], [95, 48], [87, 98], [123, 88], [116, 83], [17, 46], [120, 127], [0, 1]], ![[0, 1], [0, 103], [0, 53], [125, 63], [87, 68], [121, 105], [92, 24], [127, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [24, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [31, 24, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3, -168, 46, 287, 189]
  a := ![4, 0, 0, 5, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-136, -321, 46, 287, 189]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-177, -78, 134, 158, 78]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-177, -78, 134, 158, 78]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![9, 51, 1, 0, 0], ![150, 21, 0, 1, 0], ![114, 136, 0, 0, 1]] where
  M :=![![![-177, -78, 134, 158, 78], ![-488, -391, 334, 426, 238], ![-566, -386, 227, 334, 188], ![-1098, -918, 466, 695, 414], ![-1096, -872, 372, 600, 361]]]
  hmulB := by decide  
  f := ![![![265, -226, -106, 238, -126]], ![![1392, -345, -1354, 26, 602]], ![![457, -117, -441, 14, 192]], ![![472, -285, -300, 253, -48]], ![![1486, -484, -1336, 196, 469]]]
  g := ![![![-225, -138, 134, 158, 78], ![-626, -389, 334, 426, 238], ![-491, -295, 227, 334, 188], ![-1038, -633, 466, 695, 414], ![-898, -540, 372, 600, 361]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [127, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 150], [0, 1]]
 g := ![![[40, 44], [100, 110], [113, 121], [85], [67, 16], [47], [1]], ![[0, 107], [0, 41], [3, 30], [85], [25, 135], [47], [1]]]
 h' := ![![[54, 150], [135, 73], [145, 84], [17, 11], [98, 113], [43, 147], [24, 54], [0, 1]], ![[0, 1], [0, 78], [0, 67], [7, 140], [9, 38], [129, 4], [71, 97], [54, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [31, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [127, 97, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-632499, 130172, 456643, -80891, -49391]
  a := ![-60, 45, 21, -60, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![86238, -97634, 456643, -80891, -49391]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, -26, -49, 17, 10]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![61, -26, -49, 17, 10]] 
 ![![151, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![115, 0, 1, 0, 0], ![55, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![61, -26, -49, 17, 10], ![-132, 87, 77, -81, 24], ![-56, -40, 106, 77, -105], ![492, -208, -397, 134, 84], ![-894, 518, 588, -446, 57]]]
  hmulB := by decide  
  f := ![![![-291, 836, 139, 53, -123]], ![![-6, 45, 11, 5, -5]], ![![-231, 640, 109, 44, -93]], ![![-105, 298, 58, 27, -40]], ![![-125, 322, 61, 29, -44]]]
  g := ![![![29, -26, -49, 17, 10], ![-44, 87, 77, -81, 24], ![-66, -40, 106, 77, -105], ![235, -208, -397, 134, 84], ![-341, 518, 588, -446, 57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-15, 6, -1, 1, -1]] ![![-177, -78, 134, 158, 78]]
  ![![291, -836, -139, -53, 123]] where
 M := ![![![291, -836, -139, -53, 123]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![291, -836, -139, -53, 123]] ![![61, -26, -49, 17, 10]]
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


lemma PB314I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB314I3 : PrimesBelowBoundCertificateInterval O 103 151 314 where
  m := 9
  g := ![2, 3, 2, 2, 1, 2, 1, 3, 3]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB314I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
    · exact ![I137N0, I137N1]
    · exact ![I139N0]
    · exact ![I149N0, I149N1, I149N2]
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
    · exact ![1295029, 109, 109]
    · exact ![1442897, 12769]
    · exact ![2048383, 16129]
    · exact ![38579489651]
    · exact ![352275361, 137]
    · exact ![51888844699]
    · exact ![3307949, 149, 149]
    · exact ![22801, 22801, 151]
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
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
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
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
  β := ![I107N1, I109N1, I109N2, I137N1, I149N1, I149N2, I151N2]
  Il := ![[I107N1], [I109N1, I109N2], [], [], [], [I137N1], [], [I149N1, I149N2], [I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
