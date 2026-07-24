
import IdealArithmetic.Examples.NF5_3_125000000_1.RI5_3_125000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![123, 98, 28, -34, -22]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![123, 98, 28, -34, -22]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![75, 100, 38, 1, 0], ![39, 55, 47, 0, 1]] where
  M :=![![![123, 98, 28, -34, -22], ![-440, -113, 196, 78, -68], ![-680, -530, -113, 230, 78], ![1000, 128, -628, -191, 264], ![2640, 1770, 128, -760, -191]]]
  hmulB := by decide  
  f := ![![![369, 6, -68, 22, -42]], ![![-840, -203, 12, -94, 44]], ![![440, -150, -203, -10, -94]], ![![-375, -242, -110, -77, -22]], ![![-107, -173, -111, -46, -35]]]
  g := ![![![33, 44, 22, -34, -22], ![-34, -39, 4, 78, -68], ![-196, -260, -117, 230, 78], ![47, 44, -54, -191, 264], ![627, 825, 355, -760, -191]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [19, 71, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 28, 29], [37, 78, 78], [0, 1]]
 g := ![![[72, 22, 19], [72, 90, 13], [85, 27], [83, 40, 36], [7, 69], [1]], ![[94, 77, 61, 34], [10, 87, 100, 53], [4, 12], [64, 68, 64, 35], [36, 27], [91, 40, 32, 100]], ![[34, 26, 8, 51], [43, 60, 49, 65], [9, 75], [41, 2, 3, 67], [93, 36], [96, 30, 13, 7]]]
 h' := ![![[23, 28, 29], [23, 9, 33], [25, 47, 86], [28, 70, 54], [14, 34, 101], [88, 36, 60], [0, 1]], ![[37, 78, 78], [85, 98, 53], [31, 23, 46], [0, 103, 36], [15, 17, 90], [59, 86, 53], [23, 28, 29]], ![[0, 1], [18, 0, 21], [92, 37, 82], [100, 41, 17], [30, 56, 23], [37, 92, 101], [37, 78, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 77], []]
 b := ![[], [15, 78, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [19, 71, 47, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54441, -91235, -78385, -39024, -8641]
  a := ![0, -2, -3, -3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![29994, 40060, 16922, -39024, -8641]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -12, -6, -4, -2]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-13, -12, -6, -4, -2]] 
 ![![107, 0, 0, 0, 0], ![64, 1, 0, 0, 0], ![92, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-13, -12, -6, -4, -2], ![-40, -43, -24, -10, -8], ![-80, -80, -43, -20, -10], ![-80, -100, -68, -33, -16], ![-160, -170, -100, -60, -33]]]
  hmulB := by decide  
  f := ![![![-48439, -4944, 5558, -3828, 4306]], ![![-28168, -2875, 3232, -2226, 2504]], ![![-42364, -4324, 4861, -3348, 3766]], ![![-8820, -900, 1012, -697, 784]], ![![-1114, -114, 128, -88, 99]]]
  g := ![![![13, -12, -6, -4, -2], ![48, -43, -24, -10, -8], ![88, -80, -43, -20, -10], ![124, -100, -68, -33, -16], ![198, -170, -100, -60, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![333, 94, -78, 48, -40]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![333, 94, -78, 48, -40]] 
 ![![107, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![80, 0, 0, 0, 1]] where
  M :=![![![333, 94, -78, 48, -40], ![-800, -225, 188, -116, 96], ![960, 270, -225, 140, -116], ![-760, -216, 176, -109, 92], ![920, 260, -216, 130, -109]]]
  hmulB := by decide  
  f := ![![![-681, -122, 38, -64, 48]], ![![-462, -85, 24, -44, 32]], ![![-292, -54, 15, -28, 20]], ![![-301, -58, 14, -29, 20]], ![![-520, -100, 24, -50, 35]]]
  g := ![![![-21, 94, -78, 48, -40], ![50, -225, 188, -116, 96], ![-60, 270, -225, 140, -116], ![49, -216, 176, -109, 92], ![-58, 260, -216, 130, -109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![123, 98, 28, -34, -22]] ![![-13, -12, -6, -4, -2]]
  ![![-1519, -790, 218, 410, -40]] where
 M := ![![![-1519, -790, 218, 410, -40]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-1519, -790, 218, 410, -40]] ![![333, 94, -78, 48, -40]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![-12947, -5136, 1712, -642, 1712]]]
 hmul := by decide  
 g := ![![![![-121, -48, 16, -6, 16]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![231, 69, -48, 34, -26]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![231, 69, -48, 34, -26]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![78, 20, 107, 1, 0], ![47, 78, 16, 0, 1]] where
  M :=![![![231, 69, -48, 34, -26], ![-520, -129, 138, -70, 68], ![680, 217, -129, 104, -70], ![-440, -80, 148, -59, 70], ![700, 274, -80, 113, -59]]]
  hmulB := by decide  
  f := ![![![59, 5, -6, 6, -6]], ![![-120, -19, 10, -6, 12]], ![![120, 17, -19, 4, -6]], ![![138, 17, -21, 7, -8]], ![![-43, -9, 2, -1, 5]]]
  g := ![![![-11, 13, -30, 34, -26], ![16, -37, 60, -70, 68], ![-38, 33, -93, 104, -70], ![8, -40, 49, -59, 70], ![-49, 24, -103, 113, -59]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [56, 3, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 101, 34], [86, 7, 75], [0, 1]]
 g := ![![[45, 25, 84], [29, 78], [24, 21, 66], [6, 8, 20], [103, 97], [1]], ![[45, 95, 15, 83], [62, 71], [51, 7, 16, 12], [88, 38, 31, 36], [80, 75], [67, 68, 36, 64]], ![[35, 41, 71, 3], [58, 35], [57, 65, 87, 75], [60, 16, 37, 31], [49, 45], [101, 45, 93, 45]]]
 h' := ![![[96, 101, 34], [108, 108, 56], [73, 32, 29], [100, 8, 34], [93, 45, 42], [53, 106, 73], [0, 1]], ![[86, 7, 75], [23, 68, 31], [15, 32, 92], [100, 97, 74], [34, 12, 80], [46, 1, 82], [96, 101, 34]], ![[0, 1], [93, 42, 22], [92, 45, 97], [72, 4, 1], [65, 52, 96], [53, 2, 63], [86, 7, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 108], []]
 b := ![[], [71, 30, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [56, 3, 36, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-72737824, -43578876, -2064976, -10212368, -4268928]
  a := ![3, -65, 2, -66, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8481344, 4528852, 10632672, -10212368, -4268928]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-699, -71, 80, -55, 62]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-699, -71, 80, -55, 62]] 
 ![![109, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![92, 0, 0, 1, 0], ![88, 0, 0, 0, 1]] where
  M :=![![![-699, -71, 80, -55, 62], ![1240, 125, -142, 98, -110], ![-1100, -111, 125, -87, 98], ![360, 38, -40, 27, -32], ![-320, -32, 38, -24, 27]]]
  hmulB := by decide  
  f := ![![![-111, -165, -118, -43, -40]], ![![-44, -61, -42, -16, -14]], ![![-14, -19, -13, -5, -4]], ![![-108, -154, -108, -41, -36]], ![![-112, -158, -110, -42, -37]]]
  g := ![![![9, -71, 80, -55, 62], ![-16, 125, -142, 98, -110], ![14, -111, 125, -87, 98], ![-4, 38, -40, 27, -32], ![4, -32, 38, -24, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -2, -2, -1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-1, -2, -2, -1, 0]] 
 ![![109, 0, 0, 0, 0], ![77, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![108, 0, 0, 1, 0], ![93, 0, 0, 0, 1]] where
  M :=![![![-1, -2, -2, -1, 0], ![0, -3, -4, -4, -2], ![-20, -14, -3, -3, -4], ![-40, -34, -12, 1, -2], ![-20, -38, -34, -11, 1]]]
  hmulB := by decide  
  f := ![![![-2549, -324, 334, -225, 238]], ![![-1757, -223, 230, -155, 164]], ![![-813, -104, 107, -72, 76]], ![![-2508, -318, 328, -221, 234]], ![![-2193, -280, 288, -194, 205]]]
  g := ![![![3, -2, -2, -1, 0], ![9, -3, -4, -4, -2], ![17, -14, -3, -3, -4], ![28, -34, -12, 1, -2], ![47, -38, -34, -11, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![231, 69, -48, 34, -26]] ![![-699, -71, 80, -55, 62]]
  ![![-2549, -324, 334, -225, 238]] where
 M := ![![![-2549, -324, 334, -225, 238]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-2549, -324, 334, -225, 238]] ![![-1, -2, -2, -1, 0]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36349, -10242, 8518, -5261, 4374]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-36349, -10242, 8518, -5261, 4374]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![16, 33, 98, 43, 1]] where
  M :=![![![-36349, -10242, 8518, -5261, 4374], ![87480, 24657, -20484, 12662, -10522], ![-105220, -29634, 24657, -15223, 12662], ![82880, 23362, -19392, 11995, -9962], ![-99620, -28028, 23362, -14411, 11995]]]
  hmulB := by decide  
  f := ![![![3, -4, -2, 3, 0]], ![![0, 1, -8, -4, 6]], ![![60, 32, 1, -11, -4]], ![![-40, 6, 36, 5, -14]], ![![36, 29, 12, -8, -7]]]
  g := ![![![-941, -1368, -3718, -1711, 4374], ![2264, 3291, 8944, 4116, -10522], ![-2724, -3960, -10763, -4953, 12662], ![2144, 3116, 8468, 3897, -9962], ![-2580, -3751, -10196, -4692, 11995]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 4 2 6 [75, 81, 78, 21, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 58, 102, 19], [9, 74, 75, 16], [80, 93, 49, 78], [0, 1]]
 g := ![![[9, 28, 109, 8], [63, 99, 8], [26, 66, 97], [82, 83, 112], [36, 24, 92, 1], []], ![[5, 7, 100, 92, 17, 5], [25, 68, 88], [43, 103, 91], [14, 15, 104], [89, 57, 91, 106, 47, 45], [70, 12, 18, 69, 101, 79]], ![[31, 28, 70, 106, 76, 14], [62, 14, 14], [45, 57, 1], [42, 34, 62], [19, 67, 100, 48, 19, 4], [60, 25, 54, 95, 60, 28]], ![[87, 32, 59, 103, 24, 55], [87, 107, 53], [81], [104, 85, 36], [74, 36, 68, 98, 66, 3], [0, 107, 61, 9, 57, 65]]]
 h' := ![![[3, 58, 102, 19], [47, 92, 85, 102], [34, 46, 106, 102], [96, 57, 87, 53], [12, 30, 100, 15], [0, 0, 0, 1], [0, 1]], ![[9, 74, 75, 16], [44, 63, 0, 97], [26, 60, 49, 38], [58, 27, 109, 59], [59, 73, 96, 45], [88, 81, 49, 65], [3, 58, 102, 19]], ![[80, 93, 49, 78], [68, 98, 105, 44], [56, 45, 98, 50], [70, 69, 39, 1], [100, 77, 7, 47], [71, 60, 60, 57], [9, 74, 75, 16]], ![[0, 1], [40, 86, 36, 96], [89, 75, 86, 36], [47, 73, 104], [29, 46, 23, 6], [110, 85, 4, 103], [80, 93, 49, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [92, 54, 62], []]
 b := ![[], [], [37, 29, 42, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 4
  hpos := by decide
  P := [75, 81, 78, 21, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5391996, 5031224, 2346419, 1026785, 862930]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-74468, -207482, -727617, -319285, 862930]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 163047361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -4, -2, 3, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![3, -4, -2, 3, 0]] 
 ![![113, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![69, 0, 0, 0, 1]] where
  M :=![![![3, -4, -2, 3, 0], ![0, 1, -8, -4, 6], ![60, 32, 1, -11, -4], ![-40, 6, 36, 5, -14], ![-140, -86, 6, 43, 5]]]
  hmulB := by decide  
  f := ![![![-36349, -10242, 8518, -5261, 4374]], ![![-7911, -2229, 1854, -1145, 952]], ![![-10903, -3072, 2555, -1578, 1312]], ![![-5700, -1606, 1336, -825, 686]], ![![-23077, -6502, 5408, -3340, 2777]]]
  g := ![![![1, -4, -2, 3, 0], ![-1, 1, -8, -4, 6], ![-3, 32, 1, -11, -4], ![-4, 6, 36, 5, -14], ![7, -86, 6, 43, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-36349, -10242, 8518, -5261, 4374]] ![![3, -4, -2, 3, 0]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-83, -7, 10, -6, 6]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-83, -7, 10, -6, 6]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![104, 56, 3, 1, 0], ![69, 76, 47, 0, 1]] where
  M :=![![![-83, -7, 10, -6, 6], ![120, -1, -14, 14, -12], ![-120, -19, -1, -8, 14], ![80, 24, -12, -15, -2], ![-20, 22, 24, -11, -15]]]
  hmulB := by decide  
  f := ![![![11, 3, -4, 2, -2]], ![![-40, -17, 6, -6, 4]], ![![40, 7, -17, 4, -6]], ![![-8, -5, -1, -1, 0]], ![![-3, -6, -5, -1, -1]]]
  g := ![![![1, -1, -2, -6, 6], ![-4, 1, 4, 14, -12], ![-2, -5, -5, -8, 14], ![14, 8, 1, -15, -2], ![17, 14, 6, -11, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [18, 32, 117, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [100, 90, 101], [37, 36, 26], [0, 1]]
 g := ![![[65, 86, 121], [8, 114, 62], [50, 20, 37], [21, 101, 16], [48, 106, 100], [1]], ![[2, 63, 91, 12], [2, 34, 123, 20], [56, 21, 95, 53], [91, 8, 89, 24], [13, 20, 43, 58], [14, 118, 29, 77]], ![[64, 41, 8, 13], [6, 64, 105, 99], [16, 119, 120, 68], [34, 93, 116, 124], [107, 1, 123, 82], [13, 30, 102, 50]]]
 h' := ![![[100, 90, 101], [110, 99, 11], [116, 81, 69], [3, 40, 75], [25, 55, 123], [109, 95, 10], [0, 1]], ![[37, 36, 26], [16, 32, 108], [44, 57, 124], [101, 45, 9], [96, 85, 77], [4, 75, 49], [100, 90, 101]], ![[0, 1], [66, 123, 8], [53, 116, 61], [84, 42, 43], [106, 114, 54], [0, 84, 68], [37, 36, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92, 41], []]
 b := ![[], [66, 67, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [18, 32, 117, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3439688, 4201743, 2859168, 1257955, 520972]
  a := ![1, 18, 4, 17, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1286100, -833367, -200003, 1257955, 520972]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 4, -6, 4, -4]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![47, 4, -6, 4, -4]] 
 ![![127, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![97, 0, 1, 0, 0], ![114, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![47, 4, -6, 4, -4], ![-80, -7, 8, -8, 8], ![80, 12, -7, 4, -8], ![-40, -8, 8, 1, 0], ![0, -16, -8, 8, 1]]]
  hmulB := by decide  
  f := ![![![2481, 692, -586, 356, -300]], ![![363, 101, -86, 52, -44]], ![![1951, 544, -461, 280, -236]], ![![2182, 608, -516, 313, -264]], ![![1479, 412, -350, 212, -179]]]
  g := ![![![3, 4, -6, 4, -4], ![-3, -7, 8, -8, 8], ![5, 12, -7, 4, -8], ![-6, -8, 8, 1, 0], ![1, -16, -8, 8, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -3, 2, 0, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![-13, -3, 2, 0, 0]] 
 ![![127, 0, 0, 0, 0], ![100, 1, 0, 0, 0], ![80, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![-13, -3, 2, 0, 0], ![0, -11, -6, 4, 0], ![0, -3, -11, -6, 4], ![40, 24, 0, -15, -6], ![-60, -16, 24, 3, -15]]]
  hmulB := by decide  
  f := ![![![-33339, -9381, 7800, -4820, 4008]], ![![-25620, -7209, 5994, -3704, 3080]], ![![-21760, -6123, 5091, -3146, 2616]], ![![-3078, -866, 720, -445, 370]], ![![-16994, -4782, 3976, -2457, 2043]]]
  g := ![![![1, -3, 2, 0, 0], ![12, -11, -6, 4, 0], ![8, -3, -11, -6, 4], ![-14, 24, 0, -15, -6], ![4, -16, 24, 3, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-83, -7, 10, -6, 6]] ![![47, 4, -6, 4, -4]]
  ![![-2301, -211, 276, -194, 202]] where
 M := ![![![-2301, -211, 276, -194, 202]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![-2301, -211, 276, -194, 202]] ![![-13, -3, 2, 0, 0]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![10033, 508, -1524, 1016, -762]]]
 hmul := by decide  
 g := ![![![![79, 4, -12, 8, -6]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 160, 34, -59, -24]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![211, 160, 34, -59, -24]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![84, 37, 75, 128, 1]] where
  M :=![![![211, 160, 34, -59, -24], ![-480, -43, 320, 92, -118], ![-1180, -788, -43, 379, 92], ![1160, -38, -948, -135, 438], ![4380, 2734, -38, -1167, -135]]]
  hmulB := by decide  
  f := ![![![-839, -82, 94, -65, 74]], ![![1480, 143, -164, 114, -130]], ![![-1300, -122, 143, -99, 114]], ![![400, 34, -40, 29, -34]], ![![-476, -49, 57, -38, 43]]]
  g := ![![![17, 8, 14, 23, -24], ![72, 33, 70, 116, -118], ![-68, -32, -53, -87, 92], ![-272, -124, -258, -429, 438], ![120, 59, 77, 123, -135]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 4 2 7 [5, 60, 109, 99, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 109, 15, 36], [74, 2, 45, 12], [107, 19, 71, 83], [0, 1]]
 g := ![![[56, 37, 114, 25], [112, 79, 34, 45], [30, 77, 13], [13, 113, 62], [90, 116, 107], [1], []], ![[14, 6, 126, 117, 51, 27], [99, 103, 103, 126, 78, 21], [17, 102, 7], [13, 85, 108], [12, 83, 117], [75, 36, 43], [86, 108, 117]], ![[47, 52, 1, 74, 44, 99], [4, 68, 102, 68, 73, 99], [123, 25, 89], [50, 41, 15], [50, 61, 112], [113, 7, 11], [58, 55, 13]], ![[123, 62, 54, 110, 74, 69], [58, 58, 130, 27, 25, 95], [1, 16, 109], [35, 43, 81], [93, 92, 12], [33, 36, 1], [53, 102, 77]]]
 h' := ![![[113, 109, 15, 36], [95, 20, 121, 126], [42, 29, 5, 69], [42, 17, 96, 119], [99, 122, 92, 113], [126, 71, 22, 32], [0, 0, 1], [0, 1]], ![[74, 2, 45, 12], [56, 48, 8, 112], [123, 7, 41, 48], [48, 1, 62, 111], [84, 68, 117, 97], [119, 130, 9, 95], [25, 70, 11, 82], [113, 109, 15, 36]], ![[107, 19, 71, 83], [16, 36, 64, 98], [73, 62, 50, 33], [65, 31, 100, 73], [61, 48, 100, 43], [124, 88, 5, 80], [77, 78, 121, 50], [74, 2, 45, 12]], ![[0, 1], [73, 27, 69, 57], [54, 33, 35, 112], [37, 82, 4, 90], [9, 24, 84, 9], [9, 104, 95, 55], [49, 114, 129, 130], [107, 19, 71, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [79, 97, 21], []]
 b := ![[], [], [23, 53, 19, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 4
  hpos := by decide
  P := [5, 60, 109, 99, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![186696, -4649410, -4792518, 4835635, 2696799]
  a := ![-1, 2, -4, 4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1727820, -797183, -1580553, -2598127, 2696799]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 294499921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-839, -82, 94, -65, 74]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-839, -82, 94, -65, 74]] 
 ![![131, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![113, 0, 1, 0, 0], ![51, 0, 0, 1, 0], ![109, 0, 0, 0, 1]] where
  M :=![![![-839, -82, 94, -65, 74], ![1480, 143, -164, 114, -130], ![-1300, -122, 143, -99, 114], ![400, 34, -40, 29, -34], ![-340, -24, 34, -23, 29]]]
  hmulB := by decide  
  f := ![![![211, 160, 34, -59, -24]], ![![6, 7, 4, -2, -2]], ![![173, 132, 29, -48, -20]], ![![91, 62, 6, -24, -6]], ![![209, 154, 28, -58, -21]]]
  g := ![![![-120, -82, 94, -65, 74], ![210, 143, -164, 114, -130], ![-184, -122, 143, -99, 114], ![53, 34, -40, 29, -34], ![-46, -24, 34, -23, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![211, 160, 34, -59, -24]] ![![-839, -82, 94, -65, 74]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 31, -10, 14, -8]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![107, 31, -10, 14, -8]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![78, 127, 97, 1, 0], ![106, 30, 34, 0, 1]] where
  M :=![![![107, 31, -10, 14, -8], ![-160, 1, 62, -12, 28], ![280, 119, 1, 48, -12], ![-40, 68, 88, 13, 34], ![340, 228, 68, 71, 13]]]
  hmulB := by decide  
  f := ![![![11, -1, -4, 2, 0]], ![![0, 7, -2, -8, 4]], ![![40, 23, 7, -4, -8]], ![![34, 22, 1, -9, -2]], ![![18, 6, -2, -1, -1]]]
  g := ![![![-1, -11, -8, 14, -8], ![-16, 5, 2, -12, 28], ![-16, -41, -31, 48, -12], ![-34, -19, -17, 13, 34], ![-48, -67, -53, 71, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [107, 30, 101, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 79, 75], [88, 57, 62], [0, 1]]
 g := ![![[117, 43, 103], [69, 15], [90, 78], [35, 134, 118], [44, 130], [36, 1], []], ![[86, 4, 77, 117], [51, 133], [50, 77], [130, 113], [133, 7], [107, 98], [82, 8]], ![[64, 113, 130, 92], [84, 98], [1, 11], [31, 69, 63, 55], [35, 30], [89, 76], [95, 8]]]
 h' := ![![[85, 79, 75], [45, 103, 68], [21, 103, 17], [91, 59, 107], [69, 12, 114], [121, 46, 33], [0, 0, 1], [0, 1]], ![[88, 57, 62], [53, 66, 93], [116, 57, 63], [64, 38, 112], [0, 130], [42, 102, 125], [95, 113, 57], [85, 79, 75]], ![[0, 1], [113, 105, 113], [123, 114, 57], [97, 40, 55], [90, 132, 23], [37, 126, 116], [45, 24, 79], [88, 57, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 126], []]
 b := ![[], [29, 34, 86], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [107, 30, 101, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-799093, 350200, 867896, -527880, -64368]
  a := ![0, -10, 4, -20, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![344515, 506000, 396064, -527880, -64368]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -1, -4, 2, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![11, -1, -4, 2, 0]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![70, 40, 1, 0, 0], ![77, 11, 0, 1, 0], ![52, 78, 0, 0, 1]] where
  M :=![![![11, -1, -4, 2, 0], ![0, 7, -2, -8, 4], ![40, 23, 7, -4, -8], ![-80, -28, 24, 15, -6], ![-60, -64, -28, 27, 15]]]
  hmulB := by decide  
  f := ![![![107, 31, -10, 14, -8]], ![![-160, 1, 62, -12, 28]], ![![10, 17, 13, 4, 4]], ![![47, 18, 0, 7, -2]], ![![-48, 14, 32, -1, 13]]]
  g := ![![![1, 1, -4, 2, 0], ![4, -1, -2, -8, 4], ![2, 3, 7, -4, -8], ![-19, -5, 24, 15, -6], ![-7, -3, -28, 27, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P1 : CertificateIrreducibleZModOfList' 137 2 2 7 [76, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 136], [0, 1]]
 g := ![![[92, 128], [1], [100], [70, 38], [34], [25], [1]], ![[0, 9], [1], [100], [17, 99], [34], [25], [1]]]
 h' := ![![[132, 136], [130, 26], [53, 136], [23, 127], [112, 77], [40, 87], [61, 132], [0, 1]], ![[0, 1], [0, 111], [58, 1], [73, 10], [1, 60], [16, 50], [86, 5], [132, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [1, 110]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N1 : CertifiedPrimeIdeal' SI137N1 137 where
  n := 2
  hpos := by decide
  P := [76, 5, 1]
  hirr := P137P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![470, 197, -2, 345, 394]
  a := ![13, 0, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-339, -250, -2, 345, 394]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N1 B_one_repr
lemma NI137N1 : Nat.card (O ⧸ I137N1) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![107, 31, -10, 14, -8]] ![![11, -1, -4, 2, 0]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-481, -360, -54, 148, 50]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-481, -360, -54, 148, 50]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![71, 104, 99, 53, 1]] where
  M :=![![![-481, -360, -54, 148, 50], ![1000, 65, -720, -158, 296], ![2960, 1916, 65, -868, -158], ![-2080, 532, 2276, 223, -1016], ![-10160, -5998, 532, 2784, 223]]]
  hmulB := by decide  
  f := ![![![-139, -156, -90, -44, -26]], ![![-520, -541, -312, -154, -88]], ![![-880, -944, -541, -268, -154]], ![![-1280, -1364, -788, -387, -224]], ![![-1591, -1694, -975, -481, -277]]]
  g := ![![![-29, -40, -36, -18, 50], ![-144, -221, -216, -114, 296], ![102, 132, 113, 54, -158], ![504, 764, 740, 389, -1016], ![-187, -210, -155, -65, 223]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 4 2 7 [57, 11, 108, 103, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [125, 31, 1, 101], [8, 14, 56, 82], [42, 93, 82, 95], [0, 1]]
 g := ![![[10, 102, 62, 25], [71, 126, 5, 79], [77], [105, 94, 80, 89], [124, 99, 45], [1], []], ![[98, 136, 96, 41, 126, 48], [128, 111, 83, 43, 11, 101], [31, 92, 91], [7, 26, 57, 86, 3, 22], [125, 135, 6], [27, 55, 34], [125, 61, 54]], ![[29, 58, 0, 17, 93, 93], [107, 126, 109, 52, 64, 134], [51, 99, 34], [126, 138, 4, 71, 104, 87], [54, 2, 136], [119, 96, 36], [14, 75, 52]], ![[78, 88, 64, 91, 132, 138], [6, 102, 110, 24, 66, 82], [96, 53, 113], [47, 111, 15, 77, 126, 94], [23, 85, 100], [14, 35, 116], [19, 69, 129]]]
 h' := ![![[125, 31, 1, 101], [123, 77, 83, 5], [123, 27, 30, 94], [131, 67, 63], [73, 85, 113, 28], [82, 128, 31, 36], [0, 0, 1], [0, 1]], ![[8, 14, 56, 82], [76, 5, 6, 81], [111, 120, 73, 138], [99, 59, 64, 62], [21, 103, 96, 6], [14, 134, 123, 59], [21, 118, 86, 112], [125, 31, 1, 101]], ![[42, 93, 82, 95], [79, 130, 106, 98], [23, 63, 28, 120], [17, 123, 44, 112], [102, 21, 14, 14], [20, 119, 122, 54], [100, 104, 100, 133], [8, 14, 56, 82]], ![[0, 1], [124, 66, 83, 94], [16, 68, 8, 65], [117, 29, 107, 104], [110, 69, 55, 91], [93, 36, 2, 129], [125, 56, 91, 33], [42, 93, 82, 95]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [61, 125, 31], []]
 b := ![[], [], [52, 53, 19, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 4
  hpos := by decide
  P := [57, 11, 108, 103, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-519868, 1206753, 1087286, -1981774, 467637]
  a := ![-1, -4, 2, -5, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-242605, -341205, -325243, -192565, 467637]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 373301041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 156, 90, 44, 26]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 156, 90, 44, 26]] 
 ![![139, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![81, 0, 1, 0, 0], ![37, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![139, 156, 90, 44, 26], ![520, 541, 312, 154, 88], ![880, 944, 541, 268, 154], ![1280, 1364, 788, 387, 224], ![2240, 2378, 1364, 676, 387]]]
  hmulB := by decide  
  f := ![![![481, 360, 54, -148, -50]], ![![107, 85, 18, -34, -14]], ![![259, 196, 31, -80, -28]], ![![143, 92, -2, -41, -6]], ![![125, 82, 2, -36, -7]]]
  g := ![![![-103, 156, 90, 44, 26], ![-357, 541, 312, 154, 88], ![-621, 944, 541, 268, 154], ![-901, 1364, 788, 387, 224], ![-1565, 2378, 1364, 676, 387]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-481, -360, -54, 148, 50]] ![![139, 156, 90, 44, 26]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![-139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 5 2 7 [97, 2, 136, 116, 82, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [117, 17, 32, 53, 112], [135, 84, 146, 116, 67], [1, 130, 69, 40, 83], [112, 66, 51, 89, 36], [0, 1]]
 g := ![![[114, 22, 144, 80, 17], [56, 88, 114, 49], [74, 49, 134, 45, 127], [36, 74, 29, 95], [5, 46, 52, 67, 1], [], []], ![[147, 50, 2, 62, 28, 79, 42, 69], [74, 59, 0, 113], [122, 56, 114, 68, 39, 50, 77, 95], [129, 90, 46, 30], [117, 78, 109, 5, 54, 9, 68, 69], [65, 52, 97, 132], [77, 22, 40, 28]], ![[69, 10, 40, 139, 135, 64, 97, 37], [135, 7, 84, 67], [105, 105, 1, 94, 64, 65, 105, 121], [98, 67, 56, 86], [80, 87, 69, 80, 136, 144, 64, 31], [116, 132, 115, 100], [61, 123, 129, 19]], ![[40, 101, 140, 136, 74, 57, 57, 55], [102, 139, 109, 9], [38, 56, 145, 95, 31, 136, 28, 111], [128, 17, 115, 24], [39, 38, 127, 85, 113, 102, 66, 146], [97, 25, 28, 85], [137, 89, 45, 35]], ![[106, 11, 85, 69, 89, 64, 137, 49], [12, 52, 14, 49], [82, 40, 147, 31, 59, 71, 146, 53], [142, 113, 148, 124], [80, 110, 70, 0, 85, 13, 38, 28], [26, 89, 80, 36], [35, 82, 115, 104]]]
 h' := ![![[117, 17, 32, 53, 112], [12, 64, 141, 137, 100], [123, 119, 16, 61, 7], [38, 54, 126, 18, 96], [111, 147, 144, 120, 63], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[135, 84, 146, 116, 67], [140, 98, 3, 112, 96], [100, 44, 115, 96, 115], [20, 80, 126, 89, 126], [49, 53, 12, 24, 46], [56, 39, 62, 142, 53], [111, 51, 86, 111, 70], [117, 17, 32, 53, 112]], ![[1, 130, 69, 40, 83], [59, 13, 14, 85, 68], [41, 19, 63, 114, 31], [11, 124, 111, 93, 115], [32, 53, 132, 51, 58], [126, 74, 131, 141, 107], [90, 48, 91, 143, 139], [135, 84, 146, 116, 67]], ![[112, 66, 51, 89, 36], [72, 96, 100, 44, 60], [70, 91, 99, 17, 3], [39, 129, 129, 60, 96], [45, 112, 1, 108, 60], [111, 35, 32, 47, 106], [122, 144, 121, 98, 95], [1, 130, 69, 40, 83]], ![[0, 1], [147, 27, 40, 69, 123], [87, 25, 5, 10, 142], [125, 60, 104, 38, 14], [108, 82, 9, 144, 71], [35, 1, 73, 117, 31], [60, 55, 148, 95, 143], [112, 66, 51, 89, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82, 9, 146, 7], [], [], []]
 b := ![[], [39, 10, 72, 76, 121], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 5
  hpos := by decide
  P := [97, 2, 136, 116, 82, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![605165884, 1663835171, 932530655, -1566263713, 323478553]
  a := ![3, -4, 7, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4061516, 11166679, 6258595, -10511837, 2170997]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![929, 379, -270, -227, 90]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![929, 379, -270, -227, 90]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![12, 73, 148, 26, 1]] where
  M :=![![![929, 379, -270, -227, 90], ![1800, 1739, 758, -630, -454], ![-4540, -1445, 1739, 985, -630], ![-7200, -6050, -1824, 2369, 1212], ![12120, 2760, -6050, -2430, 2369]]]
  hmulB := by decide  
  f := ![![![319, 91, -80, 47, -40]], ![![-800, -241, 182, -120, 94]], ![![940, 255, -241, 135, -120]], ![![-800, -250, 164, -121, 88]], ![![428, 99, -128, 58, -61]]]
  g := ![![![-1, -41, -90, -17, 90], ![48, 231, 450, 74, -454], ![20, 295, 629, 115, -630], ![-144, -626, -1200, -193, 1212], ![-108, -1127, -2362, -424, 2369]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 4 2 7 [45, 102, 98, 80, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 77, 3, 42], [143, 142, 38, 97], [127, 82, 110, 12], [0, 1]]
 g := ![![[142, 45, 66, 62], [102, 108, 46, 95], [149, 115, 15, 36], [9, 52, 29], [33, 5, 17, 58], [1], []], ![[105, 76, 67, 143, 134, 19], [103, 93, 1, 42, 113, 47], [42, 149, 58, 18, 138, 32], [142, 7, 31], [16, 44, 147, 55, 8, 45], [119, 96, 74], [15, 15, 103]], ![[122, 95, 18, 8, 52, 90], [85, 73, 61, 96, 18, 62], [54, 137, 93, 43, 149, 118], [2, 34, 44], [144, 12, 102, 118, 72, 123], [128, 108, 138], [129, 139, 47]], ![[17, 4, 112, 46, 147, 149], [73, 64, 51, 112, 51, 101], [132, 111, 27, 91, 115, 133], [45, 93, 50], [113, 80, 139, 5, 5, 92], [95, 19, 4], [52, 29, 144]]]
 h' := ![![[103, 77, 3, 42], [91, 84, 122, 106], [90, 92, 105, 104], [69, 133, 128, 6], [25, 95, 141, 123], [106, 49, 53, 71], [0, 0, 1], [0, 1]], ![[143, 142, 38, 97], [43, 4, 7, 74], [113, 25, 81, 98], [124, 122, 127, 127], [126, 67, 108, 22], [48, 92, 111, 120], [119, 67, 120, 15], [103, 77, 3, 42]], ![[127, 82, 110, 12], [51, 128, 79, 117], [78, 24, 99, 75], [8, 120, 67, 3], [20, 69, 137, 78], [138, 1, 87, 40], [148, 59, 134, 134], [143, 142, 38, 97]], ![[0, 1], [134, 86, 94, 5], [77, 10, 17, 25], [14, 78, 131, 15], [23, 71, 67, 79], [143, 9, 51, 71], [48, 25, 47, 2], [127, 82, 110, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [57, 127, 54], []]
 b := ![[], [], [94, 59, 125, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 4
  hpos := by decide
  P := [45, 102, 98, 80, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![452126, 428179, 472924, 3587326, 3155651]
  a := ![1, 0, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-247786, -1522744, -3089824, -519600, 3155651]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 519885601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-319, -91, 80, -47, 40]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-319, -91, 80, -47, 40]] 
 ![![151, 0, 0, 0, 0], ![99, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![123, 0, 0, 0, 1]] where
  M :=![![![-319, -91, 80, -47, 40], ![800, 241, -182, 120, -94], ![-940, -255, 241, -135, 120], ![800, 250, -164, 121, -88], ![-880, -210, 250, -120, 121]]]
  hmulB := by decide  
  f := ![![![-929, -379, 270, 227, -90]], ![![-621, -260, 172, 153, -56]], ![![-13, -8, 1, 4, 0]], ![![-303, -103, 114, 70, -42]], ![![-837, -327, 260, 201, -89]]]
  g := ![![![39, -91, 80, -47, 40], ![-113, 241, -182, 120, -94], ![103, -255, 241, -135, 120], ![-125, 250, -164, 121, -88], ![67, -210, 250, -120, 121]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![929, 379, -270, -227, 90]] ![![-319, -91, 80, -47, 40]]
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


lemma PB547I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB547I3 : PrimesBelowBoundCertificateInterval O 103 151 547 where
  m := 9
  g := ![3, 3, 2, 3, 2, 2, 2, 1, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB547I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
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
    · exact ![1225043, 107, 107]
    · exact ![1295029, 109, 109]
    · exact ![163047361, 113]
    · exact ![2048383, 127, 127]
    · exact ![294499921, 131]
    · exact ![2571353, 18769]
    · exact ![373301041, 139]
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
      exact NI107N2
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
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
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
  β := ![I107N1, I107N2, I109N1, I109N2, I113N1, I127N1, I127N2, I131N1, I139N1, I151N1]
  Il := ![[I107N1, I107N2], [I109N1, I109N2], [I113N1], [I127N1, I127N2], [I131N1], [], [I139N1], [], [I151N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
