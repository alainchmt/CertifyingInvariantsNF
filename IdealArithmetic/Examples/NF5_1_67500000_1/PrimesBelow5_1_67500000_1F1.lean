
import IdealArithmetic.Examples.NF5_1_67500000_1.RI5_1_67500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![3, -16, -10, -2, 3]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0], ![3, -16, -10, -2, 3]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![11, 25, 19, 1, 0], ![18, 21, 19, 0, 1]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]], ![![3, -16, -10, -2, 3], ![16, 36, 20, 5, -7], ![-37, -64, -48, -18, 17], ![34, 58, 60, 17, -23], ![-87, -156, -144, -45, 42]]]
  hmulB := by decide  
  f := ![![![500, 736, 390, 106, -145], ![-493, -812, 0, 0, 0]], ![![-38, -39, -20, -6, 8], ![58, 58, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![157, 245, 131, 35, -48], ![-138, -258, 0, 0, 0]], ![![285, 417, 221, 60, -82], ![-285, -462, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-11, -25, -19, 29, 0], ![-18, -21, -19, 0, 29]], ![![-1, -1, -1, -2, 3], ![3, 2, 2, 5, -7], ![-5, 1, -1, -18, 17], ![9, 4, 6, 17, -23], ![-12, 3, -3, -45, 42]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [24, 14, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 20, 22], [1, 8, 7], [0, 1]]
 g := ![![[8, 5, 1], [17, 24], [11, 0, 28], [1]], ![[8, 6, 18, 23], [21, 24], [11, 18, 12, 13], [19, 2, 13, 5]], ![[20, 18, 21, 4], [18, 9], [5, 25, 0, 5], [2, 18, 14, 24]]]
 h' := ![![[11, 20, 22], [7, 18, 28], [26, 16, 16], [5, 15, 12], [0, 1]], ![[1, 8, 7], [23, 14, 11], [11, 27, 16], [5, 15, 20], [11, 20, 22]], ![[0, 1], [4, 26, 19], [1, 15, 26], [11, 28, 26], [1, 8, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 1], []]
 b := ![[], [17, 6, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [24, 14, 17, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-52954290, -130669607, -92173335, -103532500, -31708606]
  a := ![-5, -7, -3, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![57126142, 107707711, 85427851, -103532500, -31708606]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![9, 1, 0, 0, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0], ![9, 1, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]], ![![9, 1, 0, 0, 0], ![0, 9, 1, 0, 0], ![0, 1, 9, 2, 0], ![1, 1, 0, 10, 2], ![6, 15, 12, 9, 8]]]
  hmulB := by decide  
  f := ![![![383204, 196971, 1691744, 372012, -952], ![-1236299, 108170, -5463194, 13804, 0]], ![![135228, 69507, 597039, 131288, -336], ![-436275, 38193, -1928036, 4872, 0]], ![![90170, 46347, 398092, 87540, -224], ![-290908, 25463, -1285570, 3248, 0]], ![![157778, 81100, 696598, 153181, -392], ![-509026, 44554, -2249544, 5684, 0]], ![![303908, 156217, 1341728, 295044, -755], ![-980473, 85790, -4332878, 10948, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-9, 29, 0, 0, 0], ![-6, 0, 29, 0, 0], ![-12, 0, 0, 29, 0], ![-23, 0, 0, 0, 29]], ![![0, 1, 0, 0, 0], ![-3, 9, 1, 0, 0], ![-3, 1, 9, 2, 0], ![-6, 1, 0, 10, 2], ![-17, 15, 12, 9, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![11, 1, 0, 0, 0]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0], ![11, 1, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]], ![![11, 1, 0, 0, 0], ![0, 11, 1, 0, 0], ![0, 1, 11, 2, 0], ![1, 1, 0, 12, 2], ![6, 15, 12, 9, 10]]]
  hmulB := by decide  
  f := ![![![-13307, -5724, -65536, -12180, -40], ![35032, -3886, 173130, 580, 0]], ![![-6709, -2892, -33043, -6140, -20], ![17662, -1943, 87290, 290, 0]], ![![-13380, -5760, -65975, -12260, -40], ![35224, -3914, 174290, 580, 0]], ![![-9981, -4289, -49130, -9131, -30], ![26276, -2920, 129790, 435, 0]], ![![-3680, -1581, -18079, -3360, -11], ![9688, -1069, 47760, 160, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-11, 29, 0, 0, 0], ![-24, 0, 29, 0, 0], ![-22, 0, 0, 29, 0], ![-8, 0, 0, 0, 29]], ![![0, 1, 0, 0, 0], ![-5, 11, 1, 0, 0], ![-11, 1, 11, 2, 0], ![-10, 1, 0, 12, 2], ![-25, 15, 12, 9, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0, 0, 0], ![3, -16, -10, -2, 3]] ![![29, 0, 0, 0, 0], ![9, 1, 0, 0, 0]]
  ![![29, 0, 0, 0, 0], ![63, 123, 91, 14, -26]] where
 M := ![![![841, 0, 0, 0, 0], ![261, 29, 0, 0, 0]], ![![87, -464, -290, -58, 87], ![43, -108, -70, -13, 20]]]
 hmul := by decide  
 g := ![![![![-34, -123, -91, -14, 26], ![29, 0, 0, 0, 0]], ![![-54, -122, -91, -14, 26], ![29, 0, 0, 0, 0]]], ![![![3, -16, -10, -2, 3], ![0, 0, 0, 0, 0]], ![![-55, -114, -84, -13, 24], ![26, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![29, 0, 0, 0, 0], ![63, 123, 91, 14, -26]] ![![29, 0, 0, 0, 0], ![11, 1, 0, 0, 0]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![841, 0, 0, 0, 0], ![319, 29, 0, 0, 0]], ![![1827, 3567, 2639, 406, -754], ![551, 1131, 812, 116, -232]]]
 hmul := by decide  
 g := ![![![![29, 0, 0, 0, 0]], ![![11, 1, 0, 0, 0]]], ![![![63, 123, 91, 14, -26]], ![![19, 39, 28, 4, -8]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-22, 15, 21, 8, -7]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![-22, 15, 21, 8, -7]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![12, 20, 28, 21, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-22, 15, 21, 8, -7], ![-34, -98, -69, -13, 23], ![125, 229, 178, 56, -49], ![-102, -139, -145, -8, 69], ![282, 501, 441, 168, -85]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![16, -10, -14, -5, 5], ![22, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-12, -20, -28, -21, 31]], ![![2, 5, 7, 5, -7], ![-10, -18, -23, -16, 23], ![23, 39, 50, 35, -49], ![-30, -49, -67, -47, 69], ![42, 71, 91, 63, -85]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [6, 14, 13, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 13, 22], [27, 8, 5, 29], [16, 9, 4, 2], [0, 1]]
 g := ![![[2, 9, 18, 8], [22, 20, 27, 2], [17, 18, 0, 1], []], ![[10, 16, 22, 28, 30], [4, 1, 5, 21, 23], [25, 2, 21, 0, 12], [14, 28, 15]], ![[1, 25, 16, 27, 10, 26], [10, 24, 29, 5, 8, 22], [30, 28, 22, 1, 9, 23], [19, 6, 14, 19, 29, 23]], ![[27, 7, 27, 19, 21, 2], [14, 14, 25, 26, 25, 10], [11, 11, 2, 18, 12, 8], [17, 7, 14, 7, 17, 8]]]
 h' := ![![[19, 13, 22], [23, 25, 13, 15], [22, 26, 23, 8], [0, 0, 0, 1], [0, 1]], ![[27, 8, 5, 29], [27, 12, 5, 10], [9, 13, 2, 5], [17, 13, 28, 3], [19, 13, 22]], ![[16, 9, 4, 2], [17, 0, 25, 7], [29, 8, 20, 12], [8, 20, 18, 29], [27, 8, 5, 29]], ![[0, 1], [18, 25, 19, 30], [24, 15, 17, 6], [26, 29, 16, 29], [16, 9, 4, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [21, 3, 30], []]
 b := ![[], [], [8, 30, 8, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [6, 14, 13, 0, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21414453666, 16217064868, -20831134000, 91821649440, 64797571156]
  a := ![9, -56, 5, -57, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-25773719598, -41281753492, -59198810528, -40933140156, 64797571156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-10, 1, 0, 0, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![-10, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-10, 1, 0, 0, 0], ![0, -10, 1, 0, 0], ![0, 1, -10, 2, 0], ![1, 1, 0, -9, 2], ![6, 15, 12, 9, -11]]]
  hmulB := by decide  
  f := ![![![-24453, 5666, -39290, 7998, -28], ![-75764, -2170, -122016, 434, 0]], ![![-24983, 5783, -40128, 8166, -28], ![-77406, -2232, -124620, 434, 0]], ![![-24830, 5754, -39889, 8118, -28], ![-76932, -2200, -123876, 434, 0]], ![![71, -14, 85, -17, 0], ![220, 5, 264, 0, 0]], ![![-7890, 1836, -12675, 2580, -9], ![-24446, -675, -39360, 140, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-21, 31, 0, 0, 0], ![-24, 0, 31, 0, 0], ![-1, 0, 0, 31, 0], ![-10, 0, 0, 0, 31]], ![![-1, 1, 0, 0, 0], ![6, -10, 1, 0, 0], ![7, 1, -10, 2, 0], ![-1, 1, 0, -9, 2], ![-16, 15, 12, 9, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0, 0, 0], ![-22, 15, 21, 8, -7]] ![![31, 0, 0, 0, 0], ![-10, 1, 0, 0, 0]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![961, 0, 0, 0, 0], ![-310, 31, 0, 0, 0]], ![![-682, 465, 651, 248, -217], ![186, -248, -279, -93, 93]]]
 hmul := by decide  
 g := ![![![![31, 0, 0, 0, 0]], ![![-10, 1, 0, 0, 0]]], ![![![-22, 15, 21, 8, -7]], ![![6, -8, -9, -3, 3]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![58, 165, 135, 67, -58]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![58, 165, 135, 67, -58]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![29, 31, 1, 0, 0], ![13, 34, 0, 1, 0], ![19, 18, 0, 0, 1]] where
  M :=![![![58, 165, 135, 67, -58], ![-281, -610, -531, -185, 192], ![967, 1883, 1694, 481, -562], ![-1305, -2339, -2165, -502, 666], ![2511, 4401, 4107, 891, -1235]]]
  hmulB := by decide  
  f := ![![![-54, -123, -95, -131, -44]], ![![-395, -940, -651, -717, -218]], ![![-428, -1020, -716, -811, -250]], ![![-529, -1270, -888, -993, -304]], ![![-549, -1332, -938, -1058, -325]]]
  g := ![![![-98, -142, 135, 67, -58], ![375, 505, -531, -185, 192], ![-1182, -1537, 1694, 481, -562], ![1496, 1888, -2165, -502, 666], ![-2830, -3540, 4107, 891, -1235]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [32, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 36], [0, 1]]
 g := ![![[25, 9], [11], [32, 4], [11], [1]], ![[3, 28], [11], [14, 33], [11], [1]]]
 h' := ![![[14, 36], [14, 3], [12, 23], [6, 35], [5, 14], [0, 1]], ![[0, 1], [19, 34], [1, 14], [15, 2], [16, 23], [14, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [10, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [32, 23, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1062, 2436, 1754, 1984, 730]
  a := ![0, -4, 0, -5, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2418, -3582, 1754, 1984, 730]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![-1, 6, -3, -1, 1]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0], ![-1, 6, -3, -1, 1]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![3, 8, 1, 0, 0], ![25, 7, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]], ![![-1, 6, -3, -1, 1], ![5, 10, 18, 2, -3], ![-16, -20, -26, 11, 7], ![24, 32, 23, 10, 9], ![18, 72, 51, 63, 2]]]
  hmulB := by decide  
  f := ![![![13922763, 27905572, 50119263, 5560319, -8349906], ![-290709, -103058875, 8658, 0, 0]], ![![1546419, 3099503, 5566810, 617592, -927435], ![-32264, -11446875, 962, 0, 0]], ![![1421435, 2849000, 5116892, 567677, -852478], ![-29677, -10521725, 884, 0, 0]], ![![9699838, 19441509, 34917547, 3873814, -5817289], ![-202531, -71800000, 6032, 0, 0]], ![![12417599, 24888756, 44700963, 4959203, -7447213], ![-259297, -91917375, 7722, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-3, -8, 37, 0, 0], ![-25, -7, 0, 37, 0], ![-33, 0, 0, 0, 37]], ![![0, 1, -3, -1, 1], ![0, -4, 18, 2, -3], ![-12, 3, -26, 11, 7], ![-16, -6, 23, 10, 9], ![-48, -21, 51, 63, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [7, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 36], [0, 1]]
 g := ![![[35, 16], [36], [1, 25], [11], [1]], ![[0, 21], [36], [18, 12], [11], [1]]]
 h' := ![![[14, 36], [19, 33], [30, 31], [9, 32], [30, 14], [0, 1]], ![[0, 1], [0, 4], [20, 6], [13, 5], [4, 23], [14, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [34, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where
  n := 2
  hpos := by decide
  P := [7, 23, 1]
  hirr := P37P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![92048, 227041, 160055, 179343, 54754]
  a := ![9, 27, 5, 26, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-180502, -62400, 160055, 179343, 54754]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![35, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]], ![![-2, 1, 0, 0, 0], ![0, -2, 1, 0, 0], ![0, 1, -2, 2, 0], ![1, 1, 0, -1, 2], ![6, 15, 12, 9, -3]]]
  hmulB := by decide  
  f := ![![![55, -142, 233, -234, 0], ![999, 37, 4329, 0, 0]], ![![53, -141, 233, -234, 0], ![963, 37, 4329, 0, 0]], ![![51, -127, 207, -208, 0], ![927, 38, 3848, 0, 0]], ![![50, -130, 214, -215, 0], ![908, 38, 3978, 0, 0]], ![![-37, 197, -360, 361, -1], ![-675, -18, -6669, 19, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-35, 37, 0, 0, 0], ![-33, 0, 37, 0, 0], ![-34, 0, 0, 37, 0], ![0, 0, 0, 0, 37]], ![![-1, 1, 0, 0, 0], ![1, -2, 1, 0, 0], ![-1, 1, -2, 2, 0], ![0, 1, 0, -1, 2], ![-33, 15, 12, 9, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![58, 165, 135, 67, -58]] ![![37, 0, 0, 0, 0], ![-1, 6, -3, -1, 1]]
  ![![37, 0, 0, 0, 0], ![-93, -138, -92, -15, 27]] where
 M := ![![![2146, 6105, 4995, 2479, -2146], ![-829, -2734, -2131, -1227, 995]]]
 hmul := by decide  
 g := ![![![![-35, 27, 43, 52, -31], ![-37, 0, 0, 0, 0]], ![![53, 38, 17, -21, 5], ![30, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0, 0, 0], ![-93, -138, -92, -15, 27]] ![![37, 0, 0, 0, 0], ![-2, 1, 0, 0, 0]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![1369, 0, 0, 0, 0], ![-74, 37, 0, 0, 0]], ![![-3441, -5106, -3404, -555, 999], ![333, 481, 370, 74, -111]]]
 hmul := by decide  
 g := ![![![![37, 0, 0, 0, 0]], ![![-2, 1, 0, 0, 0]]], ![![![-93, -138, -92, -15, 27]], ![![9, 13, 10, 2, -3]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![152, 183, 67, -6, -15]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0], ![152, 183, 67, -6, -15]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![9, 37, 1, 25, 1]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![152, 183, 67, -6, -15], ![-96, -12, 3, -7, 3], ![11, -55, 24, 26, -17], ![10, -91, -131, -36, 33], ![48, 129, 183, 24, -63]]]
  hmulB := by decide  
  f := ![![![-151, -183, -67, 6, 15], ![41, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![-111, -133, -49, 5, 11], ![30, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-9, -37, -1, -25, 41]], ![![7, 18, 2, 9, -15], ![-3, -3, 0, -2, 3], ![4, 14, 1, 11, -17], ![-7, -32, -4, -21, 33], ![15, 60, 6, 39, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [23, 15, 31, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 25, 8, 2], [40, 26, 30, 27], [33, 30, 3, 12], [0, 1]]
 g := ![![[39, 23, 16, 25], [12, 40, 20], [17, 12, 20], [37, 1], []], ![[26, 33, 33, 13, 20, 18], [8, 33, 25], [20, 39, 20], [33, 22, 14, 24, 40, 2], [17, 16, 4]], ![[27, 10, 30, 3, 5, 27], [16, 7, 21], [39], [0, 0, 27, 37, 11, 11], [18, 16, 32]], ![[20, 25, 40, 13, 38, 14], [19, 20, 40], [38, 16, 39], [39, 32, 9, 12, 14, 30], [3, 29, 21]]]
 h' := ![![[5, 25, 8, 2], [27, 16, 28, 5], [37, 4, 4, 15], [10, 37, 27, 26], [0, 0, 1], [0, 1]], ![[40, 26, 30, 27], [29, 39, 29, 3], [34, 34, 1, 5], [24, 6, 22, 26], [3, 37, 10, 1], [5, 25, 8, 2]], ![[33, 30, 3, 12], [17, 29, 22, 40], [4, 23, 26, 12], [32, 30, 11], [38, 7, 25, 7], [40, 26, 30, 27]], ![[0, 1], [39, 39, 3, 34], [5, 21, 10, 9], [10, 9, 22, 30], [36, 38, 5, 33], [33, 30, 3, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [22, 32, 40], []]
 b := ![[], [], [13, 38, 19, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [23, 15, 31, 4, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1359976895734, 3354112513227, 2366714735129, 2655768810079, 812684369561]
  a := ![-11, -9, -5, -7, -21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-145223961715, -651590467330, 37903179648, -430764400706, 812684369561]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![-8, 1, 0, 0, 0], ![0, -8, 1, 0, 0], ![0, 1, -8, 2, 0], ![1, 1, 0, -7, 2], ![6, 15, 12, 9, -9]]]
  hmulB := by decide  
  f := ![![![505591, -201852, 1194933, -301678, 748], ![2589232, 53587, 6130730, -15334, 0]], ![![416349, -166220, 984035, -248434, 616], ![2132206, 44157, 5048699, -12628, 0]], ![![223047, -89047, 527167, -133091, 330], ![1142268, 23658, 2704688, -6765, 0]], ![![431242, -172166, 1019209, -257314, 638], ![2208476, 45719, 5229161, -13079, 0]], ![![49340, -19688, 116578, -29432, 73], ![252680, 5262, 598120, -1496, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-33, 41, 0, 0, 0], ![-18, 0, 41, 0, 0], ![-35, 0, 0, 41, 0], ![-4, 0, 0, 0, 41]], ![![-1, 1, 0, 0, 0], ![6, -8, 1, 0, 0], ![1, 1, -8, 2, 0], ![5, 1, 0, -7, 2], ![-24, 15, 12, 9, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0, 0, 0], ![152, 183, 67, -6, -15]] ![![41, 0, 0, 0, 0], ![-8, 1, 0, 0, 0]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![1681, 0, 0, 0, 0], ![-328, 41, 0, 0, 0]], ![![6232, 7503, 2747, -246, -615], ![-1312, -1476, -533, 41, 123]]]
 hmul := by decide  
 g := ![![![![41, 0, 0, 0, 0]], ![![-8, 1, 0, 0, 0]]], ![![![152, 183, 67, -6, -15]], ![![-32, -36, -13, 1, 3]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![-25, -3, -13, -3, 4]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0], ![-25, -3, -13, -3, 4]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![40, 20, 18, 1, 0], ![13, 25, 21, 0, 1]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]], ![![-25, -3, -13, -3, 4], ![21, 19, 45, 7, -10], ![-53, -77, -101, 7, 24], ![65, 97, 83, 7, 0], ![-27, 21, -9, 81, 10]]]
  hmulB := by decide  
  f := ![![![73, 124, 276, 40, -58], ![-129, -301, 0, 0, 0]], ![![4, -15, -32, -4, 6], ![43, 43, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![75, 109, 245, 36, -52], ![-91, -260, 0, 0, 0]], ![![18, 28, 62, 9, -13], ![-25, -66, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-40, -20, -18, 43, 0], ![-13, -25, -21, 0, 43]], ![![1, -1, -1, -3, 4], ![-3, 3, 3, 7, -10], ![-15, -19, -17, 7, 24], ![-5, -1, -1, 7, 0], ![-79, -43, -39, 81, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [34, 39, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 33, 6], [16, 9, 37], [0, 1]]
 g := ![![[3, 22, 11], [42, 29, 17], [30, 38], [4, 0, 1], []], ![[37, 11, 25, 15], [12, 32, 3, 41], [2, 25], [27, 39, 3, 13], [9, 36]], ![[30, 24, 16, 3], [14, 16, 35, 30], [15, 24], [1, 36, 11, 2], [21, 36]]]
 h' := ![![[27, 33, 6], [34, 22, 22], [18, 23, 24], [36, 16, 9], [0, 0, 1], [0, 1]], ![[16, 9, 37], [1, 34, 29], [41, 8, 10], [18, 26, 5], [36, 35, 9], [27, 33, 6]], ![[0, 1], [28, 30, 35], [15, 12, 9], [40, 1, 29], [15, 8, 33], [16, 9, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 39], []]
 b := ![[], [1, 31, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [34, 39, 0, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1963460, 408644, -2369732, 7000782, 5618548]
  a := ![6, -4, 4, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8256648, -6513272, -5729612, 7000782, 5618548]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![5, 13, -3, -1, 1]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0], ![5, 13, -3, -1, 1]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![33, 7, 1, 0, 0], ![35, 14, 0, 1, 0], ![10, 5, 0, 0, 1]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]], ![![5, 13, -3, -1, 1], ![5, 16, 25, 2, -3], ![-16, -13, -20, 25, 7], ![31, 39, 23, 23, 23], ![60, 177, 135, 126, 1]]]
  hmulB := by decide  
  f := ![![![60390908, 196137176, 329123495, 27047920, -40120464], ![41795355, -561050240, 33411, 0, 0]], ![![109269666, 354885272, 595507094, 48939767, -72592876], ![75623369, -1015149031, 60458, 0, 0]], ![![64067723, 208078711, 349161715, 28694694, -42563142], ![44340008, -595208992, 35446, 0, 0]], ![![84731563, 275190587, 461777246, 37949626, -56291081], ![58641016, -787182438, 46879, 0, 0]], ![![26750170, 86879020, 145785360, 11980885, -17771373], ![18513285, -248517385, 14800, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-33, -7, 43, 0, 0], ![-35, -14, 0, 43, 0], ![-10, -5, 0, 0, 43]], ![![3, 1, -3, -1, 1], ![-20, -4, 25, 2, -3], ![-7, -6, -20, 25, 7], ![-41, -13, 23, 23, 23], ![-205, -59, 135, 126, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [4, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 42], [0, 1]]
 g := ![![[26, 11], [30, 16], [35], [31, 23], [1]], ![[0, 32], [0, 27], [35], [4, 20], [1]]]
 h' := ![![[25, 42], [9, 22], [14, 39], [5, 11], [39, 25], [0, 1]], ![[0, 1], [0, 21], [0, 4], [22, 32], [19, 18], [25, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [22, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [4, 18, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![119292, 301654, 208071, 251215, 84695]
  a := ![19, 19, 10, 20, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-381082, -118496, 208071, 251215, 84695]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0, 0, 0], ![-25, -3, -13, -3, 4]] ![![43, 0, 0, 0, 0], ![5, 13, -3, -1, 1]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![1849, 0, 0, 0, 0], ![215, 559, -129, -43, 43]], ![![-1075, -129, -559, -129, 172], ![215, 387, 731, 129, -172]]]
 hmul := by decide  
 g := ![![![![43, 0, 0, 0, 0]], ![![5, 13, -3, -1, 1]]], ![![![-25, -3, -13, -3, 4]], ![![5, 9, 17, 3, -4]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![-8, 6, 53, 19, -18]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![-8, 6, 53, 19, -18]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![35, 39, 40, 1, 0], ![40, 33, 21, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![-8, 6, 53, 19, -18], ![-89, -206, -210, -37, 56], ![299, 504, 466, 47, -130], ![-322, -466, -423, -77, 84], ![423, 552, 561, -36, -180]]]
  hmulB := by decide  
  f := ![![![44907, 80330, 36741, -2831, -6074], ![45261, 19646, 0, 0, 0]], ![![-4078, -7305, -3369, 247, 562], ![-4089, -1786, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![30057, 53759, 24569, -1902, -4058], ![30309, 13148, 0, 0, 0]], ![![35358, 63235, 28887, -2242, -4769], ![35664, 15466, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-35, -39, -40, 47, 0], ![-40, -33, -21, 0, 47]], ![![1, -3, -7, 19, -18], ![-22, -13, 2, -37, 56], ![82, 63, 28, 47, -130], ![-21, -5, 19, -77, 84], ![189, 168, 123, -36, -180]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [9, 3, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 41, 43], [8, 5, 4], [0, 1]]
 g := ![![[27], [38, 14, 17], [10, 26, 34], [44, 0, 1], []], ![[13, 8, 26, 11], [25, 33, 40, 29], [40, 21, 12, 29], [24, 3, 10, 41], [1, 16]], ![[18, 13, 41, 36], [30, 18, 42, 25], [27, 32, 27, 17], [3, 23, 35, 3], [40, 16]]]
 h' := ![![[39, 41, 43], [34, 11], [4, 42, 8], [27, 9, 38], [0, 0, 1], [0, 1]], ![[8, 5, 4], [40, 28, 3], [14, 45, 13], [24, 29, 13], [8, 43, 5], [39, 41, 43]], ![[0, 1], [28, 8, 44], [40, 7, 26], [37, 9, 43], [33, 4, 41], [8, 5, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 32], []]
 b := ![[], [33, 26, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [9, 3, 0, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-98742, -135743, -151653, 33977, 86184]
  a := ![1, -3, 1, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-100751, -91594, -70651, 33977, 86184]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![17, 20, -3, -1, 1]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![17, 20, -3, -1, 1]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![5, 14, 1, 0, 0], ![12, 46, 0, 1, 0], ![44, 14, 0, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![17, 20, -3, -1, 1], ![5, 28, 32, 2, -3], ![-16, -6, -8, 39, 7], ![38, 46, 23, 42, 37], ![102, 282, 219, 189, 6]]]
  hmulB := by decide  
  f := ![![![85784, 1140214, 1530429, 102202, -149890], ![413177, -2208906, 705, 0, 0]], ![![-5705, -75705, -101597, -6784, 9950], ![-27401, 146640, -47, 0, 0]], ![![7418, 98736, 132546, 8852, -12982], ![35815, -191304, 61, 0, 0]], ![![16327, 217034, 291311, 19454, -28531], ![78651, -420456, 134, 0, 0]], ![![78604, 1044878, 1402480, 93658, -137359], ![378656, -2024232, 646, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-5, -14, 47, 0, 0], ![-12, -46, 0, 47, 0], ![-44, -14, 0, 0, 47]], ![![0, 2, -3, -1, 1], ![-1, -10, 32, 2, -3], ![-16, -38, -8, 39, 7], ![-47, -58, 23, 42, 37], ![-75, -246, 219, 189, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [31, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 46], [0, 1]]
 g := ![![[36, 16], [12, 32], [30, 8], [44, 3], [1]], ![[40, 31], [20, 15], [32, 39], [33, 44], [1]]]
 h' := ![![[12, 46], [4, 4], [10, 19], [46, 33], [16, 12], [0, 1]], ![[0, 1], [5, 43], [3, 28], [19, 14], [19, 35], [12, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [10, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [31, 35, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51667, 140021, 90217, 134184, 57058]
  a := ![13, 9, 10, 5, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-96174, -172219, 90217, 134184, 57058]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0, 0, 0], ![-8, 6, 53, 19, -18]] ![![47, 0, 0, 0, 0], ![17, 20, -3, -1, 1]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![2209, 0, 0, 0, 0], ![799, 940, -141, -47, 47]], ![![-376, 282, 2491, 893, -846], ![-2068, -4512, -3713, -517, 940]]]
 hmul := by decide  
 g := ![![![![47, 0, 0, 0, 0]], ![![17, 20, -3, -1, 1]]], ![![![-8, 6, 53, 19, -18]], ![![-44, -96, -79, -11, 20]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![518, -930, -766, -23, 164]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![518, -930, -766, -23, 164]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![34, 40, 2, 1, 0], ![48, 51, 15, 0, 1]] where
  M :=![![![518, -930, -766, -23, 164], ![961, 2189, 1038, -79, -210], ![-1339, -1230, -331, 107, 52], ![-271, -1486, -822, -4, 186], ![-48, 960, 648, 66, -167]]]
  hmulB := by decide  
  f := ![![![-4872, -12014, -8478, -9511, -2910]], ![![-26971, -66511, -46934, -52657, -16112]], ![![-149329, -368242, -259855, -291533, -89202]], ![![-36661, -90406, -63796, -71574, -21900]], ![![-89442, -220563, -155643, -174618, -53429]]]
  g := ![![![-124, -158, -60, -23, 164], ![259, 303, 82, -79, -210], ![-141, -154, -25, 107, 52], ![-171, -204, -68, -4, 186], ![108, 129, 57, 66, -167]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [32, 31, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 23, 24], [13, 29, 29], [0, 1]]
 g := ![![[34, 39, 13], [32, 29], [14, 33, 29], [46, 13], [1]], ![[20, 51, 46, 38], [2, 28], [36, 3, 13, 25], [34, 10], [24, 26, 23, 44]], ![[19, 46, 14, 46], [34, 15], [13, 52, 10, 29], [2, 42], [37, 35, 51, 9]]]
 h' := ![![[25, 23, 24], [29, 29, 15], [29, 40, 33], [29, 36, 33], [21, 22, 38], [0, 1]], ![[13, 29, 29], [36, 10, 18], [43, 47, 9], [49, 8, 19], [17, 50, 40], [25, 23, 24]], ![[0, 1], [18, 14, 20], [24, 19, 11], [25, 9, 1], [6, 34, 28], [13, 29, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 2], []]
 b := ![[], [32, 28, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [32, 31, 15, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![80415823, 198868931, 140068461, 158095232, 48680215]
  a := ![7, 7, 3, 6, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-143990045, -162408138, -17100476, 158095232, 48680215]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4872, -12014, -8478, -9511, -2910]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-4872, -12014, -8478, -9511, -2910]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![23, 49, 1, 0, 0], ![46, 4, 0, 1, 0], ![11, 3, 0, 0, 1]] where
  M :=![![![-4872, -12014, -8478, -9511, -2910], ![-26971, -66511, -46934, -52657, -16112], ![-149329, -368242, -259855, -291533, -89202], ![-399887, -986118, -695866, -780702, -238876], ![-891114, -2197476, -1550676, -1739724, -532315]]]
  hmulB := by decide  
  f := ![![![518, -930, -766, -23, 164]], ![![961, 2189, 1038, -79, -210]], ![![1088, 1597, 621, -81, -122]], ![![517, -670, -602, -26, 130]], ![![161, -51, -88, -8, 19]]]
  g := ![![![12446, 8494, -8478, -9511, -2910], ![68905, 47023, -46934, -52657, -16112], ![381492, 260347, -259855, -291533, -89202], ![1021603, 697184, -695866, -780702, -238876], ![2276551, 1553613, -1550676, -1739724, -532315]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [45, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 52], [0, 1]]
 g := ![![[16, 10], [24], [13, 1], [13], [22, 1]], ![[24, 43], [24], [35, 52], [13], [44, 52]]]
 h' := ![![[22, 52], [37, 13], [51, 36], [22, 1], [17, 15], [0, 1]], ![[0, 1], [5, 40], [48, 17], [44, 52], [29, 38], [22, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [6, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [45, 31, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20624, 51486, 35674, 42303, 14012]
  a := ![7, 8, 3, 9, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-54716, -35996, 35674, 42303, 14012]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![518, -930, -766, -23, 164]] ![![-4872, -12014, -8478, -9511, -2910]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![-13, 62, 74, 26, -25]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0], ![-13, 62, 74, 26, -25]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![45, 40, 24, 1, 0], ![19, 58, 22, 0, 1]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]], ![![-13, 62, 74, 26, -25], ![-124, -288, -238, -51, 77], ![411, 742, 636, 166, -179], ![-392, -592, -584, -61, 217], ![885, 1518, 1380, 405, -304]]]
  hmulB := by decide  
  f := ![![![157651, 126636, 45510, -16599, -11973], ![153282, 58941, 0, 0, 0]], ![![-5836, -4703, -1702, 609, 449], ![-5664, -2183, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![116287, 93392, 33550, -12250, -8825], ![113076, 43475, 0, 0, 0]], ![![45031, 36162, 12988, -4745, -3416], ![43790, 16835, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-45, -40, -24, 59, 0], ![-19, -58, -22, 0, 59]], ![![-12, 8, 0, 26, -25], ![12, -46, -12, -51, 77], ![-62, 76, 10, 166, -179], ![-30, -182, -66, -61, 217], ![-196, 50, -28, 405, -304]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [16, 19, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 21, 56], [47, 37, 3], [0, 1]]
 g := ![![[57, 50, 45], [44, 14, 41], [42, 26], [41, 42, 46], [1]], ![[25, 45, 7, 13], [25, 4, 11, 24], [41, 53], [43, 9, 25, 14], [58, 13, 27, 32]], ![[54, 56, 5, 3], [24, 56, 0, 53], [17, 15], [58, 42, 39, 7], [54, 20, 5, 27]]]
 h' := ![![[32, 21, 56], [4, 29, 24], [26, 58, 49], [52, 44, 12], [43, 40, 20], [0, 1]], ![[47, 37, 3], [52, 6, 34], [46, 9, 46], [17, 3, 17], [39, 13, 30], [32, 21, 56]], ![[0, 1], [20, 24, 1], [24, 51, 23], [1, 12, 30], [4, 6, 9], [47, 37, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 52], []]
 b := ![[], [58, 15, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [16, 19, 39, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-537626892, -1335957712, -937771958, -1070019538, -333533305]
  a := ![-9, -7, -17, -7, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![914413307, 1030673822, 543736096, -1070019538, -333533305]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![6, 14, -3, -1, 1]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0], ![6, 14, -3, -1, 1]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![22, 11, 1, 0, 0], ![56, 10, 0, 1, 0], ![10, 57, 0, 0, 1]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]], ![![6, 14, -3, -1, 1], ![5, 17, 26, 2, -3], ![-16, -12, -19, 27, 7], ![32, 40, 23, 25, 25], ![66, 192, 147, 135, 1]]]
  hmulB := by decide  
  f := ![![![3661789, 12693900, 20358504, 1593288, -2374772], ![2282120, -45931028, 5192, 0, 0]], ![![10977188, 38053333, 61029953, 4776291, -7119001], ![6841109, -137690306, 15576, 0, 0]], ![![3406370, 11808465, 18938426, 1482149, -2209123], ![2122899, -42727178, 4832, 0, 0]], ![![5336138, 18498168, 29667385, 2321814, -3460631], ![3325577, -66932892, 7568, 0, 0]], ![![11225720, 38914893, 62411736, 4884432, -7280183], ![6996028, -140807758, 15928, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-22, -11, 59, 0, 0], ![-56, -10, 0, 59, 0], ![-10, -57, 0, 0, 59]], ![![2, 0, -3, -1, 1], ![-11, -2, 26, 2, -3], ![-20, -8, -19, 27, 7], ![-36, -32, 23, 25, 25], ![-182, -48, 147, 135, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [5, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 58], [0, 1]]
 g := ![![[22, 12], [12, 28], [49], [], [8, 1]], ![[0, 47], [0, 31], [49], [], [16, 58]]]
 h' := ![![[8, 58], [58, 37], [50, 38], [0, 7], [19], [0, 1]], ![[0, 1], [0, 22], [0, 21], [56, 52], [19], [8, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [27, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [5, 51, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20157, 53948, 35492, 49076, 18666]
  a := ![-6, -4, -6, -5, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-62637, -32054, 35492, 49076, 18666]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0, 0, 0], ![-13, 62, 74, 26, -25]] ![![59, 0, 0, 0, 0], ![6, 14, -3, -1, 1]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![3481, 0, 0, 0, 0], ![354, 826, -177, -59, 59]], ![![-767, 3658, 4366, 1534, -1475], ![-1770, -3776, -2832, -590, 944]]]
 hmul := by decide  
 g := ![![![![59, 0, 0, 0, 0]], ![![6, 14, -3, -1, 1]]], ![![![-13, 62, 74, 26, -25]], ![![-30, -64, -48, -10, 16]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![-129, -191, -70, 3, 17]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![-129, -191, -70, 3, 17]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![57, 39, 21, 54, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![-129, -191, -70, 3, 17], ![105, 59, 13, 16, -11], ![-50, -31, -73, -57, 43], ![48, 203, 236, 84, -73], ![-189, -399, -426, -102, 154]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![39, 57, 21, 0, -5], ![18, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-57, -39, -21, -54, 61]], ![![-18, -14, -7, -15, 17], ![12, 8, 4, 10, -11], ![-41, -28, -16, -39, 43], ![69, 50, 29, 66, -73], ![-147, -105, -60, -138, 154]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [54, 0, 0, 11, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 0, 30, 17], [39, 38, 38, 54], [53, 22, 54, 51], [0, 1]]
 g := ![![[55, 8, 17, 60], [23, 19, 45], [39, 29, 16, 3], [11, 60, 50, 1], []], ![[44, 31, 51, 57, 20, 7], [31, 1, 5], [23, 25, 53, 37, 40, 59], [37, 57, 43, 48, 4, 51], [60, 56, 11, 36, 27, 33]], ![[2, 18, 40, 4, 33, 11], [32, 9, 39], [20, 3, 44, 49, 52, 38], [37, 2, 7, 46, 26, 30], [45, 45, 50, 47, 26, 23]], ![[25, 7, 12, 31, 25, 21], [31, 27, 52], [34, 35, 21, 22, 47, 32], [8, 42, 41, 5, 12, 17], [23, 23, 32, 11, 55, 37]]]
 h' := ![![[19, 0, 30, 17], [26, 37, 28, 11], [29, 32, 10, 44], [16, 54, 45, 8], [0, 0, 0, 1], [0, 1]], ![[39, 38, 38, 54], [20, 35, 49, 2], [48, 13, 13, 35], [51, 29, 0, 5], [20, 26, 54, 8], [19, 0, 30, 17]], ![[53, 22, 54, 51], [60, 55, 46, 46], [43, 7, 28, 10], [31, 8, 42, 45], [37, 42, 55, 29], [39, 38, 38, 54]], ![[0, 1], [50, 56, 60, 2], [57, 9, 10, 33], [25, 31, 35, 3], [15, 54, 13, 23], [53, 22, 54, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2, 26, 28], []]
 b := ![[], [], [52, 57, 52, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [54, 0, 0, 11, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1265275472738, 3120155085696, 2201776136212, 2470200057722, 755821165654]
  a := ![9, 14, 5, 19, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-685516901140, -432079842210, -224106038402, -628592506354, 755821165654]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![15, 1, 0, 0, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![15, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![15, 1, 0, 0, 0], ![0, 15, 1, 0, 0], ![0, 1, 15, 2, 0], ![1, 1, 0, 16, 2], ![6, 15, 12, 9, 14]]]
  hmulB := by decide  
  f := ![![![-1499206, -313970, -3631967, -482144, 296], ![6097377, -114253, 14777616, -9028, 0]], ![![-405200, -84858, -981574, -130304, 80], ![1647977, -30866, 3993792, -2440, 0]], ![![-486188, -101823, -1177793, -156352, 96], ![1977361, -37026, 4792160, -2928, 0]], ![![-810382, -169726, -1963231, -260619, 160], ![3295881, -61709, 7987920, -4880, 0]], ![![-835624, -175014, -2024376, -268736, 165], ![3398542, -63624, 8236704, -5032, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-15, 61, 0, 0, 0], ![-19, 0, 61, 0, 0], ![-33, 0, 0, 61, 0], ![-34, 0, 0, 0, 61]], ![![0, 1, 0, 0, 0], ![-4, 15, 1, 0, 0], ![-6, 1, 15, 2, 0], ![-10, 1, 0, 16, 2], ![-20, 15, 12, 9, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0, 0, 0], ![-129, -191, -70, 3, 17]] ![![61, 0, 0, 0, 0], ![15, 1, 0, 0, 0]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![3721, 0, 0, 0, 0], ![915, 61, 0, 0, 0]], ![![-7869, -11651, -4270, 183, 1037], ![-1830, -2806, -1037, 61, 244]]]
 hmul := by decide  
 g := ![![![![61, 0, 0, 0, 0]], ![![15, 1, 0, 0, 0]]], ![![![-129, -191, -70, 3, 17]], ![![-30, -46, -17, 1, 4]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)


lemma PB512I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB512I1 : PrimesBelowBoundCertificateInterval O 23 61 512 where
  m := 9
  g := ![3, 2, 3, 2, 2, 2, 2, 2, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB512I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![24389, 29, 29]
    · exact ![923521, 31]
    · exact ![1369, 1369, 37]
    · exact ![2825761, 41]
    · exact ![79507, 1849]
    · exact ![103823, 2209]
    · exact ![148877, 2809]
    · exact ![205379, 3481]
    · exact ![13845841, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I29N1, I29N2, I31N1, I37N2, I41N1, I61N1]
  Il := ![[I29N1, I29N2], [I31N1], [I37N2], [I41N1], [], [], [], [], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
