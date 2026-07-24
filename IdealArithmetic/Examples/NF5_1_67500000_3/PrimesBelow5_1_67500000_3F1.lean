
import IdealArithmetic.Examples.NF5_1_67500000_3.RI5_1_67500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [12, 20, 5, 12, 20, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 26, 17, 14, 26], [28, 20, 23, 7, 14], [12, 27, 17, 3, 8], [4, 13, 1, 5, 10], [0, 1]]
 g := ![![[15, 14, 19, 27, 16], [19, 27, 1, 22], [11, 9, 1], []], ![[20, 9, 2, 28, 16, 27, 25, 26], [11, 20, 21, 6], [5, 26, 22, 27, 11, 0, 13, 26], [8, 7, 27, 19, 15, 2, 19, 2]], ![[16, 21, 27, 17, 9, 16, 24, 15], [19, 9, 28, 22], [17, 11, 17, 15, 17, 12, 10, 10], [19, 16, 12, 2, 1, 15, 15, 18]], ![[10, 7, 25, 4, 19, 9, 16, 19], [17, 2, 9, 16], [21, 26, 17, 26, 12, 2, 15, 10], [28, 3, 4, 22, 12, 28, 22, 19]], ![[11, 8, 19, 22, 1, 12, 22, 15], [21, 6, 21, 5], [9, 27, 6, 2, 12, 3, 20, 21], [22, 26, 28, 27, 6, 1, 2, 14]]]
 h' := ![![[23, 26, 17, 14, 26], [28, 19, 1, 11, 25], [13, 20, 14, 6, 15], [0, 0, 0, 1], [0, 1]], ![[28, 20, 23, 7, 14], [20, 16, 11, 16, 28], [23, 28, 20, 22, 21], [7, 12, 10, 15, 1], [23, 26, 17, 14, 26]], ![[12, 27, 17, 3, 8], [17, 27, 1, 1, 17], [19, 25, 5, 4, 15], [3, 10, 21, 20, 26], [28, 20, 23, 7, 14]], ![[4, 13, 1, 5, 10], [22, 3, 27, 12, 21], [9, 22, 23, 6, 25], [0, 19, 19, 1, 20], [12, 27, 17, 3, 8]], ![[0, 1], [2, 22, 18, 18, 25], [15, 21, 25, 20, 11], [3, 17, 8, 21, 11], [4, 13, 1, 5, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 22, 10, 3], [], [], []]
 b := ![[], [9, 13, 0, 28, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [12, 20, 5, 12, 20, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3331149032, 1465498296, 413386764, 840725544, -1594714466]
  a := ![-17, 4, 8, -20, -34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![114867208, 50534424, 14254716, 28990536, -54990154]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 20511149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37600, -15390, -624, 2661, 10836]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![37600, -15390, -624, 2661, 10836]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![29, 1, 18, 7, 1]] where
  M :=![![![37600, -15390, -624, 2661, 10836], ![-57033, 23479, 960, -4101, -16542], ![86949, -35430, -1403, 6159, 25020], ![-37305, 15444, 666, -2624, -10782], ![28800, -11796, -474, 2058, 8323]]]
  hmulB := by decide  
  f := ![![![-290, -36, 102, -69, -90]], ![![333, -29, -78, 87, -144]], ![![1125, 312, -491, 249, 954]], ![![-2655, -270, 900, -638, -612]], ![![-136, 91, -12, -44, 337]]]
  g := ![![![-8924, -846, -6312, -2361, 10836], ![13635, 1291, 9636, 3603, -16542], ![-20601, -1950, -14573, -5451, 25020], ![8883, 846, 6282, 2350, -10782], ![-6857, -649, -4848, -1813, 8323]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [14, 13, 2, 12, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 29, 3, 21], [25, 30], [21, 2, 28, 10], [0, 1]]
 g := ![![[13, 10], [28, 8, 21, 18], [12, 18, 19, 1], []], ![[10, 29, 7, 2, 22, 22], [19, 6, 22, 23, 22, 3], [19, 23, 25, 20, 12, 30], [7, 27, 14, 28, 4, 23]], ![[15, 21], [10, 5, 7, 13], [0, 9, 1, 30], []], ![[6, 8, 14, 15, 13, 9], [30, 8, 19, 14, 25, 28], [11, 23, 15, 8, 11, 1], [3, 23, 15, 3, 27, 8]]]
 h' := ![![[4, 29, 3, 21], [11, 3, 17], [18, 26, 3, 24], [0, 0, 0, 1], [0, 1]], ![[25, 30], [7, 3, 27, 29], [18, 15, 0, 28], [28, 24, 3, 20], [4, 29, 3, 21]], ![[21, 2, 28, 10], [16, 15, 17], [25, 22, 5, 7], [1, 16, 13, 30], [25, 30]], ![[0, 1], [29, 10, 1, 2], [18, 30, 23, 3], [12, 22, 15, 11], [21, 2, 28, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [15], []]
 b := ![[], [], [9, 14, 21, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [14, 13, 2, 12, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16131668034, 38354800657, 53037229183, 48710005862, 521964332]
  a := ![-110, -4, 57, -173, -223]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1008665602, 1220414075, 1407802297, 1453427598, 521964332]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-290, -36, 102, -69, -90]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-290, -36, 102, -69, -90]] 
 ![![31, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-290, -36, 102, -69, -90], ![333, -29, -78, 87, -144], ![1125, 312, -491, 249, 954], ![-2655, -270, 900, -638, -612], ![2196, 168, -714, 534, 313]]]
  hmulB := by decide  
  f := ![![![37600, -15390, -624, 2661, 10836]], ![![26057, -10661, -432, 1842, 7506]], ![![37979, -15540, -629, 2688, 10944]], ![![31545, -12906, -522, 2233, 9090]], ![![26400, -10806, -438, 1869, 7609]]]
  g := ![![![43, -36, 102, -69, -90], ![127, -29, -78, 87, -144], ![-599, 312, -491, 249, 954], ![243, -270, 900, -638, -612], ![-63, 168, -714, 534, 313]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![37600, -15390, -624, 2661, 10836]] ![![-290, -36, 102, -69, -90]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-562046, -77249, 201717, -132911, -200352]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-562046, -77249, 201717, -132911, -200352]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![14, 30, 2, 1, 0], ![15, 23, 27, 0, 1]] where
  M :=![![![-562046, -77249, 201717, -132911, -200352], ![803379, -27066, -212131, 205053, -196410], ![1793619, 582605, -829992, 387307, 1819548], ![-5279373, -608081, 1829609, -1261332, -1469196], ![4491009, 412483, -1498317, 1084469, 881821]]]
  hmulB := by decide  
  f := ![![![-8797775714, 3607452857, 146236613, -627123689, -2541972006]], ![![13370460969, -5482443406, -222243777, 953074165, 3863173884]], ![![-20319820809, 8331969143, 337756032, -1448438943, -5871076662]], ![![6650288339, -2726893967, -110541079, 474046332, 1921490982]], ![![-10265473059, 4209269653, 170632681, -731744200, -2966038925]]]
  g := ![![![116324, 230221, 158839, -132911, -200352], ![23751, -44898, 126509, 205053, -196410], ![-835727, -1429357, -1371146, 387307, 1819548], ![930195, 1919551, 1189745, -1261332, -1469196], ![-646456, -1416310, -742606, 1084469, 881821]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [34, 2, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 16, 33], [25, 20, 4], [0, 1]]
 g := ![![[28, 27, 27], [35, 27], [14, 20, 4], [35, 1], []], ![[6, 23, 3, 33], [23, 1], [26, 26, 24, 16], [6, 30], [25, 16]], ![[28, 14, 27, 28], [13, 12], [30, 13, 36, 7], [5, 34], [17, 16]]]
 h' := ![![[10, 16, 33], [19, 25, 29], [5, 31, 8], [31, 7, 2], [0, 0, 1], [0, 1]], ![[25, 20, 4], [16, 2, 36], [13, 6, 36], [7, 8, 12], [27, 22, 20], [10, 16, 33]], ![[0, 1], [9, 10, 9], [9, 0, 30], [4, 22, 23], [10, 15, 16], [25, 20, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 6], []]
 b := ![[], [32, 9, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [34, 2, 2, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2721, -44233, -35909, 46157, 76947]
  a := ![-9, 1, 5, -13, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-48586, -86452, -59616, 46157, 76947]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]], ![![9, 1, 0, 0, 0], ![0, 9, 1, 0, 0], ![0, 1, 9, 2, 0], ![3, -1, -2, 12, 6], ![-6, -1, 2, -1, 6]]]
  hmulB := by decide  
  f := ![![![403744, 176263, 1341714, 295186, -1650], ![-1663224, 74851, -5521991, 10175, 0]], ![![110088, 48062, 365880, 80496, -450], ![-453508, 20424, -1505826, 2775, 0]], ![![330348, 144221, 1097794, 241522, -1350], ![-1360869, 61236, -4518107, 8325, 0]], ![![293628, 128189, 975784, 214679, -1200], ![-1209601, 54441, -4015961, 7400, 0]], ![![349184, 152450, 1160402, 255296, -1427], ![-1438464, 64710, -4775776, 8800, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-9, 37, 0, 0, 0], ![-30, 0, 37, 0, 0], ![-27, 0, 0, 37, 0], ![-32, 0, 0, 0, 37]], ![![0, 1, 0, 0, 0], ![-3, 9, 1, 0, 0], ![-9, 1, 9, 2, 0], ![-12, -1, -2, 12, 6], ![-6, -1, 2, -1, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![-13, 1, 0, 0, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0], ![-13, 1, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]], ![![-13, 1, 0, 0, 0], ![0, -13, 1, 0, 0], ![0, 1, -13, 2, 0], ![3, -1, -2, -10, 6], ![-6, -1, 2, -1, -16]]]
  hmulB := by decide  
  f := ![![![657059, -95002, 688344, -110334, 2520], ![1866502, 25419, 1963479, -15540, 0]], ![![431818, -62434, 452449, -72522, 1656], ![1226662, 16724, 1290597, -10212, 0]], ![![300348, -43424, 314617, -50430, 1152], ![853196, 11619, 897435, -7104, 0]], ![![319142, -46144, 334340, -53591, 1224], ![906584, 12346, 953694, -7548, 0]], ![![159835, -23109, 167435, -26838, 613], ![454042, 6184, 477603, -3780, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-24, 37, 0, 0, 0], ![-16, 0, 37, 0, 0], ![-18, 0, 0, 37, 0], ![-9, 0, 0, 0, 37]], ![![-1, 1, 0, 0, 0], ![8, -13, 1, 0, 0], ![4, 1, -13, 2, 0], ![5, -1, -2, -10, 6], ![4, -1, 2, -1, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-562046, -77249, 201717, -132911, -200352]] ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0]]
  ![![37, 0, 0, 0, 0], ![2, 7, 1, 10, 13]] where
 M := ![![![-20795702, -2858213, 7463529, -4917707, -7413024], ![-4255035, -722307, 1603322, -991146, -1999578]]]
 hmul := by decide  
 g := ![![![![-555668, -54926, 204906, -101021, -158895], ![-117993, 0, 0, 0, 0]], ![![-113473, -14174, 44097, -19148, -44111], ![-28267, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0, 0, 0], ![2, 7, 1, 10, 13]] ![![37, 0, 0, 0, 0], ![-13, 1, 0, 0, 0]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![1369, 0, 0, 0, 0], ![-481, 37, 0, 0, 0]], ![![74, 259, 37, 370, 481], ![-74, -111, 0, -111, -148]]]
 hmul := by decide  
 g := ![![![![37, 0, 0, 0, 0]], ![![-13, 1, 0, 0, 0]]], ![![![2, 7, 1, 10, 13]], ![![-2, -3, 0, -3, -4]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![-36, 20, 1, 8, -10]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0], ![-36, 20, 1, 8, -10]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![20, 39, 4, 32, 1]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![-36, 20, 1, 8, -10], ![84, -33, -16, 36, 78], ![-360, -46, 51, -2, -18], ![9, -128, -31, 39, -18], ![-55, 26, -11, -6, 69]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![4, -1, 0, 0, 1], ![4, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-20, -39, -4, -32, 41]], ![![4, 10, 1, 8, -10], ![-36, -75, -8, -60, 78], ![0, 16, 3, 14, -18], ![9, 14, 1, 15, -18], ![-35, -65, -7, -54, 69]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [9, 3, 4, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 4, 34, 11], [3, 5, 3, 26], [17, 31, 4, 4], [0, 1]]
 g := ![![[25, 22, 17, 16], [2, 9, 23], [17, 24, 16], [0, 1], []], ![[22, 14, 24, 36, 1, 29], [18, 12, 39], [4, 39, 1], [0, 30, 12, 20, 40, 17], [22, 10, 39]], ![[4, 16, 28, 26, 25, 27], [10], [23, 31, 33], [21, 16, 22, 9, 21, 34], [25, 33, 20]], ![[24, 6, 10, 34, 12, 9], [20, 30, 33], [22, 10, 2], [6, 19, 25, 33, 10, 36], [36, 32, 16]]]
 h' := ![![[21, 4, 34, 11], [21, 25, 38, 4], [11, 20, 2, 33], [0, 32, 38, 37], [0, 0, 1], [0, 1]], ![[3, 5, 3, 26], [22, 16, 23, 36], [15, 36, 33, 30], [25, 17, 1, 40], [38, 12, 32, 3], [21, 4, 34, 11]], ![[17, 31, 4, 4], [2, 31, 31, 20], [16, 16, 16], [10, 10, 24, 22], [30, 27, 33, 35], [3, 5, 3, 26]], ![[0, 1], [27, 10, 31, 22], [17, 10, 31, 19], [25, 23, 19, 24], [6, 2, 16, 3], [17, 31, 4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [28, 8], []]
 b := ![[], [], [12, 14, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [9, 3, 4, 0, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5610447740, 984554161, -743320785, 4509993155, 2728912950]
  a := ![62, -8, -30, 80, 123]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1194336860, -2571781729, -284365185, -2019883445, 2728912950]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![16, 1, 0, 0, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0], ![16, 1, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![16, 1, 0, 0, 0], ![0, 16, 1, 0, 0], ![0, 1, 16, 2, 0], ![3, -1, -2, 19, 6], ![-6, -1, 2, -1, 13]]]
  hmulB := by decide  
  f := ![![![-64383, -8432, -87171, -12136, -384], ![164492, -2501, 223860, 2624, 0]], ![![-32208, -4225, -43586, -6068, -192], ![82288, -1230, 111930, 1312, 0]], ![![-64345, -8425, -86836, -12094, -384], ![164394, -2459, 222999, 2624, 0]], ![![-48297, -6334, -65387, -9103, -288], ![123394, -1853, 167916, 1968, 0]], ![![-17293, -2274, -23388, -3256, -103], ![44182, -644, 60060, 704, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-16, 41, 0, 0, 0], ![-31, 0, 41, 0, 0], ![-31, 0, 0, 41, 0], ![-11, 0, 0, 0, 41]], ![![0, 1, 0, 0, 0], ![-7, 16, 1, 0, 0], ![-14, 1, 16, 2, 0], ![-14, -1, -2, 19, 6], ![-4, -1, 2, -1, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0, 0, 0], ![-36, 20, 1, 8, -10]] ![![41, 0, 0, 0, 0], ![16, 1, 0, 0, 0]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![1681, 0, 0, 0, 0], ![656, 41, 0, 0, 0]], ![![-1476, 820, 41, 328, -410], ![-492, 287, 0, 164, -82]]]
 hmul := by decide  
 g := ![![![![41, 0, 0, 0, 0]], ![![16, 1, 0, 0, 0]]], ![![![-36, 20, 1, 8, -10]], ![![-12, 7, 0, 4, -2]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![-14, -7, 0, 1, -4]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0], ![-14, -7, 0, 1, -4]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![38, 15, 6, 1, 0], ![13, 27, 23, 0, 1]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]], ![![-14, -7, 0, 1, -4], ![27, -11, -17, 7, 18], ![-87, -15, 11, -31, -12], ![-24, -11, 20, -33, -84], ![62, 21, -28, 11, 52]]]
  hmulB := by decide  
  f := ![![![7575, -3759, -5236, 2209, 5332], ![-2279, -13244, 0, 0, 0]], ![![-336, 176, 238, -101, -240], ![129, 602, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![6576, -3261, -4544, 1917, 4628], ![-1972, -11494, 0, 0, 0]], ![![2085, -1023, -1433, 604, 1463], ![-590, -3626, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-38, -15, -6, 43, 0], ![-13, -27, -23, 0, 43]], ![![0, 2, 2, 1, -4], ![-11, -14, -11, 7, 18], ![29, 18, 11, -31, -12], ![54, 64, 50, -33, -84], ![-24, -36, -30, 11, 52]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [23, 27, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 26, 28], [16, 16, 15], [0, 1]]
 g := ![![[15, 6, 9], [10, 7, 4], [10, 25], [26, 15, 1], []], ![[40, 33, 36, 12], [30, 10, 3, 12], [41, 16], [16, 26, 4, 30], [15, 10]], ![[16, 5, 19, 14], [12, 1, 32, 4], [35, 38], [28, 21, 26, 35], [28, 10]]]
 h' := ![![[42, 26, 28], [28, 0, 3], [1, 24, 41], [4, 28, 5], [0, 0, 1], [0, 1]], ![[16, 16, 15], [28, 3, 5], [20, 20, 38], [19, 2, 4], [0, 1, 16], [42, 26, 28]], ![[0, 1], [25, 40, 35], [0, 42, 7], [17, 13, 34], [42, 42, 26], [16, 16, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 10], []]
 b := ![[], [17, 33, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [23, 27, 28, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2419407, -406678, 331454, -467362, 740848]
  a := ![-30, 11, 15, -27, -59]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![132775, -311608, -323346, -467362, 740848]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0], ![-2, 11, 0, 0, 1]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0], ![-2, 11, 0, 0, 1]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![29, 31, 1, 0, 0], ![2, 29, 0, 1, 0], ![41, 11, 0, 0, 1]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]], ![![-2, 11, 0, 0, 1], ![-6, -3, 13, -1, -3], ![15, 11, -7, 26, 3], ![33, -9, -24, 31, 75], ![-71, -14, 25, -12, -44]]]
  hmulB := by decide  
  f := ![![![282525, 134529, -608794, 47696, 139967], ![24553, 2012916, -1462, 0, 0]], ![![2255522, 1074054, -4860290, 380794, 1117427], ![195865, 16070046, -11696, 0, 0]], ![![1810057, 861926, -3900383, 305586, 896735], ![157189, 12896214, -9384, 0, 0]], ![![1534306, 730623, -3306186, 259033, 760124], ![133222, 10931562, -7956, 0, 0]], ![![846377, 403037, -1823808, 142890, 419311], ![73488, 6030234, -4386, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-29, -31, 43, 0, 0], ![-2, -29, 0, 43, 0], ![-41, -11, 0, 0, 43]], ![![-1, 0, 0, 0, 1], ![-6, -8, 13, -1, -3], ![1, -13, -7, 26, 3], ![-56, -23, -24, 31, 75], ![24, 1, 25, -12, -44]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [33, 18, 1] where
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
 g := ![![[24, 13], [0, 4], [24], [0, 23], [1]], ![[5, 30], [14, 39], [24], [16, 20], [1]]]
 h' := ![![[25, 42], [0, 20], [25, 41], [0, 29], [10, 25], [0, 1]], ![[0, 1], [27, 23], [18, 2], [37, 14], [33, 18], [25, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [12, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [33, 18, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7827, -4120, 4408, -1492, -8160]
  a := ![18, -16, -8, -2, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4695, -180, 4408, -1492, -8160]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0, 0, 0], ![-14, -7, 0, 1, -4]] ![![43, 0, 0, 0, 0], ![-2, 11, 0, 0, 1]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![1849, 0, 0, 0, 0], ![-86, 473, 0, 0, 43]], ![![-602, -301, 0, 43, -172], ![387, -86, -215, 86, 258]]]
 hmul := by decide  
 g := ![![![![43, 0, 0, 0, 0]], ![![-2, 11, 0, 0, 1]]], ![![![-14, -7, 0, 1, -4]], ![![9, -2, -5, 2, 6]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![0, -6, 0, 1, -5]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![0, -6, 0, 1, -5]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![42, 26, 7, 1, 0], ![46, 44, 39, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![0, -6, 0, 1, -5], ![33, 4, -18, 8, 21], ![-102, -14, 30, -33, -15], ![-21, -14, 20, -16, -87], ![61, 23, -29, 11, 72]]]
  hmulB := by decide  
  f := ![![![-329, -34, 180, -81, -205], ![47, 470, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![-294, -32, 161, -72, -185], ![25, 420, 0, 0, 0]], ![![-322, -34, 177, -79, -202], ![33, 460, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-42, -26, -7, 47, 0], ![-46, -44, -39, 0, 47]], ![![4, 4, 4, 1, -5], ![-27, -24, -19, 8, 21], ![42, 32, 18, -33, -15], ![99, 90, 75, -16, -87], ![-79, -73, -62, 11, 72]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [32, 25, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 12, 32], [1, 34, 15], [0, 1]]
 g := ![![[40, 23, 34], [19, 39, 7], [36, 32, 37], [28, 37, 1], []], ![[39, 29, 30, 16], [41, 43, 6, 24], [24, 41, 35, 16], [17, 3, 17, 3], [22, 37]], ![[7, 6, 10, 29], [18, 41, 18, 39], [17, 31, 13, 46], [33, 42, 20, 45], [39, 37]]]
 h' := ![![[36, 12, 32], [3, 28, 9], [23, 12, 30], [44, 43, 32], [0, 0, 1], [0, 1]], ![[1, 34, 15], [41, 26, 27], [26, 35, 41], [44, 30, 20], [28, 23, 34], [36, 12, 32]], ![[0, 1], [41, 40, 11], [37, 0, 23], [39, 21, 42], [22, 24, 12], [1, 34, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 16], []]
 b := ![[], [29, 0, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [32, 25, 10, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1138923, 33661, -507495, -588949, -656132]
  a := ![16, 8, -1, 30, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1192699, 940769, 621368, -588949, -656132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![-19, 1, 0, 0, 1]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![-19, 1, 0, 0, 1]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![4, 33, 1, 0, 0], ![28, 22, 0, 1, 0], ![28, 1, 0, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![-19, 1, 0, 0, 1], ![-6, -20, 3, -1, -3], ![15, 1, -24, 6, 3], ![3, 1, -4, -16, 15], ![-11, -4, 5, -2, -31]]]
  hmulB := by decide  
  f := ![![![42801533, 160919936, -24114384, 8036532, 24381884], ![-13360126, 377491968, -37506, 0, 0]], ![![46873854, 176230579, -26408736, 8801164, 26701686], ![-14631288, 413408240, -41078, 0, 0]], ![![36532447, 137350164, -20582377, 6859430, 20810695], ![-11403260, 322201120, -32015, 0, 0]], ![![47439743, 178358105, -26727552, 8907415, 27024039], ![-14807901, 418399072, -41572, 0, 0]], ![![26496096, 99616783, -14927904, 4974980, 15093499], ![-8270542, 233684752, -23218, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-4, -33, 47, 0, 0], ![-28, -22, 0, 47, 0], ![-28, -1, 0, 0, 47]], ![![-1, 0, 0, 0, 1], ![2, -2, 3, -1, -3], ![-3, 14, -24, 6, 3], ![1, 10, -4, -16, 15], ![19, -2, 5, -2, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [41, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 46], [0, 1]]
 g := ![![[14, 36], [30, 27], [2, 17], [8, 6], [1]], ![[30, 11], [42, 20], [20, 30], [42, 41], [1]]]
 h' := ![![[37, 46], [39, 6], [12, 36], [1, 39], [6, 37], [0, 1]], ![[0, 1], [26, 41], [28, 11], [34, 8], [12, 10], [37, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [31, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [41, 10, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![120, -467, -141, 163, -11]
  a := ![0, -4, 0, -6, 1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-76, 13, -141, 163, -11]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0, 0, 0], ![0, -6, 0, 1, -5]] ![![47, 0, 0, 0, 0], ![-19, 1, 0, 0, 1]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![2209, 0, 0, 0, 0], ![-893, 47, 0, 0, 47]], ![![0, -282, 0, 47, -235], ![94, 141, -47, 0, 188]]]
 hmul := by decide  
 g := ![![![![47, 0, 0, 0, 0]], ![![-19, 1, 0, 0, 1]]], ![![![0, -6, 0, 1, -5]], ![![2, 3, -1, 0, 4]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0], ![-77, -4, 1, 20, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0], ![-77, -4, 1, 20, 1]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![29, 49, 1, 20, 1]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]], ![![-77, -4, 1, 20, 1], ![54, -97, -42, 61, 117], ![-519, -166, 15, -18, 15], ![-99, -202, -29, -50, -135], ![34, 41, -50, 7, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![2, 1, 0, 0, 0], ![1, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-29, -49, -1, -20, 53]], ![![-2, -1, 0, 0, 1], ![-63, -110, -3, -43, 117], ![-18, -17, 0, -6, 15], ![72, 121, 2, 50, -135], ![-59, -100, -3, -41, 109]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [13, 14, 23, 12, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 22, 30, 14], [47, 36, 39, 10], [19, 47, 37, 29], [0, 1]]
 g := ![![[6, 40, 23, 4], [36, 22, 6], [33, 8, 35, 46], [15, 41, 1], []], ![[46, 30, 12, 29, 8, 20], [43, 36, 4], [28, 28, 21, 40, 52, 22], [2, 31, 47], [48, 21, 32, 49, 29, 41]], ![[7, 12, 2, 0, 48, 6], [38, 16, 9], [29, 24, 15, 10, 3, 28], [27, 3, 28], [40, 21, 31, 36, 18, 46]], ![[51, 10, 39, 23, 7, 13], [7, 7, 10], [34, 1, 47, 29, 8, 7], [33, 34, 6], [7, 19, 7, 4, 16, 9]]]
 h' := ![![[28, 22, 30, 14], [34, 19, 22, 51], [48, 41, 18, 35], [17, 52, 22, 29], [0, 0, 0, 1], [0, 1]], ![[47, 36, 39, 10], [35, 16, 52, 50], [45, 5, 21, 2], [34, 33, 27, 43], [22, 25, 10, 43], [28, 22, 30, 14]], ![[19, 47, 37, 29], [32, 28, 39, 19], [46, 36, 3, 3], [3, 44, 9, 17], [6, 34, 43, 44], [47, 36, 39, 10]], ![[0, 1], [31, 43, 46, 39], [49, 24, 11, 13], [39, 30, 48, 17], [37, 47, 0, 18], [19, 47, 37, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [36, 48, 37], []]
 b := ![[], [], [16, 34, 23, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [13, 14, 23, 12, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![46774621, 64676810, -53086220, 43056890, 288643470]
  a := ![30, -11, -10, 25, 57]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-157054453, -265638740, -6447730, -108109670, 288643470]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] 
 ![![53, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]], ![![-11, 1, 0, 0, 0], ![0, -11, 1, 0, 0], ![0, 1, -11, 2, 0], ![3, -1, -2, -8, 6], ![-6, -1, 2, -1, -14]]]
  hmulB := by decide  
  f := ![![![-210946, 10168, 119069, -19928, -1254], ![-1013360, 7897, 572400, 11077, 0]], ![![-172574, 8305, 97570, -16332, -1026], ![-829025, 6466, 469050, 9063, 0]], ![![-153430, 7397, 86546, -14484, -912], ![-737060, 5725, 416050, 8056, 0]], ![![-115048, 5548, 64953, -10871, -684], ![-552677, 4325, 312250, 6042, 0]], ![![-199004, 9595, 112329, -18800, -1183], ![-955992, 7463, 540000, 10450, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-42, 53, 0, 0, 0], ![-38, 0, 53, 0, 0], ![-29, 0, 0, 53, 0], ![-50, 0, 0, 0, 53]], ![![-1, 1, 0, 0, 0], ![8, -11, 1, 0, 0], ![6, 1, -11, 2, 0], ![1, -1, -2, -8, 6], ![13, -1, 2, -1, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0, 0, 0], ![-77, -4, 1, 20, 1]] ![![53, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![2809, 0, 0, 0, 0], ![-583, 53, 0, 0, 0]], ![![-4081, -212, 53, 1060, 53], ![901, -53, -53, -159, 106]]]
 hmul := by decide  
 g := ![![![![53, 0, 0, 0, 0]], ![![-11, 1, 0, 0, 0]]], ![![![-77, -4, 1, 20, 1]], ![![17, -1, -1, -3, 2]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![50, -39, 0, 1, 26]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0], ![50, -39, 0, 1, 26]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![7, 30, 10, 1, 0], ![13, 45, 45, 0, 1]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]], ![![50, -39, 0, 1, 26], ![-153, 23, 11, -23, -72], ![363, -47, -75, 25, 78], ![-120, 81, 24, -65, -6], ![104, -37, -2, 13, -58]]]
  hmulB := by decide  
  f := ![![![109123, 32805, -13464, 26589, 47490], ![92217, 72216, 0, 0, 0]], ![![-4553, -1361, 561, -1108, -1982], ![-3835, -3009, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![10619, 3210, -1312, 2591, 4620], ![9006, 7038, 0, 0, 0]], ![![20546, 6210, -2538, 5013, 8939], ![17424, 13617, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-7, -30, -10, 59, 0], ![-13, -45, -45, 0, 59]], ![![-5, -21, -20, 1, 26], ![16, 67, 59, -23, -72], ![-14, -73, -65, 25, 78], ![7, 39, 16, -65, -6], ![13, 37, 42, 13, -58]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [50, 35, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 31, 17], [57, 27, 42], [0, 1]]
 g := ![![[3, 52, 26], [1, 32, 20], [15, 46], [51, 10, 35], [1]], ![[58, 7, 6, 45], [13, 25, 19, 17], [35, 36], [55, 5, 2, 4], [32, 1, 19, 16]], ![[43, 24, 5, 23], [38, 6, 16, 10], [4, 27], [15, 53, 37, 18], [15, 31, 58, 43]]]
 h' := ![![[27, 31, 17], [9, 39, 12], [9, 22, 43], [46, 38, 20], [9, 24, 25], [0, 1]], ![[57, 27, 42], [3, 43, 43], [9, 34, 1], [15, 41, 6], [29, 16, 21], [27, 31, 17]], ![[0, 1], [39, 36, 4], [57, 3, 15], [32, 39, 33], [9, 19, 13], [57, 27, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 37], []]
 b := ![[], [9, 51, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [50, 35, 34, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![65166, 51682, 119600, -97436, -452082]
  a := ![20, -6, -10, 20, 39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![112276, 395228, 363350, -97436, -452082]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![18, 27, 0, 0, 1]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0], ![18, 27, 0, 0, 1]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![46, 39, 1, 0, 0], ![47, 30, 0, 1, 0], ![18, 27, 0, 0, 1]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]], ![![18, 27, 0, 0, 1], ![-6, 17, 29, -1, -3], ![15, 27, 13, 58, 3], ![81, -25, -56, 99, 171], ![-167, -30, 57, -28, -72]]]
  hmulB := by decide  
  f := ![![![11440765, -23133758, -44943486, 1555854, 4768682], ![-7015336, 91439498, -6136, 0, 0]], ![![48589992, -98251002, -190878924, 6607866, 20253015], ![-29794941, 388351570, -26078, 0, 0]], ![![40990298, -82884085, -161024579, 5574362, 17085350], ![-25134892, 327611590, -21996, 0, 0]], ![![33820609, -68386718, -132859518, 4599341, 14096924], ![-20738470, 270308534, -18148, 0, 0]], ![![25726500, -52020081, -101062944, 3498606, 10723181], ![-15775242, 205617006, -13806, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-46, -39, 59, 0, 0], ![-47, -30, 0, 59, 0], ![-18, -27, 0, 0, 59]], ![![0, 0, 0, 0, 1], ![-21, -17, 29, -1, -3], ![-57, -39, 13, 58, 3], ![-86, -92, -56, 99, 171], ![-3, 9, 57, -28, -72]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [41, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 58], [0, 1]]
 g := ![![[40, 36], [55, 20], [57], [55, 48], [12, 1]], ![[0, 23], [0, 39], [57], [41, 11], [24, 58]]]
 h' := ![![[12, 58], [46, 6], [15, 43], [46, 36], [39, 44], [0, 1]], ![[0, 1], [0, 53], [0, 16], [6, 23], [36, 15], [12, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [23, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [41, 47, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-42, -1294, -958, 1137, 1624]
  a := ![9, 2, -3, 15, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-655, -710, -958, 1137, 1624]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0, 0, 0], ![50, -39, 0, 1, 26]] ![![59, 0, 0, 0, 0], ![18, 27, 0, 0, 1]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![3481, 0, 0, 0, 0], ![1062, 1593, 0, 0, 59]], ![![2950, -2301, 0, 59, 1534], ![-3127, -118, 295, -590, -1534]]]
 hmul := by decide  
 g := ![![![![59, 0, 0, 0, 0]], ![![18, 27, 0, 0, 1]]], ![![![50, -39, 0, 1, 26]], ![![-53, -2, 5, -10, -26]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![40, 11, 1, -10, -2]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![40, 11, 1, -10, -2]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![41, 25, 30, 5, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![40, 11, 1, -10, -2], ![-18, 53, 27, -26, -54], ![246, 89, -3, 30, 6], ![36, 77, 7, 52, 108], ![-41, -25, 31, -5, -62]]]
  hmulB := by decide  
  f := ![![![-39, -11, -1, 10, 2], ![61, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![-19, -5, 0, 5, 1], ![30, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-41, -25, -30, -5, 61]], ![![2, 1, 1, 0, -2], ![36, 23, 27, 4, -54], ![0, -1, -3, 0, 6], ![-72, -43, -53, -8, 108], ![41, 25, 31, 5, -62]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [50, 9, 9, 23, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 31, 32, 45], [13, 45, 7, 47], [60, 45, 22, 30], [0, 1]]
 g := ![![[19, 17, 16, 56], [7, 2, 14], [33, 12, 33, 19], [11, 32, 38, 1], []], ![[28, 9, 41, 36, 47, 48], [10, 48, 34], [38, 0, 58, 49, 54, 52], [42, 51, 58, 20, 50, 52], [34, 53, 60, 27, 17, 52]], ![[11, 2, 34, 30, 49, 34], [50, 16, 52], [38, 47, 45, 25, 42, 5], [36, 26, 23, 47, 47, 27], [15, 5, 49, 38, 6, 1]], ![[32, 31, 14, 35, 33, 35], [46, 55, 58], [12, 39, 44, 10], [32, 21, 1, 60, 2, 55], [35, 6, 23, 7, 27, 38]]]
 h' := ![![[26, 31, 32, 45], [25, 28, 1, 42], [58, 19, 1, 40], [60, 9, 31, 43], [0, 0, 0, 1], [0, 1]], ![[13, 45, 7, 47], [33, 52, 40, 27], [44, 58, 36, 20], [42, 30, 30, 16], [16, 10, 41, 45], [26, 31, 32, 45]], ![[60, 45, 22, 30], [0, 22, 57, 25], [11, 19, 26, 28], [5, 0, 38, 2], [44, 43, 45, 31], [13, 45, 7, 47]], ![[0, 1], [13, 20, 24, 28], [19, 26, 59, 34], [28, 22, 23], [18, 8, 36, 45], [60, 45, 22, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [32, 14, 20], []]
 b := ![[], [], [60, 40, 52, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [50, 9, 9, 23, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5074242558, -183909096, 1381477818, -1027868632, 813155578]
  a := ![-44, 23, 13, -35, -95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-629731496, -336275386, -377265402, -83502402, 813155578]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![-27, 1, 0, 0, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![-27, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![-27, 1, 0, 0, 0], ![0, -27, 1, 0, 0], ![0, 1, -27, 2, 0], ![3, -1, -2, -24, 6], ![-6, -1, 2, -1, -30]]]
  hmulB := by decide  
  f := ![![![38262295, -2854187, 57182235, -4248894, 2808], ![86441270, 1541226, 129248691, -28548, 0]], ![![22073932, -1646618, 32989063, -2451234, 1620], ![49868904, 889136, 74564997, -16470, 0]], ![![2942445, -219492, 4397419, -326748, 216], ![6647502, 118524, 9939462, -2196, 0]], ![![33847416, -2524858, 50584312, -3758639, 2484], ![76467280, 1363394, 114335442, -25254, 0]], ![![18817554, -1403682, 28122410, -2089620, 1381], ![42512172, 758020, 63564930, -14040, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-34, 61, 0, 0, 0], ![-3, 0, 61, 0, 0], ![-54, 0, 0, 61, 0], ![-30, 0, 0, 0, 61]], ![![-1, 1, 0, 0, 0], ![15, -27, 1, 0, 0], ![-1, 1, -27, 2, 0], ![19, -1, -2, -24, 6], ![16, -1, 2, -1, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0, 0, 0], ![40, 11, 1, -10, -2]] ![![61, 0, 0, 0, 0], ![-27, 1, 0, 0, 0]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![3721, 0, 0, 0, 0], ![-1647, 61, 0, 0, 0]], ![![2440, 671, 61, -610, -122], ![-1098, -244, 0, 244, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0, 0, 0]], ![![-27, 1, 0, 0, 0]]], ![![![40, 11, 1, -10, -2]], ![![-18, -4, 0, 4, 0]]]]
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
  g := ![1, 2, 3, 2, 2, 2, 2, 2, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB512I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
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
    · exact ![20511149]
    · exact ![923521, 31]
    · exact ![50653, 37, 37]
    · exact ![2825761, 41]
    · exact ![79507, 1849]
    · exact ![103823, 2209]
    · exact ![7890481, 53]
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
  β := ![I31N1, I37N1, I37N2, I41N1, I53N1, I61N1]
  Il := ![[], [I31N1], [I37N1, I37N2], [I41N1], [], [], [I53N1], [], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
