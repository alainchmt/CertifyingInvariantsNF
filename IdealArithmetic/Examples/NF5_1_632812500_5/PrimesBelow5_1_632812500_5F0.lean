
import IdealArithmetic.Examples.NF5_1_632812500_5.RI5_1_632812500_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 18, -2, -3, -2]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-3, 18, -2, -3, -2]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-3, 18, -2, -3, -2], ![13, 33, -5, -7, -4], ![25, 84, -12, -17, -10], ![25, 85, -12, -17, -10], ![33, 92, -13, -19, -11]]]
  hmulB := by decide  
  f := ![![![-1, -2, 1, 0, 0]], ![![0, 0, -1, 1, 0]], ![![1, -1, -1, -1, 2]], ![![-9, -20, 14, -2, -2]], ![![12, 31, -29, 13, 1]]]
  g := ![![![0, 18, -2, -3, -2], ![10, 33, -5, -7, -4], ![21, 84, -12, -17, -10], ![21, 85, -12, -17, -10], ![26, 92, -13, -19, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27115, 14618, 259, -390, -1161]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-27115, 14618, 259, -390, -1161]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-27115, 14618, 259, -390, -1161], ![8898, -4797, -85, 128, 381], ![-2920, 1574, 28, -42, -125], ![-3970, 2140, 38, -57, -170], ![14734, -7943, -141, 212, 631]]]
  hmulB := by decide  
  f := ![![![10, 33, -2, -4, -3]], ![![15, 49, -2, -6, -4]], ![![21, 73, 3, -8, -7]], ![![14, 46, -4, 3, -2]], ![![8, 21, 13, -6, 3]]]
  g := ![![![-20996, 14618, 259, -390, -1161], ![6890, -4797, -85, 128, 381], ![-2261, 1574, 28, -42, -125], ![-3074, 2140, 38, -57, -170], ![11409, -7943, -141, 212, 631]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9667264, 5211728, 92341, -139049, -413929]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-9667264, 5211728, 92341, -139049, -413929]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-9667264, 5211728, 92341, -139049, -413929], ![3172383, -1710272, -30300, 45633, 135831], ![-1041015, 561294, 9898, -14967, -44565], ![-1415415, 762945, 13608, -20402, -60600], ![5253031, -2831893, -50252, 75649, 224880]]]
  hmulB := by decide  
  f := ![![![124362, 397433, -84383, -101882, -55324]], ![![232536, 744284, -152140, -186265, -101882]], ![![520617, 1669303, -326160, -406162, -224090]], ![![522924, 1680516, -308904, -393917, -219897]], ![![681476, 2190425, -400742, -511985, -286065]]]
  g := ![![![-7278702, 5211728, 92341, -139049, -413929], ![2388562, -1710272, -30300, 45633, 135831], ![-783821, 561294, 9898, -14967, -44565], ![-1065684, 762945, 13608, -20402, -60600], ![3955148, -2831893, -50252, 75649, 224880]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-3, 18, -2, -3, -2]] ![![-27115, 14618, 259, -390, -1161]]
  ![![229791, -123882, -2195, 3305, 9839]] where
 M := ![![![229791, -123882, -2195, 3305, 9839]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![229791, -123882, -2195, 3305, 9839]] ![![-9667264, 5211728, 92341, -139049, -413929]]
  ![![-2565159759271, 1382906602420, 24501574233, -36895581599, -109834043286]] where
 M := ![![![-2565159759271, 1382906602420, 24501574233, -36895581599, -109834043286]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-2565159759271, 1382906602420, 24501574233, -36895581599, -109834043286]] ![![-9667264, 5211728, 92341, -139049, -413929]]
  ![![28634940410246253628, -15437419837152179683, -273511665533602297, 411866269408800012, 1226080080643646854]] where
 M := ![![![28634940410246253628, -15437419837152179683, -273511665533602297, 411866269408800012, 1226080080643646854]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![28634940410246253628, -15437419837152179683, -273511665533602297, 411866269408800012, 1226080080643646854]] ![![-9667264, 5211728, 92341, -139049, -413929]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-319652532102479398868787432, 172328290870443719716101360, 3053217335004419163978430, -4597673123042922407601490, -13686761582989564226339860]]]
 hmul := by decide  
 g := ![![![![-159826266051239699434393716, 86164145435221859858050680, 1526608667502209581989215, -2298836561521461203800745, -6843380791494782113169930]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N2, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4357, -2343, -45, 62, 188]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![4357, -2343, -45, 62, 188]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![4357, -2343, -45, 62, 188], ![-1442, 740, 39, -28, -64], ![484, -187, -64, 50, 8], ![714, -236, -86, -25, 78], ![-2618, 769, 435, -92, -193]]]
  hmulB := by decide  
  f := ![![![-10535, -34417, 3475, 5872, 3668]], ![![-7824, -25584, 2465, 4274, 2692]], ![![-17262, -56507, 5138, 9204, 5856]], ![![-14910, -48902, 3976, 7603, 4930]], ![![-22362, -73313, 6111, 11514, 7435]]]
  g := ![![![1327, -2343, -45, 62, 188], ![-438, 740, 39, -28, -64], ![156, -187, -64, 50, 8], ![186, -236, -86, -25, 78], ![-744, 769, 435, -92, -193]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 18, -14, -2, 6]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![11, 18, -14, -2, 6]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![11, 18, -14, -2, 6], ![-50, -117, 98, -30, -10], ![50, 238, -217, 166, -50], ![308, 450, -338, -119, 196], ![-978, -1992, 1626, -254, -343]]]
  hmulB := by decide  
  f := ![![![197, 338, -42, -66, -38]], ![![145, 405, -44, -72, -44]], ![![332, 870, -93, -154, -94]], ![![180, 574, -54, -95, -60]], ![![170, 612, -54, -98, -63]]]
  g := ![![![7, 18, -14, -2, 6], ![-43, -117, 98, -30, -10], ![82, 238, -217, 166, -50], ![178, 450, -338, -119, 196], ![-746, -1992, 1626, -254, -343]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![4357, -2343, -45, 62, 188]] ![![4357, -2343, -45, 62, 188]]
  ![![21892359, -11803916, -208114, 314642, 937260]] where
 M := ![![![21892359, -11803916, -208114, 314642, 937260]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![21892359, -11803916, -208114, 314642, 937260]] ![![11, 18, -14, -2, 6]]
  ![![875505, 156482, -480292, 279400, -11334]] where
 M := ![![![875505, 156482, -480292, 279400, -11334]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![875505, 156482, -480292, 279400, -11334]] ![![11, 18, -14, -2, 6]]
  ![![74931707, 31448528, -5564754, -116543706, 86352772]] where
 M := ![![![74931707, 31448528, -5564754, -116543706, 86352772]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![74931707, 31448528, -5564754, -116543706, 86352772]] ![![11, 18, -14, -2, 6]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-121374887787, -228114508026, 183041843364, -10081971492, -52048224510]]]
 hmul := by decide  
 g := ![![![![-40458295929, -76038169342, 61013947788, -3360657164, -17349408170]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2352, 7605, -1162, -1601, -926]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![2352, 7605, -1162, -1601, -926]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![2352, 7605, -1162, -1601, -926], ![5807, 18784, -2832, -3925, -2276], ![14283, 46219, -6879, -9589, -5574], ![14598, 47263, -6911, -9711, -5664], ![16467, 53327, -7732, -10905, -6371]]]
  hmulB := by decide  
  f := ![![![562242, -303110, -5371, 8087, 24074]], ![![-36901, 19893, 353, -531, -1580]], ![![12109, -6528, -116, 175, 518]], ![![16466, -8871, -161, 237, 706]], ![![276237, -148938, -2628, 3970, 11827]]]
  g := ![![![1026, 7605, -1162, -1601, -926], ![2527, 18784, -2832, -3925, -2276], ![6201, 46219, -6879, -9589, -5574], ![6318, 47263, -6911, -9711, -5664], ![7116, 53327, -7732, -10905, -6371]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![2352, 7605, -1162, -1601, -926]] ![![2352, 7605, -1162, -1601, -926]]
  ![![-5522547, -18016063, 1947357, 3172582, 1957666]] where
 M := ![![![-5522547, -18016063, 1947357, 3172582, 1957666]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-5522547, -18016063, 1947357, 3172582, 1957666]] ![![2352, 7605, -1162, -1601, -926]]
  ![![-11243970296, -36065606296, 6980433513, 8724147217, 4822075458]] where
 M := ![![![-11243970296, -36065606296, 6980433513, 8724147217, 4822075458]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-11243970296, -36065606296, 6980433513, 8724147217, 4822075458]] ![![2352, 7605, -1162, -1601, -926]]
  ![![70582955609767, 229138101638040, -30391980479646, -44681202294238, -26546712557676]] where
 M := ![![![70582955609767, 229138101638040, -30391980479646, -44681202294238, -26546712557676]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![70582955609767, 229138101638040, -30391980479646, -44681202294238, -26546712557676]] ![![2352, 7605, -1162, -1601, -926]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-26873496163050570, -91197671803295725, -7819093986564050, 2449395879583525, 4730198470241350]]]
 hmul := by decide  
 g := ![![![![-5374699232610114, -18239534360659145, -1563818797312810, 489879175916705, 946039694048270]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![290444, 944387, -117712, -178341, -107200]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![290444, 944387, -117712, -178341, -107200]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 2, 0, 1, 1]] where
  M :=![![![290444, 944387, -117712, -178341, -107200], ![679259, 2209532, -270872, -413765, -249482], ![1582091, 5148545, -619969, -955509, -578048], ![1494808, 4867751, -569849, -890841, -541744], ![1619975, 5277251, -608244, -958433, -584521]]]
  hmulB := by decide  
  f := ![![![-54405918, 29330846, 519667, -782539, -2329532]], ![![17853717, -9625143, -170531, 256795, 764454]], ![![-5858837, 3158560, 55964, -84267, -250864]], ![![-7965536, 4294343, 76063, -114567, -341062]], ![![8186453, -4413415, -78190, 117746, 350525]]]
  g := ![![![41492, 165541, -16816, -10163, -107200], ![97037, 386928, -38696, -23469, -249482], ![226013, 900663, -88567, -53923, -578048], ![213544, 850177, -81407, -49871, -541744], ![231425, 920899, -86892, -53416, -584521]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [5, 6, 3, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 0, 3, 1], [3, 2, 1, 1], [6, 4, 3, 5], [0, 1]]
 g := ![![[5, 1, 5, 1], []], ![[0, 2, 5, 1, 4, 2], [0, 6, 3, 3, 0, 1]], ![[5, 0, 0, 6, 0, 4], [0, 3, 5, 4, 1, 1]], ![[4, 5, 4, 1, 2, 3], [1, 3, 5, 5, 3, 6]]]
 h' := ![![[3, 0, 3, 1], [0, 0, 0, 1], [0, 1]], ![[3, 2, 1, 1], [6, 5, 2, 4], [3, 0, 3, 1]], ![[6, 4, 3, 5], [6, 4, 6, 5], [3, 2, 1, 1]], ![[0, 1], [1, 5, 6, 4], [6, 4, 3, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6, 1, 5], []]
 b := ![[], [], [2, 2, 1, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [5, 6, 3, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![936723921, 477390968, -323400504, -1187682952, 1051466912]
  a := ![-5, -2, 2, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![133817703, -232220408, -46200072, -319878552, 1051466912]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54405918, 29330846, 519667, -782539, -2329532]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-54405918, 29330846, 519667, -782539, -2329532]] 
 ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-54405918, 29330846, 519667, -782539, -2329532], ![17853717, -9625143, -170531, 256795, 764454], ![-5858837, 3158560, 55964, -84267, -250864], ![-7965536, 4294343, 76063, -114567, -341062], ![29563273, -15937962, -282331, 425199, 1265829]]]
  hmulB := by decide  
  f := ![![![290444, 944387, -117712, -178341, -107200]], ![![345989, 1125122, -139592, -211973, -127526]], ![![474965, 1544981, -189463, -289365, -174464]], ![![213544, 695393, -81407, -127263, -77392]], ![![231425, 753893, -86892, -136919, -83503]]]
  g := ![![![-33358428, 29330846, 519667, -782539, -2329532], ![10946823, -9625143, -170531, 256795, 764454], ![-3592283, 3158560, 55964, -84267, -250864], ![-4883996, 4294343, 76063, -114567, -341062], ![18126433, -15937962, -282331, 425199, 1265829]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![290444, 944387, -117712, -178341, -107200]] ![![-54405918, 29330846, 519667, -782539, -2329532]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1097, -3494, 802, 942, 504]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-1097, -3494, 802, 942, 504]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![8, 10, 1, 0, 0], ![4, 4, 0, 1, 0], ![3, 7, 0, 0, 1]] where
  M :=![![![-1097, -3494, 802, 942, 504], ![-3090, -9871, 2116, 2546, 1380], ![-8494, -27194, 5523, 6778, 3712], ![-9914, -31814, 6084, 7639, 4232], ![-11850, -38062, 7100, 9002, 5011]]]
  hmulB := by decide  
  f := ![![![18681, -10066, -182, 270, 800]], ![![-6130, 3299, 64, -94, -260]], ![![8194, -4424, -73, 114, 352]], ![![4818, -2582, -56, 71, 208]], ![![265, -169, 18, -10, 15]]]
  g := ![![![-1163, -1710, 802, 942, 504], ![-3122, -4625, 2116, 2546, 1380], ![-8266, -12320, 5523, 6778, 3712], ![-9258, -13894, 6084, 7639, 4232], ![-10881, -16377, 7100, 9002, 5011]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [5, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 10], [0, 1]]
 g := ![![[8, 9], [2, 5], [1]], ![[0, 2], [0, 6], [1]]]
 h' := ![![[4, 10], [1, 8], [6, 4], [0, 1]], ![[0, 1], [0, 3], [0, 7], [4, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [10, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [5, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11756, 25880, -59065, 104095, -21410]
  a := ![6, -62, -1, -57, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9874, 31820, -59065, 104095, -21410]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-488405436, 263304889, 4665090, -7024905, -20912360]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-488405436, 263304889, 4665090, -7024905, -20912360]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![6, 10, 1, 0, 0], ![3, 3, 0, 1, 0], ![4, 1, 0, 0, 1]] where
  M :=![![![-488405436, 263304889, 4665090, -7024905, -20912360], ![160273975, -86405506, -1530886, 2305275, 6862550], ![-52595125, 28354639, 502369, -756497, -2252000], ![-71507236, 38550375, 683011, -1028517, -3061772], ![265391603, -143075591, -2534938, 3817215, 11363435]]]
  hmulB := by decide  
  f := ![![![-1218, -2608, 2145, -455, -364]], ![![2457, 7843, -6885, 3835, -546]], ![![2315, 6248, -5370, 2335, 52]], ![![-3213, -5792, 4597, 15, -1500]], ![![6538, 16825, -14322, 5642, 553]]]
  g := ![![![-37424711, 23512824, 4665090, -7024905, -20912360], ![12281206, -7715911, -1530886, 2305275, 6862550], ![-4030168, 2532040, 502369, -756497, -2252000], ![-5479333, 3442508, 683011, -1028517, -3061772], ![20335986, -12776481, -2534938, 3817215, 11363435]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [1, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 10], [0, 1]]
 g := ![![[10, 1], [10, 1], [1]], ![[0, 10], [0, 10], [1]]]
 h' := ![![[1, 10], [1, 10], [10, 1], [0, 1]], ![[0, 1], [0, 1], [0, 10], [1, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [7, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [1, 10, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-697, -2378, 1095, -28, 341]
  a := ![-1, -3, 1, -5, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-777, -1235, 1095, -28, 341]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5306, 5568, -3675, -4505, 4460]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![5306, 5568, -3675, -4505, 4460]] 
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![5306, 5568, -3675, -4505, 4460], ![-40185, -83109, 68053, -11855, -13470], ![95905, 283798, -246364, 124251, -10240], ![123178, 63605, -20813, -178311, 136106], ![-649869, -1134512, 894709, 43565, -321767]]]
  hmulB := by decide  
  f := ![![![244008, -150595, 498, 7313, 12764]], ![![35747, -27200, 820, 2085, 2490]], ![![154679, -106938, 1943, 6868, 9464]], ![![66598, -53392, 1831, 4350, 4940]], ![![94839, -73986, 2314, 5794, 6789]]]
  g := ![![![1010, 5568, -3675, -4505, 4460], ![-22493, -83109, 68053, -11855, -13470], ![84664, 283798, -246364, 124251, -10240], ![-358, 63605, -20813, -178311, 136106], ![-287788, -1134512, 894709, 43565, -321767]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-1097, -3494, 802, 942, 504]] ![![-488405436, 263304889, 4665090, -7024905, -20912360]]
  ![![-244008, 150595, -498, -7313, -12764]] where
 M := ![![![-244008, 150595, -498, -7313, -12764]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![-244008, 150595, -498, -7313, -12764]] ![![5306, 5568, -3675, -4505, 4460]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![744442, 2385010, -467993, -581849, -320750]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![744442, 2385010, -467993, -581849, -320750]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![5, 6, 7, 1, 0], ![2, 0, 2, 0, 1]] where
  M :=![![![744442, 2385010, -467993, -581849, -320750], ![1984151, 6370699, -1202891, -1517835, -842948], ![5225749, 16797272, -3069790, -3923617, -2192722], ![5817004, 18723489, -3290803, -4272681, -2405782], ![6818939, 21962416, -3794995, -4961687, -2802885]]]
  hmulB := by decide  
  f := ![![![-60820, -284661, 259082, -196353, 58422]], ![![-663729, -911756, 671178, 321811, -451128]], ![![3930835, 8578881, -7098231, 1664167, 1094750]], ![![1539563, 3202337, -2625192, 474709, 506996]], ![![212341, 1349469, -1253916, 1084887, -380377]]]
  g := ![![![330399, 452008, 326650, -581849, -320750], ![866094, 1190593, 854450, -1517835, -842948], ![2248406, 3102998, 2213921, -3923617, -2192722], ![2460921, 3412275, 2417656, -4272681, -2405782], ![2864088, 3979426, 2810968, -4961687, -2802885]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [8, 3, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 9], [2, 3], [0, 1]]
 g := ![![[12, 7, 12], [4, 9], [1]], ![[4, 10, 10], [11, 3], [1]], ![[9, 9, 4], [9, 1], [1]]]
 h' := ![![[8, 9], [6, 3, 5], [5, 10, 10], [0, 1]], ![[2, 3], [12, 6, 2], [10, 9, 4], [8, 9]], ![[0, 1], [6, 4, 6], [0, 7, 12], [2, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], []]
 b := ![[], [3, 6, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [8, 3, 3, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17707652, -42311879, 19352367, 6462818, -1458381]
  a := ![8, 19, -3, 26, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3623460, -6237599, -1766969, 6462818, -1458381]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![60820, 284661, -259082, 196353, -58422]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![60820, 284661, -259082, 196353, -58422]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![3, 12, 1, 0, 0], ![8, 8, 0, 1, 0], ![12, 10, 0, 0, 1]] where
  M :=![![![60820, 284661, -259082, 196353, -58422], ![663729, 911756, -671178, -321811, 451128], ![-3930835, -8578881, 7098231, -1664167, -1094750], ![3215052, 11527945, -10237643, 6427053, -1342356], ![4979597, -954657, 2622610, -11167903, 7251245]]]
  hmulB := by decide  
  f := ![![![-744442, -2385010, 467993, 581849, 320750]], ![![-1984151, -6370699, 1202891, 1517835, 842948]], ![![-2405299, -7723130, 1454497, 1837168, 1020796]], ![![-2126596, -6828397, 1281375, 1620781, 901182]], ![![-2737981, -8791502, 1649217, 2086325, 1160105]]]
  g := ![![![-2438, 185157, -259082, 196353, -58422], ![-12445, 540700, -671178, -321811, 451128], ![94216, -5345909, 7098231, -1664167, -1094750], ![-106167, 7414369, -10237643, 6427053, -1342356], ![-43073, -1199631, 2622610, -11167903, 7251245]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [6, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 12], [0, 1]]
 g := ![![[6, 9], [9], [3, 1]], ![[7, 4], [9], [6, 12]]]
 h' := ![![[3, 12], [10, 10], [8, 3], [0, 1]], ![[0, 1], [1, 3], [4, 10], [3, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [5, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [6, 10, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-38591, -84628, 59305, -4290, -9317]
  a := ![-10, 1, 5, -7, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5414, -51446, 59305, -4290, -9317]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![744442, 2385010, -467993, -581849, -320750]] ![![60820, 284661, -259082, 196353, -58422]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-118146, -384285, 47246, 72067, 43430]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-118146, -384285, 47246, 72067, 43430]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![6, 0, 13, 6, 1]] where
  M :=![![![-118146, -384285, 47246, 72067, 43430], ![-275373, -896070, 108238, 166559, 100704], ![-639073, -2080511, 246523, 383035, 232414], ![-600452, -1956173, 224799, 354761, 216476], ![-648761, -2114375, 238866, 380283, 232777]]]
  hmulB := by decide  
  f := ![![![-636044, 342896, 6077, -9149, -27234]], ![![208723, -112521, -1997, 3005, 8936]], ![![-68483, 36942, 642, -989, -2926]], ![![-93152, 50137, 945, -1355, -3994]], ![![-289400, 156014, 2769, -4168, -12389]]]
  g := ![![![-22278, -22605, -30432, -11089, 43430], ![-51741, -52710, -70642, -25745, 100704], ![-119621, -122383, -163227, -59497, 232414], ![-111724, -115069, -152317, -55535, 216476], ![-120319, -124375, -163955, -59787, 232777]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [11, 9, 16, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 8, 4], [5, 3, 6, 5], [8, 5, 7, 12], [0, 1]]
 g := ![![[9, 15, 1, 9], [6, 14, 1], [1], []], ![[13, 11, 3, 2, 13], [13, 4, 13], [15, 13, 9], [16]], ![[7, 0, 1, 10, 4, 5], [14, 2, 9], [6, 1, 15], [5, 1, 8]], ![[0, 3, 7, 12], [10, 0, 16], [5, 11, 15], [0, 7, 8]]]
 h' := ![![[3, 8, 4], [4, 7, 13, 3], [6, 8, 1, 16], [0, 0, 1], [0, 1]], ![[5, 3, 6, 5], [2, 16, 3, 13], [14, 13, 0, 8], [3, 6, 2, 14], [3, 8, 4]], ![[8, 5, 7, 12], [0, 3, 2, 1], [1, 16, 1, 14], [4, 8, 11, 10], [5, 3, 6, 5]], ![[0, 1], [0, 8, 16], [12, 14, 15, 13], [13, 3, 3, 10], [8, 5, 7, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 16, 4], []]
 b := ![[], [], [12, 12, 16, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [11, 9, 16, 1, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-46352911703, -88044543770, 70815473166, -4892532134, -19416845828]
  a := ![6, -10, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4126362545, -5179090810, 19013792290, 6565208402, -19416845828]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![636044, -342896, -6077, 9149, 27234]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![636044, -342896, -6077, 9149, 27234]] 
 ![![17, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![636044, -342896, -6077, 9149, 27234], ![-208723, 112521, 1997, -3005, -8936], ![68483, -36942, -642, 989, 2926], ![93152, -50137, -945, 1355, 3994], ![-345655, 186206, 3405, -5025, -14793]]]
  hmulB := by decide  
  f := ![![![118146, 384285, -47246, -72067, -43430]], ![![57897, 188340, -23042, -35233, -21252]], ![![141839, 461458, -56189, -86120, -51992]], ![![56170, 182884, -21561, -33586, -20398]], ![![79861, 260005, -30726, -47805, -29021]]]
  g := ![![![152572, -342896, -6077, 9149, 27234], ![-50069, 112521, 1997, -3005, -8936], ![16426, -36942, -642, 989, 2926], ![22360, -50137, -945, 1355, 3994], ![-82949, 186206, 3405, -5025, -14793]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-118146, -384285, 47246, 72067, 43430]] ![![636044, -342896, -6077, 9149, 27234]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, 0, -3, 2]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![2, 1, 0, -3, 2]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![17, 17, 1, 0, 0], ![17, 7, 0, 1, 0], ![17, 11, 0, 0, 1]] where
  M :=![![![2, 1, 0, -3, 2], ![-19, -36, 30, -3, -8], ![61, 163, -137, 57, 2], ![30, -39, 51, -107, 60], ![-279, -429, 330, 81, -167]]]
  hmulB := by decide  
  f := ![![![36, -310, 33, 51, 34]], ![![-221, -577, 81, 117, 68]], ![![-188, -869, 112, 165, 100]], ![![-71, -564, 69, 103, 64]], ![![-124, -691, 87, 129, 79]]]
  g := ![![![1, 0, 0, -3, 2], ![-18, -23, 30, -3, -8], ![73, 109, -137, 57, 2], ![-2, -43, 51, -107, 60], ![-233, -251, 330, 81, -167]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [7, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 18], [0, 1]]
 g := ![![[16, 11], [17, 1], [4], [1]], ![[0, 8], [0, 18], [4], [1]]]
 h' := ![![[2, 18], [14, 12], [2, 18], [12, 2], [0, 1]], ![[0, 1], [0, 7], [0, 1], [16, 17], [2, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [11, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [7, 17, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2595, -3040, -3336, 11344, -792]
  a := ![6, 13, 4, 20, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6593, -896, -3336, 11344, -792]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13540753362, -37237896453, 32002371520, -14363445495, 41322254]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-13540753362, -37237896453, 32002371520, -14363445495, 41322254]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![3, 7, 1, 0, 0], ![18, 6, 0, 1, 0], ![3, 17, 0, 0, 1]] where
  M :=![![![-13540753362, -37237896453, 32002371520, -14363445495, 41322254], ![-14694023527, 17676495332, -22337261656, 49641297545, -28768213244], ![279787003497, 509564766453, -405951574385, 4966774233, 128050808334], ![-502372834456, -1288403212283, 1095797881109, -428288836041, -44674523312], ![362403970885, 1638723432385, -1487317503156, 1105462990973, -319609569689]]]
  hmulB := by decide  
  f := ![![![444196617868, -239463937762, -4244089525, 6387420199, 19018488058]], ![![-145760484265, 78601255241, 1388986793, -2100758851, -6243647660]], ![![18953415062, -10206590449, -182882448, 270219125, 810108448]], ![![378211923458, -203881721159, -3615265405, 5436452199, 16192045930]], ![![-72983565534, 39369174493, 693441353, -1054531295, -3127848283]]]
  g := ![![![7835272854, -9251384339, 32002371520, -14363445495, 41322254], ![-39732681823, 19223640358, -22337261656, 49641297545, -28768213244], ![53899335024, 60240073688, -405951574385, 4966774233, 128050808334], ![213339796889, -296304656184, 1095797881109, -428288836041, -44674523312], ![-742902560426, 571080562808, -1487317503156, 1105462990973, -319609569689]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [12, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 18], [0, 1]]
 g := ![![[17, 7], [9, 6], [6], [1]], ![[14, 12], [1, 13], [6], [1]]]
 h' := ![![[5, 18], [6, 8], [15, 5], [7, 5], [0, 1]], ![[0, 1], [8, 11], [2, 14], [13, 14], [5, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [13, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [12, 14, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3150, -4689, 3513, 1166, -1983]
  a := ![2, -5, -1, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1512, -135, 3513, 1166, -1983]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![992260, 3307900, -2914067, 1702879, -290298]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![992260, 3307900, -2914067, 1702879, -290298]] 
 ![![19, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![992260, 3307900, -2914067, 1702879, -290298], ![4025263, 3593855, -2168853, -4125255, 3696056], ![-33693703, -68368654, 55767838, -8462961, -11946566], ![41542152, 122732517, -106521099, 53598985, -4337706], ![6036259, -88485802, 88973179, -111604019, 52108557]]]
  hmulB := by decide  
  f := ![![![10479144538, -5649374767, -100099834, 150715901, 448686234]], ![![7540486819, -4065117920, -72029858, 108449413, 322860676]], ![![7229338457, -3897367440, -69058707, 103972826, 309537260]], ![![8905296868, -4800887257, -85067941, 128077221, 381296868]], ![![251844609, -135751116, -2408120, 3618574, 10780979]]]
  g := ![![![-1810065, 3307900, -2914067, 1702879, -290298], ![2327074, 3593855, -2168853, -4125255, 3696056], ![18202079, -68368654, 55767838, -8462961, -11946566], ![-60272887, 122732517, -106521099, 53598985, -4337706], ![95881153, -88485802, 88973179, -111604019, 52108557]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![2, 1, 0, -3, 2]] ![![-13540753362, -37237896453, 32002371520, -14363445495, 41322254]]
  ![![2190150914887, 7085857204045, -6220361168255, 3516706896624, -533881138178]] where
 M := ![![![2190150914887, 7085857204045, -6220361168255, 3516706896624, -533881138178]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![2190150914887, 7085857204045, -6220361168255, 3516706896624, -533881138178]] ![![992260, 3307900, -2914067, 1702879, -290298]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![383151567343193860466, 936843253679135200909, -790751108654495006142, 275216469002881170275, 56791667518558848834]]]
 hmul := by decide  
 g := ![![![![20165871965431255814, 49307539667322905311, -41618479402868158218, 14485077315941114225, 2989035132555728886]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151587117, -81722327, -1447911, 2180330, 6490600]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![151587117, -81722327, -1447911, 2180330, 6490600]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![18, 15, 15, 1, 0], ![9, 14, 16, 0, 1]] where
  M :=![![![151587117, -81722327, -1447911, 2180330, 6490600], ![-49744470, 26817806, 475143, -715492, -2129940], ![16324028, -8800467, -155922, 234794, 698956], ![22193808, -11964932, -211988, 319221, 950286], ![-82369982, 44406589, 786771, -1184756, -3526887]]]
  hmulB := by decide  
  f := ![![![-279, -913, 105, 168, 104]], ![![-664, -2150, 271, 378, 232]], ![![-1478, -4801, 488, 920, 524]], ![![-1672, -5439, 595, 1011, 598]], ![![-1617, -5238, 586, 970, 565]]]
  g := ![![![2344599, -8925899, -6000107, 2180330, 6490600], ![-769398, 2929102, 1968981, -715492, -2129940], ![252484, -961207, -646136, 234794, 698956], ![343272, -1306837, -878473, 319221, 950286], ![-1274017, 4850189, 3260361, -1184756, -3526887]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [8, 11, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 19, 2], [2, 3, 21], [0, 1]]
 g := ![![[9, 22, 18], [22, 1, 8], [13, 22, 1], []], ![[1, 5, 21, 3], [3, 15, 12, 2], [3, 2, 6, 18], [3, 4]], ![[12, 5, 11, 22], [1, 3, 10, 11], [8, 13, 0, 14], [7, 4]]]
 h' := ![![[20, 19, 2], [8, 9, 15], [11, 3, 13], [0, 0, 1], [0, 1]], ![[2, 3, 21], [9, 16, 17], [14, 7, 22], [8, 5, 3], [20, 19, 2]], ![[0, 1], [5, 21, 14], [8, 13, 11], [17, 18, 19], [2, 3, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 2], []]
 b := ![[], [7, 21, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [8, 11, 1, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26899568, 61725152, -54267915, 17714827, 6245307]
  a := ![10, -1, 0, 5, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15138047, -12670937, -18257184, 17714827, 6245307]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-279, -913, 105, 168, 104]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-279, -913, 105, 168, 104]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![20, 16, 1, 0, 0], ![1, 9, 0, 1, 0], ![12, 1, 0, 0, 1]] where
  M :=![![![-279, -913, 105, 168, 104], ![-664, -2150, 271, 378, 232], ![-1478, -4801, 488, 920, 524], ![-1304, -4398, 410, 759, 542], ![-1736, -5341, 931, 786, 427]]]
  hmulB := by decide  
  f := ![![![151587117, -81722327, -1447911, 2180330, 6490600]], ![![-49744470, 26817806, 475143, -715492, -2129940]], ![![97919776, -52789657, -935298, 1408414, 4192692]], ![![-11909535, 6420565, 113756, -171299, -509938]], ![![73344824, -39541023, -700566, 1054944, 3140451]]]
  g := ![![![-165, -183, 105, 168, 104], ![-402, -440, 271, 378, 232], ![-802, -931, 488, 920, 524], ![-729, -797, 410, 759, 542], ![-1142, -1206, 931, 786, 427]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [14, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 22], [0, 1]]
 g := ![![[15, 1], [22, 12], [11, 9], [1]], ![[12, 22], [9, 11], [7, 14], [1]]]
 h' := ![![[20, 22], [14, 22], [7, 14], [9, 20], [0, 1]], ![[0, 1], [17, 1], [11, 9], [18, 3], [20, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [3, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [14, 3, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12422, -29012, 19650, -1764, -1948]
  a := ![6, 1, -3, 6, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16534, -14156, 19650, -1764, -1948]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![151587117, -81722327, -1447911, 2180330, 6490600]] ![![-279, -913, 105, 168, 104]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)


lemma PB1567I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1567I0 : PrimesBelowBoundCertificateInterval O 1 23 1567 where
  m := 9
  g := ![5, 5, 5, 2, 3, 2, 2, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1567I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N2, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![2401, 7]
    · exact ![121, 121, 11]
    · exact ![2197, 169]
    · exact ![83521, 17]
    · exact ![361, 361, 19]
    · exact ![12167, 529]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N2
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N1
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I11N0, I11N1, I11N2, I13N1, I17N1, I19N0, I19N1, I19N2, I23N1]
  Il := ![[I2N0, I2N1, I2N2, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N0, I11N1, I11N2], [I13N1], [I17N1], [I19N0, I19N1, I19N2], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
