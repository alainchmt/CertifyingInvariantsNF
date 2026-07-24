
import IdealArithmetic.Examples.NF5_1_405000000_1.RI5_1_405000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22298, -4489, 204, 580, 1677]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-22298, -4489, 204, 580, 1677]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-22298, -4489, 204, 580, 1677], ![100620, -24868, 5573, -6300, 2320], ![139200, 95253, -10948, 1866, -25200], ![-806310, 102693, -30760, 42602, 2572], ![13425, -193686, 28138, -16377, 42022]]]
  hmulB := by decide  
  f := ![![![-364, 340, 135, 77, 72]], ![![2160, -148, 386, -9, 154]], ![![9240, 2229, 776, 156, -36]], ![![-2342, 5366, 881, 891, 271]], ![![2985, -204, 1555, 174, 814]]]
  g := ![![![-11439, -4489, 204, 580, 1677], ![53460, -24868, 5573, -6300, 2320], ![68667, 95253, -10948, 1866, -25200], ![-424456, 102693, -30760, 42602, 2572], ![14901, -193686, 28138, -16377, 42022]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-5, -3, 1, 0, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![-5, -3, 1, 0, 1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-5, -3, 1, 0, 1], ![60, -6, 3, -2, 0], ![0, 61, -6, 6, -8], ![-270, 11, 5, 11, 12], ![165, -68, 20, -9, 11]]]
  hmulB := by decide  
  f := ![![![-99, 89, -49, 4, -32], ![80, 10, 2, 0, 0]], ![![65, -56, 29, -3, 19], ![-46, -6, -1, 0, 0]], ![![-10, 15, -5, 1, -4], ![8, 1, 0, 0, 0]], ![![14215, -12445, 6872, -562, 4478], ![-11192, -1411, -281, -1, 0]], ![![-47, 46, -25, 2, -16], ![41, 5, 1, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![-3, -3, 1, 0, 1], ![30, -6, 3, -2, 0], ![4, 61, -6, 6, -8], ![-141, 11, 5, 11, 12], ![77, -68, 20, -9, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 2, 0], ![0, 1, 0, 1, 4], ![60, -2, 6, -4, 1]]]
  hmulB := by decide  
  f := ![![![0, -2, 0, -1, -4], ![2, 0, 0, 2, 0]], ![![0, -1, 0, -1, -4], ![1, 0, 0, 2, 0]], ![![0, 0, 1, 0, 0], ![1, -1, 0, 0, 0]], ![![0, -1, 0, 0, -2], ![1, 0, 0, 1, 0]], ![![-40, 8, -12, 28, 104], ![20, 18, 0, -52, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-2, 1, 1, 2, 0], ![-1, 1, 0, 1, 4], ![30, -2, 6, -4, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-22298, -4489, 204, 580, 1677]] ![![2, 0, 0, 0, 0], ![-5, -3, 1, 0, 1]]
  ![![2, 0, 0, 0, 0], ![-27, 1, 0, 1, 1]] where
 M := ![![![-44596, -8978, 408, 1160, 3354], ![-37745, -1384, -549, 1489, 1477]]]
 hmul := by decide  
 g := ![![![![535507, -32643, 2386, -20569, -17082], ![39710, -636, -22, 0, 0]], ![![-99400, -3026777, 579580, -250312, 583789], ![-4745, -144895, 36361, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-27, 1, 0, 1, 1]] ![![2, 0, 0, 0, 0], ![-5, -3, 1, 0, 1]]
  ![![-423808, -32581, -3712, 15328, 20318]] where
 M := ![![![4, 0, 0, 0, 0], ![-10, -6, 2, 0, 2]], ![![-54, 2, 0, 2, 2], ![90, 18, 1, 0, -4]]]
 hmul := by decide  
 g := ![![![![-690268, -228716, -136086, -33602, -39378]], ![![-3848225, -1275032, -757735, -187152, -218981]]], ![![![-3237327, -1071298, -637024, -157201, -184053]], ![![-18007860, -5966151, -3548071, -876141, -1026065]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-423808, -32581, -3712, 15328, 20318]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![2, 0, 0, 0, 0], ![-36, 9, -1, 2, 0]] where
 M := ![![![-847616, -65162, -7424, 30656, 40636], ![795272, -485409, 85615, -73368, 81630]]]
 hmul := by decide  
 g := ![![![![-34216, -129979, 7110, -6316, 20318], ![21644, 0, 0, 0, 0]], ![![-33914, -134817, 30820, -12709, 40815], ![-23975, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-36, 9, -1, 2, 0]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![2, 2, 0, 0, 0]], ![![-72, 18, -2, 4, 0], ![-36, -26, 8, 0, 8]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0]]], ![![![-36, 9, -1, 2, 0]], ![![-18, -13, 4, 0, 4]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, -13, -7, -2, -2]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-33, -13, -7, -2, -2]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-33, -13, -7, -2, -2], ![-120, -38, -25, -6, -8], ![-480, -135, -86, -18, -24], ![-660, -249, -127, -35, -32], ![-450, -180, -104, -30, -33]]]
  hmulB := by decide  
  f := ![![![-111, 33, -7, 6, -2]], ![![-40, -36, 7, -2, 8]], ![![480, -51, 12, -18, -8]], ![![-220, 263, -53, 29, -40]], ![![-590, -32, 4, 14, 27]]]
  g := ![![![-11, -13, -7, -2, -2], ![-40, -38, -25, -6, -8], ![-160, -135, -86, -18, -24], ![-220, -249, -127, -35, -32], ![-150, -180, -104, -30, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28742, 8230, -1746, 1513, -447]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-28742, 8230, -1746, 1513, -447]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-28742, 8230, -1746, 1513, -447], ![-26820, -28081, 5548, -1704, 6052], ![363120, -35080, 8231, -13112, -6816], ![-191070, 199976, -40762, 22715, -29250], ![-432045, -30634, 4732, 9295, 21202]]]
  hmulB := by decide  
  f := ![![![34956, 11650, 6914, 1717, 2003]], ![![51712, 17077, 10194, 2511, 2957]], ![![160664, 53076, 31539, 7766, 9090]], ![![212610, 71104, 41974, 10451, 12098]], ![![194759, 64678, 38560, 9549, 11214]]]
  g := ![![![-10862, 8230, -1746, 1513, -447], ![-7313, -28081, 5548, -1704, 6052], ![131790, -35080, 8231, -13112, -6816], ![-83674, 199976, -40762, 22715, -29250], ![-151093, -30634, 4732, 9295, 21202]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-33, -13, -7, -2, -2]] ![![-33, -13, -7, -2, -2]]
  ![![8229, 2726, 1620, 400, 468]] where
 M := ![![![8229, 2726, 1620, 400, 468]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![8229, 2726, 1620, 400, 468]] ![![-28742, 8230, -1746, 1513, -447]]
  ![![102, -48, 10, -7, 5]] where
 M := ![![![102, -48, 10, -7, 5]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![102, -48, 10, -7, 5]] ![![-28742, 8230, -1746, 1513, -447]]
  ![![1164141, 283546, -53092, -7532, -93490]] where
 M := ![![![1164141, 283546, -53092, -7532, -93490]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![1164141, 283546, -53092, -7532, -93490]] ![![-28742, 8230, -1746, 1513, -447]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-18512185092, 4838845992, -1031852526, 934246323, -204339543]]]
 hmul := by decide  
 g := ![![![![-6170728364, 1612948664, -343950842, 311415441, -68113181]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![48535, 1126, 800, -1968, -1756]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![48535, 1126, 800, -1968, -1756]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![48535, 1126, 800, -1968, -1756], ![-105360, 50879, -9410, 8624, -7872], ![-472320, -90402, 3647, 12668, 34496], ![1087560, -287938, 62992, -69657, 29272], ![465420, 242868, -25724, 68, -67689]]]
  hmulB := by decide  
  f := ![![![-17485, -6102, -3396, -880, -948]], ![![-11376, -3973, -2358, -600, -704]], ![![-42240, -12926, -8197, -1900, -2400]], ![![-66312, -21782, -12484, -3097, -3448]], ![![-48876, -17756, -10028, -2644, -2921]]]
  g := ![![![9707, 1126, 800, -1968, -1756], ![-21072, 50879, -9410, 8624, -7872], ![-94464, -90402, 3647, 12668, 34496], ![217512, -287938, 62992, -69657, 29272], ![93084, 242868, -25724, 68, -67689]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![48535, 1126, 800, -1968, -1756]] ![![48535, 1126, 800, -1968, -1756]]
  ![![-1098440735, 179804340, -47646972, 61293712, -5239944]] where
 M := ![![![-1098440735, 179804340, -47646972, 61293712, -5239944]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-1098440735, 179804340, -47646972, 61293712, -5239944]] ![![48535, 1126, 800, -1968, -1756]]
  ![![14469426165655, -6702601255254, 1251325891476, -1161120259632, 1018688327148]] where
 M := ![![![14469426165655, -6702601255254, 1251325891476, -1161120259632, 1018688327148]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![14469426165655, -6702601255254, 1251325891476, -1161120259632, 1018688327148]] ![![48535, 1126, 800, -1968, -1756]]
  ![![28763393797526785, 143886003310945192, -20135421651616984, 10522157205330720, -32422003729443472]] where
 M := ![![![28763393797526785, 143886003310945192, -20135421651616984, 10522157205330720, -32422003729443472]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![28763393797526785, 143886003310945192, -20135421651616984, 10522157205330720, -32422003729443472]] ![![48535, 1126, 800, -1968, -1756]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-7899807321914591931305, -1730550171127919841810, 92444891732976618600, 194044411372050550480, 624846953290342946100]]]
 hmul := by decide  
 g := ![![![![-1579961464382918386261, -346110034225583968362, 18488978346595323720, 38808882274410110096, 124969390658068589220]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![38, -9, 3, -2, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![38, -9, 3, -2, 1]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![3, 5, 3, 5, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![38, -9, 3, -2, 1], ![60, 37, -3, 2, -8], ![-480, 75, -11, 26, 8], ![210, -259, 63, -28, 56], ![825, 24, 20, -25, -26]]]
  hmulB := by decide  
  f := ![![![-37, 9, -3, 2, -1], ![7, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![-5, 2, 0, 1, 0], ![1, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-3, -5, -3, -5, 7]], ![![5, -2, 0, -1, 1], ![12, 11, 3, 6, -8], ![-72, 5, -5, -2, 8], ![6, -77, -15, -44, 56], ![129, 22, 14, 15, -26]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [4, 6, 0, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 1, 0, 3], [4, 1, 2, 4], [0, 4, 5], [0, 1]]
 g := ![![[1, 0, 0, 1], []], ![[4, 3, 6, 3, 6, 5], [4, 6, 3, 6, 0, 6]], ![[0, 6, 3, 3, 3, 4], [2, 0, 4, 5, 5, 1]], ![[0, 6, 3], [2, 6, 6]]]
 h' := ![![[3, 1, 0, 3], [0, 0, 0, 1], [0, 1]], ![[4, 1, 2, 4], [4, 0, 3, 5], [3, 1, 0, 3]], ![[0, 4, 5], [0, 1, 1, 1], [4, 1, 2, 4]], ![[0, 1], [6, 6, 3], [0, 4, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [0, 5, 6], []]
 b := ![[], [], [2, 2, 3, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [4, 6, 0, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![255558357409, 19187318268, 6824782767, -7942030398, -10763633226]
  a := ![0, -9, -4, -3, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![41121322441, 10429354914, 5587954635, 6553733676, -10763633226]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 2, 0], ![0, 1, 0, 1, 4], ![60, -2, 6, -4, 1]]]
  hmulB := by decide  
  f := ![![![0, 16, 23, 42, -24], ![7, 7, -168, 42, 0]], ![![0, 2, 3, 7, -4], ![1, 7, -28, 7, 0]], ![![0, 13, 19, 35, -20], ![6, 8, -140, 35, 0]], ![![0, -1, -1, -1, 0], ![0, 3, 4, 0, 0]], ![![0, 11, 16, 30, -17], ![5, 8, -120, 30, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 7, 0, 0, 0], ![-6, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![-5, 0, 0, 0, 7]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 1, 1, 2, 0], ![-3, 1, 0, 1, 4], ![3, -2, 6, -4, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0, 0, 0], ![38, -9, 3, -2, 1]] ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![49, 0, 0, 0, 0], ![7, 7, 0, 0, 0]], ![![266, -63, 21, -14, 7], ![98, 28, 0, 0, -7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0]]], ![![![38, -9, 3, -2, 1]], ![![14, 4, 0, 0, -1]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-10, -1, 1, 0, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![-10, -1, 1, 0, 1]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![3, 0, 3, 1, 0], ![1, 10, 1, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-10, -1, 1, 0, 1], ![60, -11, 5, -2, 0], ![0, 63, -11, 10, -8], ![-270, 13, 5, 6, 20], ![285, -72, 32, -17, 6]]]
  hmulB := by decide  
  f := ![![![3061, -1224, 684, -180, 234], ![-2574, -990, 0, 0, 0]], ![![-300, 124, -69, 18, -24], ![264, 99, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![833, -334, 187, -49, 64], ![-704, -270, 0, 0, 0]], ![![1, 1, 0, 0, 0], ![1, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-3, 0, -3, 11, 0], ![-1, -10, -1, 0, 11]], ![![-1, -1, 0, 0, 1], ![6, -1, 1, -2, 0], ![-2, 13, -3, 10, -8], ![-28, -17, -3, 6, 20], ![30, -12, 7, -17, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [10, 6, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 10, 10], [0, 0, 1], [0, 1]]
 g := ![![[4, 0, 3], [10, 4, 1], []], ![[10, 2, 3, 10], [6, 10], [6, 1]], ![[0, 1, 5, 5], [1, 0, 6, 1], [4, 1]]]
 h' := ![![[4, 10, 10], [10, 10, 6], [0, 0, 1], [0, 1]], ![[0, 0, 1], [6, 7, 1], [0, 1], [4, 10, 10]], ![[0, 1], [1, 5, 4], [4, 10, 10], [0, 0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7], []]
 b := ![[], [2, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [10, 6, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1461820414142, 97721403597, -72874225809, 69796838534, 18731351360]
  a := ![3, -125, -62, -1, -434]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-153631116464, -8144737273, -27363281161, 69796838534, 18731351360]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-4, 1, 0, 0, 0], ![0, -4, 1, 0, 0], ![0, 1, -4, 2, 0], ![0, 1, 0, -4, 4], ![60, -2, 6, -4, -4]]]
  hmulB := by decide  
  f := ![![![1045, -1489, 6227, -3080, -80], ![2871, 1023, 17380, 220, 0]], ![![777, -1113, 4651, -2300, -60], ![2135, 759, 12980, 165, 0]], ![![786, -1121, 4690, -2320, -60], ![2160, 771, 13090, 165, 0]], ![![261, -372, 1555, -769, -20], ![717, 255, 4340, 55, 0]], ![![380, -540, 2264, -1120, -29], ![1044, 376, 6320, 80, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-7, 11, 0, 0, 0], ![-6, 0, 11, 0, 0], ![-3, 0, 0, 11, 0], ![-4, 0, 0, 0, 11]], ![![-1, 1, 0, 0, 0], ![2, -4, 1, 0, 0], ![1, 1, -4, 2, 0], ![-1, 1, 0, -4, 4], ![6, -2, 6, -4, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![364, 616, -144, 17, -191]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![364, 616, -144, 17, -191]] 
 ![![11, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![364, 616, -144, 17, -191], ![-11460, 619, -530, 476, 68], ![4080, -11650, 1027, -1332, 1904], ![62850, -326, 152, -3019, -2698], ![-37605, 16190, -3996, 2655, -3036]]]
  hmulB := by decide  
  f := ![![![-485266, 83772, -18404, 20737, 2435]], ![![-383754, 24195, -6114, 12735, 9533]], ![![143638, 56222, -10813, 921, -15377]], ![![-867358, 320558, -67180, 51949, -26550]], ![![-869285, -31438, 3460, 21333, 37196]]]
  g := ![![![-218, 616, -144, 17, -191], ![-1619, 619, -530, 476, 68], ![8487, -11650, 1027, -1332, 1904], ![10532, -326, 152, -3019, -2698], ![-13293, 16190, -3996, 2655, -3036]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0, 0, 0], ![-10, -1, 1, 0, 1]] ![![11, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]]
  ![![485266, -83772, 18404, -20737, -2435]] where
 M := ![![![121, 0, 0, 0, 0], ![-44, 11, 0, 0, 0]], ![![-110, -11, 11, 0, 11], ![100, -7, 1, -2, -4]]]
 hmul := by decide  
 g := ![![![![-4004, -6776, 1584, -187, 2101]], ![![12916, 1845, -46, -408, -832]]], ![![![25705, 2239, 999, -677, -710]], ![![-13220, 1681, -547, 686, 12]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![485266, -83772, 18404, -20737, -2435]] ![![364, 616, -144, 17, -191]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![-22, 0, -1, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![-22, 0, -1, 1, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![1, 3, 1, 0, 0], ![5, 3, 0, 1, 0], ![9, 9, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![-22, 0, -1, 1, 0], ![0, -22, 0, -2, 4], ![240, -10, 2, -16, -8], ![-240, 132, -29, 19, -34], ![-510, -40, -18, 20, 18]]]
  hmulB := by decide  
  f := ![![![681, -26520, -76, -2492, 4704], ![-1300, -15600, -156, 0, 0]], ![![44, 1, 2, -2, 0], ![26, 0, 0, 0, 0]], ![![53, -1309, -3, -124, 232], ![-56, -770, -8, 0, 0]], ![![267, -10149, -29, -954, 1800], ![-497, -5970, -60, 0, 0]], ![![463, -18207, -53, -1711, 3229], ![-905, -10710, -108, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-1, -3, 13, 0, 0], ![-5, -3, 0, 13, 0], ![-9, -9, 0, 0, 13]], ![![-2, 0, -1, 1, 0], ![-2, -4, 0, -2, 4], ![30, 8, 2, -16, -8], ![0, 36, -29, 19, -34], ![-58, -16, -18, 20, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [6, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 12], [0, 1]]
 g := ![![[4, 3], [4], [2, 1]], ![[10, 10], [4], [4, 12]]]
 h' := ![![[2, 12], [3, 4], [1, 11], [0, 1]], ![[0, 1], [11, 9], [10, 2], [2, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [9, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [6, 11, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![266163, -98093, 34417, -23383, 25743]
  a := ![1, -9, -4, -2, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8998, -27914, 34417, -23383, 25743]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![457, 102, -8, -10, -36]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![457, 102, -8, -10, -36]] 
 ![![13, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![457, 102, -8, -10, -36], ![-2160, 511, -114, 128, -40], ![-2400, -2066, 271, -68, 512], ![16440, -1866, 560, -817, -116], ![-1200, 3976, -612, 364, -807]]]
  hmulB := by decide  
  f := ![![![-16042571, -5314166, -3159724, -780210, -913476]], ![![-5450087, -1805363, -1073442, -265058, -310332]], ![![-29212404, -9676726, -5753637, -1420708, -1663376]], ![![-22497000, -7452222, -4430980, -1094113, -1280996]], ![![-21863061, -7242226, -4306120, -1063282, -1244899]]]
  g := ![![![43, 102, -8, -10, -36], ![-91, 511, -114, 128, -40], ![-394, -2066, 271, -68, 512], ![918, -1866, 560, -817, -116], ![353, 3976, -612, 364, -807]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16883, -753, 443, -778, -360]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![16883, -753, 443, -778, -360]] 
 ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![16883, -753, 443, -778, -360], ![-21600, 17268, -2913, 2326, -3112], ![-186720, -15963, -1404, 6622, 9304], ![289920, -108689, 21387, -21175, 14800], ![227400, 60816, -4244, -4688, -20397]]]
  hmulB := by decide  
  f := ![![![608831, 201603, 119901, 29598, 34664]], ![![253654, 84016, 49953, 12334, 14440]], ![![967923, 320632, 190651, 47076, 55120]], ![![994161, 329228, 195812, 48339, 56616]], ![![1204417, 398857, 237179, 58554, 68563]]]
  g := ![![![1592, -753, 443, -778, -360], ![-205, 17268, -2913, 2326, -3112], ![-20336, -15963, -1404, 6622, 9304], ![16580, -108689, 21387, -21175, 14800], ![29415, 60816, -4244, -4688, -20397]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2

def I13N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![-6, 1, 0, 0, 0]] i)))

def SI13N3: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![-6, 1, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![-6, 1, 0, 0, 0], ![0, -6, 1, 0, 0], ![0, 1, -6, 2, 0], ![0, 1, 0, -6, 4], ![60, -2, 6, -4, -6]]]
  hmulB := by decide  
  f := ![![![247, -68, 267, -90, 0], ![533, 39, 585, 0, 0]], ![![145, -37, 148, -50, 0], ![313, 26, 325, 0, 0]], ![![57, -13, 59, -20, 0], ![123, 14, 130, 0, 0]], ![![228, -66, 247, -83, 0], ![492, 29, 540, 0, 0]], ![![-24, 10, -46, 20, -3], ![-52, -2, -100, 10, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-7, 13, 0, 0, 0], ![-3, 0, 13, 0, 0], ![-12, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![-1, 1, 0, 0, 0], ![3, -6, 1, 0, 0], ![-1, 1, -6, 2, 0], ![5, 1, 0, -6, 4], ![8, -2, 6, -4, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N3 : Nat.card (O ⧸ I13N3) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N3)

lemma isPrimeI13N3 : Ideal.IsPrime I13N3 := prime_ideal_of_norm_prime hp13.out _ NI13N3
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0], ![-22, 0, -1, 1, 0]] ![![457, 102, -8, -10, -36]]
  ![![13, 0, 0, 0, 0], ![63, -14, 4, -3, 1]] where
 M := ![![![5941, 1326, -104, -130, -468]], ![![8786, -2044, 465, -529, 164]]]
 hmul := by decide  
 g := ![![![![638191, 2424764, -361832, 203224, -431162], ![290186, -442871, 0, 0, 0]]], ![![![1007222, 3826816, -571051, 320735, -680456], ![458020, -699006, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0], ![63, -14, 4, -3, 1]] ![![16883, -753, 443, -778, -360]]
  ![![13, 0, 0, 0, 0], ![-71, 1, 0, 3, 2]] where
 M := ![![![219479, -9789, 5759, -10114, -4680]], ![![-23211, 33840, -5330, 3747, -6693]]]
 hmul := by decide  
 g := ![![![![553, -523, 443, -88, 100], ![-2990, 0, 0, 0, 0]]], ![![![-5, 2578, -410, 213, -565], ![326, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N2 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0], ![-71, 1, 0, 3, 2]] ![![13, 0, 0, 0, 0], ![-6, 1, 0, 0, 0]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![169, 0, 0, 0, 0], ![-78, 13, 0, 0, 0]], ![![-923, 13, 0, 39, 26], ![546, -78, 13, -26, 0]]]
 hmul := by decide  
 g := ![![![![13, 0, 0, 0, 0]], ![![-6, 1, 0, 0, 0]]], ![![![-71, 1, 0, 3, 2]], ![![42, -6, 1, -2, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2, I13N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
    exact isPrimeI13N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1 ⊙ MulI13N2)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-118, 57, -15, 8, -8]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![-118, 57, -15, 8, -8]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![2, 12, 4, 16, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-118, 57, -15, 8, -8], ![-480, -109, 9, 2, 32], ![1920, -533, 83, -110, 8], ![480, 993, -247, 66, -236], ![-3420, 220, -108, 112, 58]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![14, -6, 2, 0, 1], ![2, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-2, -12, -4, -16, 17]], ![![-6, 9, 1, 8, -8], ![-32, -29, -7, -30, 32], ![112, -37, 3, -14, 8], ![56, 225, 41, 226, -236], ![-208, -28, -20, -48, 58]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [6, 11, 2, 9, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 3, 14, 6], [8, 7, 15, 1], [2, 6, 5, 10], [0, 1]]
 g := ![![[6, 4, 12, 1], [4, 4, 13], [1], []], ![[16, 15, 9, 12, 11, 7], [12, 7, 8], [14, 8, 15], [0, 14, 2]], ![[16, 3, 6, 5, 7, 4], [14, 6, 16], [16, 4, 16], [14, 4, 1]], ![[11, 12, 16, 0, 10, 5], [1, 7, 13], [6, 4, 2], [5, 16, 15]]]
 h' := ![![[15, 3, 14, 6], [12, 13, 15, 16], [11, 6, 15, 8], [0, 0, 1], [0, 1]], ![[8, 7, 15, 1], [13, 13, 5, 2], [0, 16, 13, 5], [4, 6, 8, 10], [15, 3, 14, 6]], ![[2, 6, 5, 10], [5, 12, 0, 2], [15, 9, 11, 13], [14, 2, 7, 13], [8, 7, 15, 1]], ![[0, 1], [13, 13, 14, 14], [11, 3, 12, 8], [8, 9, 1, 11], [2, 6, 5, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [15, 16, 7], []]
 b := ![[], [], [8, 6, 9, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [6, 11, 2, 9, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![173012525952239, 54465579115721, -1976794853613, -1256475843905, -17063448154645]
  a := ![1, 45, 23, -1, 163]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![12184671897737, 15248644527733, 3898646927351, 15985805566495, -17063448154645]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![4, 1, 0, 0, 0], ![0, 4, 1, 0, 0], ![0, 1, 4, 2, 0], ![0, 1, 0, 4, 4], ![60, -2, 6, -4, 4]]]
  hmulB := by decide  
  f := ![![![-771, -731, -2488, -1156, 96], ![3281, -272, 10642, -408, 0]], ![![-196, -185, -628, -292, 24], ![834, -68, 2686, -102, 0]], ![![-203, -185, -620, -288, 24], ![863, -67, 2652, -102, 0]], ![![-583, -549, -1866, -867, 72], ![2481, -206, 7982, -306, 0]], ![![-137, -133, -440, -204, 17], ![583, -32, 1878, -72, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-4, 17, 0, 0, 0], ![-1, 0, 17, 0, 0], ![-13, 0, 0, 17, 0], ![-3, 0, 0, 0, 17]], ![![0, 1, 0, 0, 0], ![-1, 4, 1, 0, 0], ![-2, 1, 4, 2, 0], ![-4, 1, 0, 4, 4], ![6, -2, 6, -4, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0, 0], ![-118, 57, -15, 8, -8]] ![![17, 0, 0, 0, 0], ![4, 1, 0, 0, 0]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![289, 0, 0, 0, 0], ![68, 17, 0, 0, 0]], ![![-2006, 969, -255, 136, -136], ![-952, 119, -51, 34, 0]]]
 hmul := by decide  
 g := ![![![![17, 0, 0, 0, 0]], ![![4, 1, 0, 0, 0]]], ![![![-118, 57, -15, 8, -8]], ![![-56, 7, -3, 2, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [13, 16, 11, 11, 11, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 0, 2, 13, 15], [6, 16, 5, 4, 18], [16, 18, 18, 4, 17], [6, 3, 13, 17, 7], [0, 1]]
 g := ![![[3, 1, 3, 8, 16], [13, 2, 15, 8, 1], [], []], ![[7, 18, 4, 8, 1, 14, 17, 2], [6, 15, 16, 17, 7, 8, 3, 12], [9, 11, 9, 17], [14, 17, 5, 16]], ![[17, 4, 0, 18, 0, 6, 1, 8], [14, 14, 7, 10, 18, 11, 15, 18], [18, 18, 7, 11], [14, 14, 0, 1]], ![[4, 9, 1, 18, 3, 13, 6, 6], [9, 3, 8, 2, 2, 11, 5, 9], [10, 5, 13, 7], [0, 9, 16, 4]], ![[18, 7, 17, 4, 12, 0, 3, 17], [12, 2, 6, 0, 11, 2, 4, 17], [16, 9, 13, 4], [16, 13, 3, 11]]]
 h' := ![![[18, 0, 2, 13, 15], [2, 13, 10, 4, 4], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[6, 16, 5, 4, 18], [13, 8, 6, 8, 3], [2, 6, 15, 10, 4], [9, 11, 18, 10, 6], [18, 0, 2, 13, 15]], ![[16, 18, 18, 4, 17], [12, 3, 10, 10, 12], [11, 7, 15, 0, 1], [6, 14, 14, 1, 7], [6, 16, 5, 4, 18]], ![[6, 3, 13, 17, 7], [14, 0, 1, 10, 15], [8, 0, 14, 4, 9], [9, 3, 16, 8, 8], [16, 18, 18, 4, 17]], ![[0, 1], [1, 14, 11, 6, 4], [2, 6, 13, 5, 4], [18, 10, 8, 0, 17], [6, 3, 13, 17, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 4, 7], [], [], []]
 b := ![[], [12, 18, 1, 16], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [13, 16, 11, 11, 11, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![499859057110207, -123682167421760, 29225921073092, -32285557420370, 9914972687060]
  a := ![-1, -6, -4, 5, -34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![26308371426853, -6509587759040, 1538206372268, -1699239864230, 521840667740]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 2476099 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21142, -7010, -4164, -1029, -1203]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-21142, -7010, -4164, -1029, -1203]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![17, 20, 4, 1, 0], ![12, 0, 20, 0, 1]] where
  M :=![![![-21142, -7010, -4164, -1029, -1203], ![-72180, -23929, -14228, -3516, -4116], ![-246960, -81692, -48625, -11992, -14064], ![-385830, -127760, -75924, -18739, -21926], ![-310845, -103178, -61272, -15157, -17710]]]
  hmulB := by decide  
  f := ![![![-1124, -278, 52, 7, 91]], ![![5460, -1247, 268, -260, 28]], ![![1680, 5412, -1079, 424, -1040]], ![![2734, -254, 60, -98, -53]], ![![1359, 4194, -836, 327, -808]]]
  g := ![![![469, 590, 1044, -1029, -1203], ![1608, 2017, 3572, -3516, -4116], ![5464, 6876, 12201, -11992, -14064], ![8515, 10740, 19024, -18739, -21926], ![6928, 8694, 15372, -15157, -17710]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [21, 21, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 3, 17], [5, 19, 6], [0, 1]]
 g := ![![[11, 17, 1], [2, 3, 8], [18, 4, 1], []], ![[22, 11, 20, 15], [11, 1, 17, 14], [19, 19, 21, 19], [16, 13]], ![[8, 4, 16, 4], [1, 8, 19, 4], [12, 16, 10, 8], [4, 13]]]
 h' := ![![[22, 3, 17], [4, 18, 1], [13, 21, 13], [0, 0, 1], [0, 1]], ![[5, 19, 6], [19, 14, 3], [7, 3, 6], [10, 6, 19], [22, 3, 17]], ![[0, 1], [12, 14, 19], [18, 22, 4], [10, 17, 3], [5, 19, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 1], []]
 b := ![[], [3, 8, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [21, 21, 19, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39948741, 214245710, -33265960, 23761002, -55352764]
  a := ![0, -2, 4, -18, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13054125, -11346710, 42554144, 23761002, -55352764]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1124, 278, -52, -7, -91]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![1124, 278, -52, -7, -91]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![17, 15, 1, 0, 0], ![22, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![1124, 278, -52, -7, -91], ![-5460, 1247, -268, 260, -28], ![-1680, -5412, 1079, -424, 1040], ![33930, -2176, 548, -1131, -834], ![-11145, 8442, -1728, 1043, -1124]]]
  hmulB := by decide  
  f := ![![![21142, 7010, 4164, 1029, 1203]], ![![72180, 23929, 14228, 3516, 4116]], ![![73438, 24339, 14471, 3575, 4185]], ![![36998, 12260, 7284, 1799, 2104]], ![![13515, 4486, 2664, 659, 770]]]
  g := ![![![94, 46, -52, -7, -91], ![-288, 229, -268, 260, -28], ![-465, -939, 1079, -424, 1040], ![2152, -452, 548, -1131, -834], ![-205, 1494, -1728, 1043, -1124]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [12, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 22], [0, 1]]
 g := ![![[12, 2], [9, 13], [20, 13], [1]], ![[0, 21], [0, 10], [11, 10], [1]]]
 h' := ![![[17, 22], [7, 5], [13, 6], [11, 17], [0, 1]], ![[0, 1], [0, 18], [0, 17], [1, 6], [17, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [12, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [12, 6, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![498904, -135886, 49065, -40136, 24470]
  a := ![13, -7, -4, 3, -33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![23817, -37907, 49065, -40136, 24470]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-21142, -7010, -4164, -1029, -1203]] ![![1124, 278, -52, -7, -91]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB1253I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1253I0 : PrimesBelowBoundCertificateInterval O 1 23 1253 where
  m := 9
  g := ![5, 5, 5, 2, 3, 4, 2, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1253I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1, I13N2, I13N3]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
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
    · exact ![1331, 11, 11]
    · exact ![169, 13, 13, 13]
    · exact ![83521, 17]
    · exact ![2476099]
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
      exact NI2N1
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
      exact NI13N2
      exact NI13N3
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I11N1, I11N2, I13N0, I13N1, I13N2, I13N3, I17N1, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N1, I11N2], [I13N0, I13N1, I13N2, I13N3], [I17N1], [], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
