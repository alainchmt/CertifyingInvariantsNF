
import IdealArithmetic.Examples.NF5_3_1518750000_3.RI5_3_1518750000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39478, 42951, -9591, 7680, -3555]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-39478, 42951, -9591, 7680, -3555]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-39478, 42951, -9591, 7680, -3555], ![85320, -92803, 20718, -16596, 7680], ![-184320, 200520, -44773, 35856, -16596], ![158544, -172470, 38508, -30841, 14274], ![-51264, 55764, -12450, 9972, -4615]]]
  hmulB := by decide  
  f := ![![![121, -15, -51, -24, -9]], ![![108, -7, -54, -36, -12]], ![![288, -72, -85, 0, -36]], ![![0, -6, 12, 23, 18]], ![![-144, 180, -114, -252, 41]]]
  g := ![![![-19739, 42951, -9591, 7680, -3555], ![42660, -92803, 20718, -16596, 7680], ![-92160, 200520, -44773, 35856, -16596], ![79272, -172470, 38508, -30841, 14274], ![-25632, 55764, -12450, 9972, -4615]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 8, -3, -12, -3]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-13, 8, -3, -12, -3]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-13, 8, -3, -12, -3], ![72, -58, 23, 72, -12], ![288, -108, -13, 138, 72], ![-432, 282, -89, -367, -13], ![-696, 111, 154, -162, -334]]]
  hmulB := by decide  
  f := ![![![18958, -20647, 4615, -3690, 1710]], ![![-20520, 22304, -4976, 3990, -1845]], ![![44280, -48195, 10766, -8616, 3990]], ![![-28621, 31129, -6949, 5567, -2576]], ![![21803, -23726, 5299, -4242, 1964]]]
  g := ![![![1, 8, -3, -12, -3], ![6, -58, 23, 72, -12], ![39, -108, -13, 138, 72], ![-26, 282, -89, -367, -13], ![-100, 111, 154, -162, -334]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54745, -5474, 11529, 3691, 3015]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-54745, -5474, 11529, 3691, 3015]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-54745, -5474, 11529, 3691, 3015], ![-72360, -9520, 13362, 3831, 3691], ![-88584, -16995, 11971, 2241, 3831], ![28968, 3311, -5760, -1763, -1542], ![35328, -1224, -11347, -4563, -2558]]]
  hmulB := by decide  
  f := ![![![406, -229, 55, 311, 43]], ![![-313, 411, -246, -533, 177]], ![![-3529, 1702, -201, -2219, -667]], ![![4823, -3366, 1185, 4367, -30]], ![![11567, -4205, -513, 5653, 3390]]]
  g := ![![![-33753, -5474, 11529, 3691, 3015], ![-41862, -9520, 13362, 3831, 3691], ![-44816, -16995, 11971, 2241, 3831], ![17361, 3311, -5760, -1763, -1542], ![27510, -1224, -11347, -4563, -2558]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-39478, 42951, -9591, 7680, -3555]] ![![-13, 8, -3, -12, -3]]
  ![![-2, 1, 0, 0, 0]] where
 M := ![![![-2, 1, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-2, 1, 0, 0, 0]] ![![-13, 8, -3, -12, -3]]
  ![![98, -74, 29, 96, -6]] where
 M := ![![![98, -74, 29, 96, -6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![98, -74, 29, 96, -6]] ![![-54745, -5474, 11529, 3691, 3015]]
  ![![-10346, 373, 3335, 1343, 751]] where
 M := ![![![-10346, 373, 3335, 1343, 751]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-10346, 373, 3335, 1343, 751]] ![![-54745, -5474, 11529, 3691, 3015]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![309409202, -67832, -90629000, -35078910, -21032026]]]
 hmul := by decide  
 g := ![![![![154704601, -33916, -45314500, -17539455, -10516013]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2008323, 2184855, -487891, 390671, -180839]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-2008323, 2184855, -487891, 390671, -180839]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-2008323, 2184855, -487891, 390671, -180839], ![4340136, -4720908, 1053867, -844257, 390671], ![-9376104, 10200201, -2277734, 1823895, -844257], ![8065080, -8773427, 1958889, -1568858, 726111], ![-2607528, 2836665, -633413, 507231, -234782]]]
  hmulB := by decide  
  f := ![![![2463, -1049, 23, 1395, 589]], ![![-4712, 3766, -1577, -4883, 465]], ![![-11160, 2263, 2058, -3183, -4883]], ![![25112, -15199, 4163, 19890, 1911]], ![![18312, 10443, -15697, -12603, 20740]]]
  g := ![![![-669441, 2184855, -487891, 390671, -180839], ![1446712, -4720908, 1053867, -844257, 390671], ![-3125368, 10200201, -2277734, 1823895, -844257], ![2688360, -8773427, 1958889, -1568858, 726111], ![-869176, 2836665, -633413, 507231, -234782]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48811, -2148, 12524, 4544, 3040]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-48811, -2148, 12524, 4544, 3040]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-48811, -2148, 12524, 4544, 3040], ![-72960, -3211, 18720, 6792, 4544], ![-109056, -4800, 27981, 10152, 6792], ![27360, 1204, -7020, -2547, -1704], ![13920, 612, -3572, -1296, -867]]]
  hmulB := by decide  
  f := ![![![-9, 12, -4, 0, 0]], ![![0, -3, 0, -8, 0]], ![![0, 0, 5, 24, -8]], ![![29, -16, 0, 5, 8]], ![![-96, 92, -44, -112, 21]]]
  g := ![![![-17785, -2148, 12524, 4544, 3040], ![-26584, -3211, 18720, 6792, 4544], ![-39736, -4800, 27981, 10152, 6792], ![9969, 1204, -7020, -2547, -1704], ![5072, 612, -3572, -1296, -867]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-2008323, 2184855, -487891, 390671, -180839]] ![![-2008323, 2184855, -487891, 390671, -180839]]
  ![![21712781493945, -23619483424048, 5273502118098, -4223669108440, 1954776255268]] where
 M := ![![![21712781493945, -23619483424048, 5273502118098, -4223669108440, 1954776255268]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![21712781493945, -23619483424048, 5273502118098, -4223669108440, 1954776255268]] ![![-48811, -2148, 12524, 4544, 3040]]
  ![![-1215207290643, 1321920416124, -295144079738, 236387652312, -109403695292]] where
 M := ![![![-1215207290643, 1321920416124, -295144079738, 236387652312, -109403695292]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-1215207290643, 1321920416124, -295144079738, 236387652312, -109403695292]] ![![-48811, -2148, 12524, 4544, 3040]]
  ![![68991867441, -73941265656, 16267032154, -13321207992, 6062010756]] where
 M := ![![![68991867441, -73941265656, 16267032154, -13321207992, 6062010756]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![68991867441, -73941265656, 16267032154, -13321207992, 6062010756]] ![![-48811, -2148, 12524, 4544, 3040]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-26909818925115, -1179665420748, 6902859135246, 2505630559608, 1675423362660]]]
 hmul := by decide  
 g := ![![![![-8969939641705, -393221806916, 2300953045082, 835210186536, 558474454220]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, -38, 8, -7, 3]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![37, -38, 8, -7, 3]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![37, -38, 8, -7, 3], ![-72, 82, -19, 15, -7], ![168, -177, 38, -33, 15], ![-144, 154, -34, 26, -13], ![48, -54, 14, -3, 2]]]
  hmulB := by decide  
  f := ![![![-1519, 216, 622, 271, 131]], ![![-1844, 262, 755, 329, 159]], ![![-2516, 357, 1030, 449, 217]], ![![-406, 58, 166, 72, 35]], ![![-886, 126, 362, 157, 76]]]
  g := ![![![33, -38, 8, -7, 3], ![-68, 82, -19, 15, -7], ![152, -177, 38, -33, 15], ![-130, 154, -34, 26, -13], ![42, -54, 14, -3, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![37, -38, 8, -7, 3]] ![![37, -38, 8, -7, 3]]
  ![![6601, -7178, 1602, -1284, 594]] where
 M := ![![![6601, -7178, 1602, -1284, 594]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![6601, -7178, 1602, -1284, 594]] ![![37, -38, 8, -7, 3]]
  ![![1243597, -1352800, 302038, -241909, 111959]] where
 M := ![![![1243597, -1352800, 302038, -241909, 111959]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![1243597, -1352800, 302038, -241909, 111959]] ![![37, -38, 8, -7, 3]]
  ![![234366001, -254946784, 56921752, -45589944, 21099696]] where
 M := ![![![234366001, -254946784, 56921752, -45589944, 21099696]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![234366001, -254946784, 56921752, -45589944, 21099696]] ![![37, -38, 8, -7, 3]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![44168302165, -48046929390, 10727397320, -8591819215, 3976420435]]]
 hmul := by decide  
 g := ![![![![8833660433, -9609385878, 2145479464, -1718363843, 795284087]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11221, 7858, 268, 2107, -201]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-11221, 7858, 268, 2107, -201]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![2, 4, 4, 1, 0], ![0, 2, 1, 0, 1]] where
  M :=![![![-11221, 7858, 268, 2107, -201], ![4824, -14236, 7359, -1095, 2107], ![-50568, 36429, 508, 9513, -1095], ![29664, -29380, 5216, -5720, 2133], ![-12768, 9948, -388, 2415, -416]]]
  hmulB := by decide  
  f := ![![![-10459, -464, 2686, 979, 653]], ![![-15672, -664, 4003, 1425, 979]], ![![-23496, -987, 6004, 2121, 1425]], ![![-24506, -1056, 6276, 2250, 1509]], ![![-7368, -317, 1882, 678, 477]]]
  g := ![![![-2205, -24, -1137, 2107, -201], ![1002, -2010, 1376, -1095, 2107], ![-9942, 81, -5207, 9513, -1095], ![5872, -1538, 3709, -5720, 2133], ![-2514, 160, -1376, 2415, -416]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [5, 5, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2, 3], [3, 4, 4], [0, 1]]
 g := ![![[1, 5, 4], [1]], ![[4, 3, 6, 5], [0, 4, 0, 6]], ![[4, 5, 3, 1], [6, 0, 1, 1]]]
 h' := ![![[2, 2, 3], [2, 2, 5], [0, 1]], ![[3, 4, 4], [1, 4, 5], [2, 2, 3]], ![[0, 1], [4, 1, 4], [3, 4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 3], []]
 b := ![[], [5, 5, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [5, 5, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3857189, -3143477, 1341553, 4071151, -440759]
  a := ![0, -1, -4, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-612159, -2649509, -2071756, 4071151, -440759]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1763, -79, 453, 164, 110]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-1763, -79, 453, 164, 110]] 
 ![![7, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-1763, -79, 453, 164, 110], ![-2640, -113, 676, 246, 164], ![-3936, -180, 1013, 366, 246], ![984, 49, -255, -91, -62], ![504, 21, -129, -48, -31]]]
  hmulB := by decide  
  f := ![![![-509, 71, 209, 92, 44]], ![![-369, 52, 151, 66, 32]], ![![-679, 97, 276, 118, 58]], ![![-94, 11, 41, 21, 8]], ![![-415, 52, 178, 88, 39]]]
  g := ![![![-667, -79, 453, 164, 110], ![-999, -113, 676, 246, 164], ![-1489, -180, 1013, 366, 246], ![372, 49, -255, -91, -62], ![191, 21, -129, -48, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, 21, -5, -27, 1]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![-41, 21, -5, -27, 1]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-41, 21, -5, -27, 1], ![-24, -26, 29, 33, -27], ![648, -429, 136, 561, 33], ![-456, 405, -187, -524, 77], ![-2568, 1485, -365, -1947, -260]]]
  hmulB := by decide  
  f := ![![![45361, -49287, 10977, -8823, 4073]], ![![11956, -12956, 2869, -2325, 1067]], ![![62651, -68076, 15163, -12186, 5626]], ![![-25992, 28269, -6309, 5056, -2339]], ![![40811, -44346, 9878, -7938, 3665]]]
  g := ![![![-15, 21, -5, -27, 1], ![10, -26, 29, 33, -27], ![217, -429, 136, 561, 33], ![-218, 405, -187, -524, 77], ![-769, 1485, -365, -1947, -260]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-11221, 7858, 268, 2107, -201]] ![![-1763, -79, 453, 164, 110]]
  ![![-45361, 49287, -10977, 8823, -4073]] where
 M := ![![![-45361, 49287, -10977, 8823, -4073]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-45361, 49287, -10977, 8823, -4073]] ![![-41, 21, -5, -27, 1]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2755, -361, 823, 238, 206]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-2755, -361, 823, 238, 206]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![8, 9, 0, 1, 0], ![2, 2, 8, 0, 1]] where
  M :=![![![-2755, -361, 823, 238, 206], ![-4944, 335, 1046, 516, 238], ![-5712, -1374, 2005, 444, 516], ![792, 1025, -647, 13, -184], ![1080, -267, -129, -126, -23]]]
  hmulB := by decide  
  f := ![![![-137, 81, -21, -106, -12]], ![![288, -317, 172, 408, -106]], ![![2544, -1302, 215, 1716, 408]], ![![-128, -10, 55, 9, -88]], ![![1138, -689, 189, 902, 87]]]
  g := ![![![-461, -265, -75, 238, 206], ![-868, -435, -78, 516, 238], ![-936, -582, -193, 444, 516], ![96, 116, 75, 13, -184], ![194, 83, 5, -126, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [6, 1, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 7, 4], [4, 3, 7], [0, 1]]
 g := ![![[1, 5, 1], [3, 9, 1], []], ![[9, 7, 5, 1], [4, 2, 1, 3], [2, 5]], ![[7, 3, 0, 2], [8, 6, 5, 2], [10, 5]]]
 h' := ![![[5, 7, 4], [4, 9, 1], [0, 0, 1], [0, 1]], ![[4, 3, 7], [7, 2, 6], [2, 5, 3], [5, 7, 4]], ![[0, 1], [7, 0, 4], [0, 6, 7], [4, 3, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 3], []]
 b := ![[], [9, 1, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [6, 1, 2, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![921798, -1020994, -166454, -365128, -168754]
  a := ![3, -64, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![380030, 236606, 107598, -365128, -168754]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-137, 81, -21, -106, -12]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-137, 81, -21, -106, -12]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![3, 3, 1, 0, 0], ![8, 3, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-137, 81, -21, -106, -12], ![288, -317, 172, 408, -106], ![2544, -1302, 215, 1716, 408], ![-2904, 2095, -775, -2725, 82], ![-8136, 3309, 57, -4410, -2071]]]
  hmulB := by decide  
  f := ![![![-2755, -361, 823, 238, 206]], ![![-4944, 335, 1046, 516, 238]], ![![-2619, -132, 692, 246, 168]], ![![-3280, -78, 825, 315, 198]], ![![-1655, -254, 512, 140, 129]]]
  g := ![![![78, 42, -21, -106, -12], ![-250, -187, 172, 408, -106], ![-1335, -645, 215, 1716, 408], ![1877, 1145, -775, -2725, 82], ![3770, 1488, 57, -4410, -2071]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [8, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 10], [0, 1]]
 g := ![![[7, 9], [4, 1], [1]], ![[9, 2], [3, 10], [1]]]
 h' := ![![[10, 10], [1, 8], [3, 10], [0, 1]], ![[0, 1], [4, 3], [4, 1], [10, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [5, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [8, 1, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1142, 1247, -621, -1519, 497]
  a := ![1, -3, -2, -1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![854, 697, -621, -1519, 497]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-2755, -361, 823, 238, 206]] ![![-137, 81, -21, -106, -12]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1723, 251, 699, 307, 147]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-1723, 251, 699, 307, 147]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![3, 2, 1, 0, 0], ![4, 1, 0, 1, 0], ![12, 7, 0, 0, 1]] where
  M :=![![![-1723, 251, 699, 307, 147], ![-3528, 482, 1453, 627, 307], ![-7368, 1077, 2986, 1311, 627], ![1176, -199, -457, -206, -95], ![-1560, 231, 631, 279, 136]]]
  hmulB := by decide  
  f := ![![![-130711, -5751, 33539, 12169, 8141]], ![![-195384, -8596, 50133, 18189, 12169]], ![![-82689, -3638, 21217, 7698, 5150]], ![![-49612, -2183, 12730, 4619, 3090]], ![![-222996, -9811, 57218, 20760, 13889]]]
  g := ![![![-524, -191, 699, 307, 147], ![-1083, -400, 1453, 627, 307], ![-2238, -815, 2986, 1311, 627], ![347, 122, -457, -206, -95], ![-477, -174, 631, 279, 136]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [11, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 12], [0, 1]]
 g := ![![[4, 1], [1], [8, 1]], ![[12, 12], [1], [3, 12]]]
 h' := ![![[8, 12], [11, 1], [3, 1], [0, 1]], ![[0, 1], [6, 12], [11, 12], [8, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [3, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [11, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10471, 8700, -2792, -10007, 1743]
  a := ![1, 19, 3, -1, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1309, 930, -2792, -10007, 1743]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15155, 2428, 6458, 2838, 1348]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-15155, 2428, 6458, 2838, 1348]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![11, 9, 1, 0, 0], ![4, 12, 0, 1, 0], ![8, 6, 0, 0, 1]] where
  M :=![![![-15155, 2428, 6458, 2838, 1348], ![-32352, 5065, 13572, 5970, 2838], ![-68112, 10218, 28459, 12438, 5970], ![10176, -1536, -4350, -1889, -912], ![-15696, 2106, 6360, 2754, 1345]]]
  hmulB := by decide  
  f := ![![![673, -856, 502, 1098, -352]], ![![8448, -4607, 960, 6054, 1098]], ![![4391, -1997, 153, 2646, 928]], ![![7156, -4648, 1462, 6067, 260]], ![![15224, -11660, 4652, 15138, -1039]]]
  g := ![![![-8333, -7526, 6458, 2838, 1348], ![-17556, -15827, 13572, 5970, 2838], ![-36821, -33153, 28459, 12438, 5970], ![5606, 5058, -4350, -1889, -912], ![-8264, -7404, 6360, 2754, 1345]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [2, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 12], [0, 1]]
 g := ![![[2, 1], [1], [9, 1]], ![[11, 12], [1], [5, 12]]]
 h' := ![![[9, 12], [10, 12], [8, 1], [0, 1]], ![[0, 1], [1, 1], [4, 12], [9, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [6, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [2, 4, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7609, 7847, -4083, -10212, 2515]
  a := ![-1, 0, -2, 2, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4464, 11696, -4083, -10212, 2515]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, 8, 28, 12, 6]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![-73, 8, 28, 12, 6]] 
 ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-73, 8, 28, 12, 6], ![-144, 17, 56, 24, 12], ![-288, 36, 113, 48, 24], ![48, -6, -18, -7, -4], ![-48, 6, 22, 12, 5]]]
  hmulB := by decide  
  f := ![![![59, -68, 16, -12, 6]], ![![-2, 1, 0, 0, 0]], ![![63, -72, 17, -12, 6]], ![![36, -42, 10, -7, 4]], ![![40, -46, 10, -12, 5]]]
  g := ![![![-41, 8, 28, 12, 6], ![-82, 17, 56, 24, 12], ![-165, 36, 113, 48, 24], ![26, -6, -18, -7, -4], ![-34, 6, 22, 12, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-1723, 251, 699, 307, 147]] ![![-15155, 2428, 6458, 2838, 1348]]
  ![![-28801855, 4068283, 11771749, 5127673, 2480495]] where
 M := ![![![-28801855, 4068283, 11771749, 5127673, 2480495]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-28801855, 4068283, 11771749, 5127673, 2480495]] ![![-73, 8, 28, 12, 6]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-1746496505, 246645867, 713852321, 310932713, 150422025]]]
 hmul := by decide  
 g := ![![![![-134345885, 18972759, 54911717, 23917901, 11570925]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-238337, 33660, 97416, 42431, 20529]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-238337, 33660, 97416, 42431, 20529]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![2, 0, 4, 5, 1]] where
  M :=![![![-238337, 33660, 97416, 42431, 20529], ![-492696, 69598, 201361, 87681, 42431], ![-1018344, 143769, 416276, 181365, 87681], ![158448, -22406, -64720, -28132, -13613], ![-216288, 30804, 88134, 38079, 18710]]]
  hmulB := by decide  
  f := ![![![-168769, 183626, -41006, 32833, -15199]], ![![364776, -396754, 88571, -70953, 32833]], ![![-787992, 857271, -191420, 153291, -70953]], ![![677808, -737350, 164632, -131852, 61025]], ![![-18802, 20470, -4574, 3659, -1695]]]
  g := ![![![-16435, 1980, 900, -3542, 20529], ![-33974, 4094, 1861, -7322, 42431], ![-70218, 8457, 3856, -15120, 87681], ![10922, -1318, -604, 2349, -13613], ![-14924, 1812, 782, -3263, 18710]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [9, 15, 0, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 5, 9, 16], [10, 2, 10, 14], [6, 9, 15, 4], [0, 1]]
 g := ![![[0, 11, 16, 2], [14, 16, 1], [1], []], ![[14, 15, 9, 2, 15, 1], [11, 11, 1], [8, 10, 4], [5, 15, 1]], ![[16, 12, 16, 4, 9, 12], [4, 14, 1], [9, 8, 2], [4, 16, 9]], ![[3, 1, 9, 0, 11, 8], [1, 4, 9], [4, 0, 16], [6, 2, 16]]]
 h' := ![![[0, 5, 9, 16], [6, 1, 10, 6], [8, 2, 0, 16], [0, 0, 1], [0, 1]], ![[10, 2, 10, 14], [7, 14, 1, 13], [15, 7, 11, 16], [6, 11, 12, 2], [0, 5, 9, 16]], ![[6, 9, 15, 4], [7, 1, 8, 9], [3, 0, 1, 16], [13, 6, 2, 11], [10, 2, 10, 14]], ![[0, 1], [9, 1, 15, 6], [16, 8, 5, 3], [16, 0, 2, 4], [6, 9, 15, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [8, 7, 11], []]
 b := ![[], [], [15, 4, 5, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [9, 15, 0, 1, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![338851401, -75217928, -56802394, 104943514, 142659804]
  a := ![0, 0, -6, -10, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3148929, -4424584, -36908330, -35785618, 142659804]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-168769, 183626, -41006, 32833, -15199]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-168769, 183626, -41006, 32833, -15199]] 
 ![![17, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-168769, 183626, -41006, 32833, -15199], ![364776, -396754, 88571, -70953, 32833], ![-787992, 857271, -191420, 153291, -70953], ![677808, -737350, 164632, -131852, 61025], ![-219168, 238404, -53226, 42633, -19730]]]
  hmulB := by decide  
  f := ![![![-238337, 33660, 97416, 42431, 20529]], ![![-197220, 27854, 80609, 35109, 16987]], ![![-186081, 26277, 76060, 33132, 16026]], ![![-32739, 4622, 13384, 5833, 2822]], ![![-237040, 33492, 96870, 42175, 20422]]]
  g := ![![![-109326, 183626, -41006, 32833, -15199], ![236248, -396754, 88571, -70953, 32833], ![-510417, 857271, -191420, 153291, -70953], ![439028, -737350, 164632, -131852, 61025], ![-141953, 238404, -53226, 42633, -19730]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-238337, 33660, 97416, 42431, 20529]] ![![-168769, 183626, -41006, 32833, -15199]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6973, -988, -2848, -1242, -600]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![6973, -988, -2848, -1242, -600]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![13, 11, 1, 0, 0], ![14, 5, 0, 1, 0], ![9, 4, 0, 0, 1]] where
  M :=![![![6973, -988, -2848, -1242, -600], ![14400, -2027, -5890, -2562, -1242], ![29808, -4230, -12167, -5298, -2562], ![-4656, 678, 1886, 817, 398], ![6288, -882, -2582, -1146, -551]]]
  hmulB := by decide  
  f := ![![![-1437521, -63248, 368852, 133830, 89532]], ![![-2148768, -94541, 551350, 200046, 133830]], ![![-2396639, -105447, 614951, 223122, 149268]], ![![-1582282, -69617, 405996, 147307, 98548]], ![![-1111731, -48914, 285258, 103500, 69241]]]
  g := ![![![3515, 2050, -2848, -1242, -600], ![7264, 4239, -5890, -2562, -1242], ![15011, 8755, -12167, -5298, -2562], ![-2326, -1355, 1886, 817, 398], ![3203, 1866, -2582, -1146, -551]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [14, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 18], [0, 1]]
 g := ![![[12, 4], [], [9], [1]], ![[5, 15], [], [9], [1]]]
 h' := ![![[3, 18], [0, 17], [13], [5, 3], [0, 1]], ![[0, 1], [13, 2], [13], [14, 16], [3, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [6, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [14, 16, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4961, 5603, -3034, -7228, 1665]
  a := ![13, -1, -2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6352, 3603, -3034, -7228, 1665]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![418075, -454776, 101534, -81325, 37637]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![418075, -454776, 101534, -81325, 37637]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![2, 1, 1, 0, 0], ![5, 6, 0, 1, 0], ![5, 18, 0, 0, 1]] where
  M :=![![![418075, -454776, 101534, -81325, 37637], ![-903288, 982630, -219397, 175713, -81325], ![1951800, -2123163, 474026, -379671, 175713], ![-1678752, 1826164, -407724, 326558, -151135], ![542784, -590448, 131828, -105585, 48866]]]
  hmulB := by decide  
  f := ![![![313, -194, 56, 251, 11]], ![![-264, 478, -321, -615, 251]], ![![-298, 189, -57, -248, -18]], ![![287, -126, 6, 165, 58]], ![![959, -166, -202, 232, 429]]]
  g := ![![![22813, -39254, 101534, -81325, 37637], ![-49286, 84821, -219397, 175713, -81325], ![106502, -183263, 474026, -379671, 175713], ![-91601, 157630, -407724, 326558, -151135], ![29617, -50966, 131828, -105585, 48866]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [14, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 18], [0, 1]]
 g := ![![[15, 17], [17, 7], [1], [1]], ![[17, 2], [10, 12], [1], [1]]]
 h' := ![![[18, 18], [9, 6], [11, 8], [5, 18], [0, 1]], ![[0, 1], [3, 13], [3, 11], [6, 1], [18, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [9, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [14, 1, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-394, 446, -258, -663, 163]
  a := ![-1, -3, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![138, 92, -258, -663, 163]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, -31, 13, 27, -5]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![31, -31, 13, 27, -5]] 
 ![![19, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![31, -31, 13, 27, -5], ![120, -44, 1, 87, 27], ![-648, 525, -236, -741, 87], ![-24, -153, 153, 244, -167], ![3288, -2463, 953, 3183, -170]]]
  hmulB := by decide  
  f := ![![![-133139, -7079, 33159, 11835, 8135]], ![![-59327, -3193, 14744, 5256, 3620]], ![![-71008, -3913, 17572, 6249, 4321]], ![![-80196, -4257, 19979, 7132, 4901]], ![![-116713, -6286, 29002, 10338, 7121]]]
  g := ![![![-5, -31, 13, 27, -5], ![-57, -44, 1, 87, 27], ![262, 525, -236, -741, 87], ![-14, -153, 153, 244, -167], ![-1179, -2463, 953, 3183, -170]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![6973, -988, -2848, -1242, -600]] ![![418075, -454776, 101534, -81325, 37637]]
  ![![8298703, -9050152, 2031178, -1614697, 751347]] where
 M := ![![![8298703, -9050152, 2031178, -1614697, 751347]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![8298703, -9050152, 2031178, -1614697, 751347]] ![![31, -31, 13, 27, -5]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![364219873, -396203675, 88460029, -70849708, 32790276]]]
 hmul := by decide  
 g := ![![![![19169467, -20852825, 4655791, -3728932, 1725804]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-745, 748, -138, 144, -56]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-745, 748, -138, 144, -56]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![17, 8, 0, 4, 1]] where
  M :=![![![-745, 748, -138, 144, -56], ![1344, -1585, 414, -252, 144], ![-3456, 3504, -667, 648, -252], ![2736, -2958, 644, -559, 234], ![-864, 876, -138, 300, -109]]]
  hmulB := by decide  
  f := ![![![73729, 3244, -18918, -6864, -4592]], ![![110208, 4849, -28278, -10260, -6864]], ![![164736, 7248, -42269, -15336, -10260]], ![![-41328, -1818, 10604, 3847, 2574]], ![![84727, 3728, -21740, -7888, -5277]]]
  g := ![![![9, 52, -6, 16, -56], ![-48, -119, 18, -36, 144], ![36, 240, -29, 72, -252], ![-54, -210, 28, -65, 234], ![43, 76, -6, 32, -109]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [1, 4, 6, 12, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 7, 7, 11], [17, 22], [18, 16, 16, 12], [0, 1]]
 g := ![![[1, 1, 12, 1], [9, 1], [11, 1], []], ![[0, 12, 14, 10, 1, 5], [8, 17, 4, 10, 18, 14], [17, 8, 1, 14, 16, 7], [11, 13, 6]], ![[4, 12, 17, 22], [3, 22], [5, 22], []], ![[18, 16, 14, 8, 12, 18], [7, 5, 14, 5, 12, 9], [16, 7, 22, 12, 13, 16], [11, 13, 6]]]
 h' := ![![[22, 7, 7, 11], [14, 15, 12, 1], [12, 1, 22], [0, 0, 1], [0, 1]], ![[17, 22], [11, 15, 5, 6], [21, 9, 4, 8], [13, 21, 3, 3], [22, 7, 7, 11]], ![[18, 16, 16, 12], [2, 21, 17, 22], [16, 10, 22], [13, 12, 1], [17, 22]], ![[0, 1], [1, 18, 12, 17], [16, 3, 21, 15], [14, 13, 18, 20], [18, 16, 16, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10], []]
 b := ![[], [], [13, 10, 22, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [1, 4, 6, 12, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19062448, -28200571, 17565238, 35465968, -13174339]
  a := ![3, 0, 3, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10566357, 3356267, 763706, 3833188, -13174339]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73729, 3244, -18918, -6864, -4592]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![73729, 3244, -18918, -6864, -4592]] 
 ![![23, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![73729, 3244, -18918, -6864, -4592], ![110208, 4849, -28278, -10260, -6864], ![164736, 7248, -42269, -15336, -10260], ![-41328, -1818, 10604, 3847, 2574], ![-21024, -924, 5394, 1956, 1309]]]
  hmulB := by decide  
  f := ![![![-745, 748, -138, 144, -56]], ![![-557, 549, -96, 108, -40]], ![![-377, 380, -71, 72, -28]], ![![-43, 34, -2, 7, -2]], ![![-653, 656, -120, 132, -51]]]
  g := ![![![11569, 3244, -18918, -6864, -4592], ![17293, 4849, -28278, -10260, -6864], ![25849, 7248, -42269, -15336, -10260], ![-6485, -1818, 10604, 3847, 2574], ![-3299, -924, 5394, 1956, 1309]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-745, 748, -138, 144, -56]] ![![73729, 3244, -18918, -6864, -4592]]
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


lemma PB1906I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1906I0 : PrimesBelowBoundCertificateInterval O 1 23 1906 where
  m := 9
  g := ![5, 5, 5, 3, 2, 3, 2, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1906I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
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
    · exact ![343, 7, 7]
    · exact ![1331, 121]
    · exact ![169, 169, 13]
    · exact ![83521, 17]
    · exact ![361, 361, 19]
    · exact ![279841, 23]
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
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
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
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N0, I7N1, I7N2, I11N0, I11N1, I13N0, I13N1, I13N2, I17N1, I19N0, I19N1, I19N2, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [I11N0, I11N1], [I13N0, I13N1, I13N2], [I17N1], [I19N0, I19N1, I19N2], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
