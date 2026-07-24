
import IdealArithmetic.Examples.NF5_1_40500000_1.RI5_1_40500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27855, -7984, 3744, -11250, -16207]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-27855, -7984, 3744, -11250, -16207]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-27855, -7984, 3744, -11250, -16207], ![-71121, -20385, 9559, -28724, -41379], ![-181585, -52050, 24408, -73340, -105655], ![-10804, -3096, 1452, -4363, -6286], ![-51637, -14802, 6941, -20856, -30045]]]
  hmulB := by decide  
  f := ![![![-171, 22, 31, 14, -50]], ![![-61, -1, -35, 126, 131]], ![![645, -110, -248, 290, 615]], ![![273, -30, -19, -101, -18]], ![![51, -12, -38, 70, 108]]]
  g := ![![![-5824, -7984, 3744, -11250, -16207], ![-14871, -20385, 9559, -28724, -41379], ![-37965, -52050, 24408, -73340, -105655], ![-2259, -3096, 1452, -4363, -6286], ![-10796, -14802, 6941, -20856, -30045]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![358, -164, -652, 1513, 2009]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![358, -164, -652, 1513, 2009]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![358, -164, -652, 1513, 2009], ![9053, -1389, -2694, 2037, 6077], ![22305, -2380, -1423, -8675, -1935], ![-6842, 1346, 3518, -5431, -9398], ![4827, -518, -323, -1838, -370]]]
  hmulB := by decide  
  f := ![![![493119, 141342, -66279, 199160, 286907]], ![![876080, 251113, -117755, 353832, 509733]], ![![1853902, 531366, -249174, 748740, 1078631]], ![![95625, 27412, -12853, 38623, 55635]], ![![457083, 131006, -61434, 184601, 265940]]]
  g := ![![![587, -164, -652, 1513, 2009], ![6568, -1389, -2694, 2037, 6077], ![13054, -2380, -1423, -8675, -1935], ![-5853, 1346, 3518, -5431, -9398], ![2834, -518, -323, -1838, -370]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1446, 413, -194, 583, 841]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![1446, 413, -194, 583, 841]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![1446, 413, -194, 583, 841], ![3689, 1059, -495, 1491, 2141], ![9405, 2705, -1273, 3805, 5505], ![568, 155, -73, 224, 322], ![2668, 774, -364, 1084, 1569]]]
  hmulB := by decide  
  f := ![![![128, -29, -85, 152, 238]], ![![573, -87, -166, 117, 370]], ![![899, -82, 13, -534, -306]], ![![-440, 72, 153, -157, -367]], ![![182, -15, 11, -130, -89]]]
  g := ![![![322, 413, -194, 583, 841], ![817, 1059, -495, 1491, 2141], ![2084, 2705, -1273, 3805, 5505], ![131, 155, -73, 224, 322], ![587, 774, -364, 1084, 1569]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-27855, -7984, 3744, -11250, -16207]] ![![358, -164, -652, 1513, 2009]]
  ![![-11, 2, 5, -7, -13]] where
 M := ![![![-11, 2, 5, -7, -13]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-11, 2, 5, -7, -13]] ![![358, -164, -652, 1513, 2009]]
  ![![110836, -15562, -25758, 5967, 50976]] where
 M := ![![![110836, -15562, -25758, 5967, 50976]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![110836, -15562, -25758, 5967, 50976]] ![![1446, 413, -194, 583, 841]]
  ![![-128, 29, 85, -152, -238]] where
 M := ![![![-128, 29, 85, -152, -238]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-128, 29, 85, -152, -238]] ![![1446, 413, -194, 583, 841]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-2, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1849799, -530206, 248630, -747094, -1076264]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-1849799, -530206, 248630, -747094, -1076264]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-1849799, -530206, 248630, -747094, -1076264], ![-4722980, -1353743, 634812, -1907510, -2747960], ![-12058900, -3456430, 1620827, -4870330, -7016200], ![-717436, -205638, 96430, -289757, -417424], ![-3429200, -982908, 460916, -1384980, -1995203]]]
  hmulB := by decide  
  f := ![![![-29, 2, -26, 78, 88]], ![![140, -27, -48, 50, 120]], ![![460, -50, -57, -90, 40]], ![![-76, 22, 50, -101, -144]], ![![97, -14, -18, 6, 29]]]
  g := ![![![-257845, -530206, 248630, -747094, -1076264], ![-658340, -1353743, 634812, -1907510, -2747960], ![-1680900, -3456430, 1620827, -4870330, -7016200], ![-100004, -205638, 96430, -289757, -417424], ![-477999, -982908, 460916, -1384980, -1995203]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-1849799, -530206, 248630, -747094, -1076264]] ![![-1849799, -530206, 248630, -747094, -1076264]]
  ![![7154421007065, 2050664410436, -961620011876, 2889516664144, 4162639272144]] where
 M := ![![![7154421007065, 2050664410436, -961620011876, 2889516664144, 4162639272144]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![7154421007065, 2050664410436, -961620011876, 2889516664144, 4162639272144]] ![![-1849799, -530206, 248630, -747094, -1076264]]
  ![![-27670974129930372399, -7931303147285963282, 3719233526398257354, -11175710904149324518, -16099735184438294808]] where
 M := ![![![-27670974129930372399, -7931303147285963282, 3719233526398257354, -11175710904149324518, -16099735184438294808]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-27670974129930372399, -7931303147285963282, 3719233526398257354, -11175710904149324518, -16099735184438294808]] ![![-1849799, -530206, 248630, -747094, -1076264]]
  ![![107022330464360861529257009, 30675701637974810421736648, -14384785937325657593219464, 43224015892679370085745472, 62268540717326331486314912]] where
 M := ![![![107022330464360861529257009, 30675701637974810421736648, -14384785937325657593219464, 43224015892679370085745472, 62268540717326331486314912]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N3 : IdealMulLeCertificate' Table 
  ![![107022330464360861529257009, 30675701637974810421736648, -14384785937325657593219464, 43224015892679370085745472, 62268540717326331486314912]] ![![-1849799, -530206, 248630, -747094, -1076264]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-413927574946985927560445630012823, -118643639450857916192046069729030, 55635674660920627796332290805470, -167176438788956992984772834757270, -240834468309337301453055490726920]]]
 hmul := by decide  
 g := ![![![![-137975858315661975853481876670941, -39547879816952638730682023243010, 18545224886973542598777430268490, -55725479596318997661590944919090, -80278156103112433817685163575640]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 0, 1, -2, -3]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-2, 0, 1, -2, -3]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-2, 0, 1, -2, -3], ![-13, 1, 3, -2, -7], ![-25, 0, 0, 10, 5], ![10, -2, -4, 5, 10], ![-6, 0, 0, 2, 1]]]
  hmulB := by decide  
  f := ![![![0, 0, 1, 0, -5]], ![![-3, 1, -1, 0, 3]], ![![9, -8, 4, -4, -9]], ![![-2, 2, 0, 1, -2]], ![![4, -4, 2, -2, -5]]]
  g := ![![![2, 0, 1, -2, -3], ![3, 1, 3, -2, -7], ![-9, 0, 0, 10, 5], ![-6, -2, -4, 5, 10], ![-2, 0, 0, 2, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-2, 0, 1, -2, -3]] ![![-2, 0, 1, -2, -3]]
  ![![-23, 4, 6, -2, -12]] where
 M := ![![![-23, 4, 6, -2, -12]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-23, 4, 6, -2, -12]] ![![-2, 0, 1, -2, -3]]
  ![![-104, 8, -3, 64, 39]] where
 M := ![![![-104, 8, -3, 64, 39]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-104, 8, -3, 64, 39]] ![![-2, 0, 1, -2, -3]]
  ![![585, -120, -336, 560, 920]] where
 M := ![![![585, -120, -336, 560, 920]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![585, -120, -336, 560, 920]] ![![-2, 0, 1, -2, -3]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![8870, -1240, -2015, 350, 3925]]]
 hmul := by decide  
 g := ![![![![1774, -248, -403, 70, 785]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![714, -108, -203, 136, 449]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![714, -108, -203, 136, 449]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![4, 6, 6, 1, 0], ![2, 0, 3, 0, 1]] where
  M :=![![![714, -108, -203, 136, 449], ![1619, -165, -67, -724, -259], ![-2225, 560, 1748, -3360, -5015], ![-2986, 398, 596, 99, -1054], ![-466, 120, 372, -722, -1071]]]
  hmulB := by decide  
  f := ![![![164044, 47020, -22049, 66254, 95445]], ![![418843, 120053, -56297, 169162, 243697]], ![![1069415, 306520, -143736, 431910, 622205]], ![![1378478, 395108, -185278, 556735, 802030]], ![![548635, 157252, -73740, 221580, 319206]]]
  g := ![![![-104, -132, -338, 136, 449], ![719, 597, 722, -724, -259], ![3035, 2960, 5279, -3360, -5015], ![-182, -28, 452, 99, -1054], ![652, 636, 1131, -722, -1071]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [3, 1, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 0, 6], [2, 6, 1], [0, 1]]
 g := ![![[2, 0, 2], [1]], ![[4, 6, 0, 3], [5, 2, 4, 6]], ![[5, 2, 6, 1], [1, 1, 0, 1]]]
 h' := ![![[1, 0, 6], [4, 6, 3], [0, 1]], ![[2, 6, 1], [0, 3, 5], [1, 0, 6]], ![[0, 1], [5, 5, 6], [2, 6, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 6], []]
 b := ![[], [1, 4, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [3, 1, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-74263, 29753, 20307, 26296, -94984]
  a := ![-11, -7, 13, -19, -44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1503, -18289, 21069, 26296, -94984]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22, 5, -4, 10, 15]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![22, 5, -4, 10, 15]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![22, 5, -4, 10, 15], ![65, 12, -10, 20, 35], ![145, 35, -13, 30, 55], ![-10, 5, 5, -3, -10], ![40, 10, -4, 10, 17]]]
  hmulB := by decide  
  f := ![![![36, -25, 12, -10, -25]], ![![7, -2, 4, 0, -15]], ![![35, -40, 3, -20, 30]], ![![34, -20, 13, -7, -35]], ![![18, -20, 2, -10, 13]]]
  g := ![![![-14, 5, -4, 10, 15], ![-29, 12, -10, 20, 35], ![-50, 35, -13, 30, 55], ![2, 5, 5, -3, -10], ![-16, 10, -4, 10, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4067, -1165, 543, -1642, -2350]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![-4067, -1165, 543, -1642, -2350]] 
 ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-4067, -1165, 543, -1642, -2350], ![-10334, -2994, 1411, -4196, -6086], ![-26650, -7475, 3508, -10650, -15310], ![-1556, -479, 211, -651, -884], ![-7596, -2102, 998, -3016, -4381]]]
  hmulB := by decide  
  f := ![![![4147, -339, 253, -2972, -2038]], ![![1832, 58, 1151, -4042, -4270]], ![![-7004, 1163, 2526, -2736, -6134]], ![![3062, -385, -487, -425, 680]], ![![-1082, 216, 572, -900, -1537]]]
  g := ![![![2031, -1165, 543, -1642, -2350], ![5216, -2994, 1411, -4196, -6086], ![13096, -7475, 3508, -10650, -15310], ![818, -479, 211, -651, -884], ![3698, -2102, 998, -3016, -4381]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![714, -108, -203, 136, 449]] ![![22, 5, -4, 10, 15]]
  ![![-4147, 339, -253, 2972, 2038]] where
 M := ![![![-4147, 339, -253, 2972, 2038]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-4147, 339, -253, 2972, 2038]] ![![-4067, -1165, 543, -1642, -2350]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-824, -235, 110, -332, -477]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-824, -235, 110, -332, -477]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![6, 8, 2, 1, 0], ![5, 8, 10, 0, 1]] where
  M :=![![![-824, -235, 110, -332, -477], ![-2095, -606, 284, -850, -1225], ![-5375, -1525, 719, -2160, -3125], ![-322, -91, 41, -129, -178], ![-1526, -434, 206, -614, -895]]]
  hmulB := by decide  
  f := ![![![42, -5, -6, -8, 7]], ![![5, 4, 26, -70, -85]], ![![-395, 65, 129, -120, -305]], ![![-56, 13, 39, -71, -110]], ![![-344, 61, 136, -166, -342]]]
  g := ![![![323, 567, 504, -332, -477], ![830, 1454, 1294, -850, -1225], ![2110, 3705, 3299, -2160, -3125], ![122, 215, 189, -129, -178], ![603, 1058, 944, -614, -895]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [4, 8, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 3, 7], [7, 7, 4], [0, 1]]
 g := ![![[1, 4, 9], [1, 3, 1], []], ![[3, 4, 9, 2], [0, 10, 4, 2], [2, 5]], ![[0, 8, 5, 4], [6, 4, 5, 3], [5, 5]]]
 h' := ![![[7, 3, 7], [7, 2, 8], [0, 0, 1], [0, 1]], ![[7, 7, 4], [8, 10, 4], [8, 6, 7], [7, 3, 7]], ![[0, 1], [0, 10, 10], [7, 5, 3], [7, 7, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 5], []]
 b := ![[], [2, 5, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [4, 8, 8, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15077311, 810364, 3168332, -5831128, -15577829]
  a := ![-49, -56, 48, -106, -199]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8890782, 15643820, 15509898, -5831128, -15577829]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42, -5, -6, -8, 7]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![42, -5, -6, -8, 7]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![6, 2, 1, 0, 0], ![1, 4, 0, 1, 0], ![6, 4, 0, 0, 1]] where
  M :=![![![42, -5, -6, -8, 7], ![5, 4, 26, -70, -85], ![-395, 65, 129, -120, -305], ![-118, 11, -1, 67, 38], ![-84, 14, 28, -26, -67]]]
  hmulB := by decide  
  f := ![![![-824, -235, 110, -332, -477]], ![![-2095, -606, 284, -850, -1225]], ![![-1319, -377, 177, -532, -767]], ![![-866, -250, 117, -351, -505]], ![![-1350, -388, 182, -546, -787]]]
  g := ![![![4, 1, -6, -8, 7], ![39, 52, 26, -70, -85], ![71, 137, 129, -120, -305], ![-37, -37, -1, 67, 38], ![16, 30, 28, -26, -67]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [2, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 10], [0, 1]]
 g := ![![[2, 1], [7, 5], [1]], ![[9, 10], [9, 6], [1]]]
 h' := ![![[7, 10], [8, 10], [9, 7], [0, 1]], ![[0, 1], [1, 1], [3, 4], [7, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [5, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [2, 4, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![45, 10, 116, -75, -316]
  a := ![-4, -4, 5, -9, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![120, 122, 116, -75, -316]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-824, -235, 110, -332, -477]] ![![42, -5, -6, -8, 7]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22368284, -6411395, 3006498, -9034066, -13014463]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-22368284, -6411395, 3006498, -9034066, -13014463]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![4, 1, 5, 1, 0], ![3, 2, 4, 0, 1]] where
  M :=![![![-22368284, -6411395, 3006498, -9034066, -13014463], ![-57111521, -16369860, 7676340, -23066144, -33229139], ![-145819705, -41795965, 19599433, -58893310, -84841735], ![-8675422, -2486655, 1166053, -3503835, -5047558], ![-41466888, -11885534, 5573512, -16747530, -24126559]]]
  hmulB := by decide  
  f := ![![![-42014, 7861, 19578, -28034, -51145]], ![![-209503, 27842, 40818, 9388, -70837]], ![![-193735, 3975, -71159, 294670, 287615]], ![![-84328, 3058, -24332, 110821, 103656]], ![![-104834, 7401, -12244, 90488, 70482]]]
  g := ![![![4062413, 2203969, 7710360, -9034066, -13014463], ![10372344, 5627274, 19686432, -23066144, -33229139], ![26482980, 14367755, 50264071, -58893310, -84841735], ![1575584, 854792, 2990420, -3503835, -5047558], ![7530993, 4085778, 14293646, -16747530, -24126559]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [7, 3, 3, 1] where
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
 g := ![![[10, 11, 1], [4, 9], [1]], ![[6, 9, 3], [11, 3], [1]], ![[10, 6, 9], [9, 1], [1]]]
 h' := ![![[8, 9], [8, 6, 12], [6, 10, 10], [0, 1]], ![[2, 3], [5, 1, 10], [11, 9, 4], [8, 9]], ![[0, 1], [3, 6, 4], [1, 7, 12], [2, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11], []]
 b := ![[], [10, 7, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [7, 3, 3, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4095665, -1634653, -544959, -364814, 3541701]
  a := ![36, 27, -39, 62, 143]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-390014, -642557, -991361, -364814, 3541701]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42014, -7861, -19578, 28034, 51145]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![42014, -7861, -19578, 28034, 51145]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![12, 2, 1, 0, 0], ![8, 0, 0, 1, 0], ![5, 10, 0, 0, 1]] where
  M :=![![![42014, -7861, -19578, 28034, 51145], ![209503, -27842, -40818, -9388, 70837], ![193735, -3975, 71159, -294670, -287615], ![-249970, 39407, 79651, -70071, -184870], ![42854, -1046, 14906, -62990, -60915]]]
  hmulB := by decide  
  f := ![![![22368284, 6411395, -3006498, 9034066, 13014463]], ![![57111521, 16369860, -7676340, 23066144, 33229139]], ![![40650935, 11651725, -5463853, 16418030, 23651813]], ![![14432438, 4136755, -1939849, 5828951, 8397174]], ![![55724886, 15972393, -7489954, 22506100, 32422328]]]
  g := ![![![-15619, -36935, -19578, 28034, 51145], ![32326, -50352, -40818, -9388, 70837], ![241174, 209989, 71159, -294670, -287615], ![21472, 132985, 79651, -70071, -184870], ![51729, 44484, 14906, -62990, -60915]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [4, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 12], [0, 1]]
 g := ![![[4, 10], [12], [10, 1]], ![[0, 3], [12], [7, 12]]]
 h' := ![![[10, 12], [5, 6], [12, 5], [0, 1]], ![[0, 1], [0, 7], [10, 8], [10, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [6, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [4, 3, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1537, 985, 1894, 1220, -6675]
  a := ![-21, -9, 26, -28, -83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-50, 4919, 1894, 1220, -6675]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-22368284, -6411395, 3006498, -9034066, -13014463]] ![![42014, -7861, -19578, 28034, 51145]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [15, 15, 2, 0, 10, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 0, 15, 12, 10], [13, 11, 15, 15, 6], [9, 4, 11, 14, 7], [15, 1, 10, 10, 11], [0, 1]]
 g := ![![[2, 13, 9, 9, 8], [1, 15, 7, 1], [], []], ![[11, 1, 2, 5], [7, 7, 0, 15], [16, 1, 1, 2], [11, 3, 5, 15]], ![[13, 6, 6, 7, 3, 15, 16, 6], [1, 9, 1, 8], [9, 8, 12, 9], [16, 12, 7, 2]], ![[0, 8, 3, 11, 7, 5, 4, 7], [4, 0, 9, 13], [11, 13, 3, 1], [6, 9, 12, 15]], ![[16, 16, 5, 2, 6, 14, 0, 3], [10, 5, 6, 15], [7, 9, 15, 15], [1, 3, 13, 2]]]
 h' := ![![[4, 0, 15, 12, 10], [2, 15, 8, 3, 12], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[13, 11, 15, 15, 6], [6, 10, 14], [14, 3, 2, 16, 10], [4, 11, 12, 11, 11], [4, 0, 15, 12, 10]], ![[9, 4, 11, 14, 7], [0, 1, 12, 2, 16], [10, 5, 1, 3, 5], [14, 2, 7, 0, 14], [13, 11, 15, 15, 6]], ![[15, 1, 10, 10, 11], [9, 2, 10, 14, 1], [1, 14, 4, 14, 8], [8, 0, 6, 2, 16], [9, 4, 11, 14, 7]], ![[0, 1], [4, 6, 7, 15, 5], [16, 12, 10, 1, 10], [6, 4, 8, 4, 10], [15, 1, 10, 10, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 1, 15, 15], [], [], []]
 b := ![[], [7, 9, 7, 4, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [15, 15, 2, 0, 10, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10689404755, -127481980, 7563454870, 1956292170, -32596995440]
  a := ![12, -4, -14, -2, 48]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![628788515, -7498940, 444909110, 115076010, -1917470320]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 1419857 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-732507, -209958, 98456, -295844, -426194]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-732507, -209958, 98456, -295844, -426194]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![3, 18, 1, 0, 0], ![6, 14, 0, 1, 0], ![1, 16, 0, 0, 1]] where
  M :=![![![-732507, -209958, 98456, -295844, -426194], ![-1870270, -536071, 251380, -755360, -1088170], ![-4775230, -1368730, 641839, -1928620, -2778370], ![-284100, -81430, 38186, -114741, -165300], ![-1357936, -389228, 182520, -548444, -790085]]]
  hmulB := by decide  
  f := ![![![1795, -318, -744, 956, 1886]], ![![7570, -969, -1300, -800, 1990]], ![![7685, -954, -1169, -1208, 1532]], ![![5630, -736, -1042, -397, 1724]], ![![6521, -830, -1096, -752, 1637]]]
  g := ![![![61757, 472566, 98456, -295844, -426194], ![157680, 1206571, 251380, -755360, -1088170], ![402597, 3080672, 641839, -1928620, -2778370], ![23952, 183284, 38186, -114741, -165300], ![114487, 876052, 182520, -548444, -790085]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [2, 1, 1] where
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
 g := ![![[10, 4], [3, 9], [1], [1]], ![[6, 15], [13, 10], [1], [1]]]
 h' := ![![[18, 18], [13, 2], [2, 3], [17, 18], [0, 1]], ![[0, 1], [11, 17], [18, 16], [18, 1], [18, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [11, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5323, 3193, 604, 620, -2565]
  a := ![24, 19, -20, 44, 83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![124, 1299, 604, 620, -2565]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![292, -50, -129, 172, 329]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![292, -50, -129, 172, 329]] 
 ![![19, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![292, -50, -129, 172, 329], ![1331, -181, -237, -116, 389], ![935, 30, 556, -1940, -2095], ![-1682, 268, 494, -387, -1118], ![226, -4, 124, -418, -465]]]
  hmulB := by decide  
  f := ![![![-193246034, -55389914, 25974045, -78047914, -112435867]], ![![-76822821, -22019647, 10325694, -31027084, -44697634]], ![![-198525033, -56903028, 26683591, -80179988, -115507334]], ![![-105653154, -30283256, 14200756, -42671035, -61471916]], ![![-59538320, -17065408, 8002498, -24046246, -34641035]]]
  g := ![![![-43, -50, -129, 172, 329], ![259, -181, -237, -116, 389], ![1123, 30, 556, -1940, -2095], ![-58, 268, 494, -387, -1118], ![246, -4, 124, -418, -465]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-202, 30, 55, -32, -119]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-202, 30, 55, -32, -119]] 
 ![![19, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-202, 30, 55, -32, -119], ![-421, 41, 7, 216, 101], ![735, -170, -506, 920, 1425], ![822, -108, -154, -53, 258], ![154, -36, -108, 198, 305]]]
  hmulB := by decide  
  f := ![![![-56, 94, -59, 54, 177]], ![![13, 19, -16, 16, 60]], ![![-47, 98, -34, 58, 59]], ![![-38, 44, -34, 23, 110]], ![![-20, 58, -23, 36, 50]]]
  g := ![![![25, 30, 55, -32, -119], ![-179, 41, 7, 216, 101], ![-748, -170, -506, 920, 1425], ![48, -108, -154, -53, 258], ![-161, -36, -108, 198, 305]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2

def I19N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-987, -282, 132, -398, -572]] i)))

def SI19N3: IdealEqSpanCertificate' Table ![![-987, -282, 132, -398, -572]] 
 ![![19, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-987, -282, 132, -398, -572], ![-2512, -725, 340, -1018, -1468], ![-6440, -1830, 861, -2590, -3740], ![-384, -110, 50, -155, -216], ![-1830, -520, 246, -736, -1069]]]
  hmulB := by decide  
  f := ![![![655, -98, -184, 118, 404]], ![![352, -49, -80, 14, 156]], ![![300, -34, -31, -86, 12]], ![![305, -48, -98, 87, 228]], ![![390, -56, -98, 40, 203]]]
  g := ![![![617, -282, 132, -398, -572], ![1582, -725, 340, -1018, -1468], ![4022, -1830, 861, -2590, -3740], ![237, -110, 50, -155, -216], ![1146, -520, 246, -736, -1069]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N3 : Nat.card (O ⧸ I19N3) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N3)

lemma isPrimeI19N3 : Ideal.IsPrime I19N3 := prime_ideal_of_norm_prime hp19.out _ NI19N3
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-732507, -209958, 98456, -295844, -426194]] ![![292, -50, -129, 172, 329]]
  ![![-18, 12, -7, 4, 17]] where
 M := ![![![-18, 12, -7, 4, 17]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![-18, 12, -7, 4, 17]] ![![-202, 30, 55, -32, -119]]
  ![![-655, 98, 184, -118, -404]] where
 M := ![![![-655, 98, 184, -118, -404]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N2 : IdealMulLeCertificate' Table 
  ![![-655, 98, 184, -118, -404]] ![![-987, -282, 132, -398, -572]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2, I19N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
    exact isPrimeI19N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1 ⊙ MulI19N2)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 5 2 4 [3, 11, 22, 0, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 7, 19, 19, 2], [16, 14, 7, 1, 18], [21, 12, 14, 16, 14], [1, 12, 6, 10, 12], [0, 1]]
 g := ![![[22, 21, 1, 22, 9], [2, 4, 17, 13, 2], [1], []], ![[14, 10, 0, 15, 11, 0, 21, 6], [20, 9, 0, 5, 22, 16, 12, 1], [15, 17, 4, 14, 12, 3, 13, 2], [15, 19, 10, 4]], ![[17, 1, 11, 1, 10, 12], [15, 22, 4, 1, 20, 9, 9, 6], [2, 14, 2, 13, 7, 20, 0, 13], [20, 8, 3, 2]], ![[12, 7, 21, 17, 0, 5, 9, 11], [12, 19, 7, 20, 3, 20, 2, 17], [9, 22, 18, 22, 12, 2, 5, 15], [11, 19, 20, 12]], ![[2, 11, 17, 22, 14, 1, 5, 13], [20, 6, 17, 16, 3, 5, 20, 1], [17, 6, 2, 20, 11, 14, 0, 1], [5, 22, 3, 6]]]
 h' := ![![[3, 7, 19, 19, 2], [17, 21, 19, 8, 20], [20, 12, 1, 0, 18], [0, 0, 1], [0, 1]], ![[16, 14, 7, 1, 18], [21, 5, 0, 15, 16], [2, 11, 21, 5, 9], [10, 4, 8, 1, 1], [3, 7, 19, 19, 2]], ![[21, 12, 14, 16, 14], [19, 7, 9, 4], [21, 18, 0, 22, 10], [12, 20, 21, 13, 5], [16, 14, 7, 1, 18]], ![[1, 12, 6, 10, 12], [4, 6, 17, 10, 3], [16, 18, 14, 18, 4], [17, 4, 14, 12, 12], [21, 12, 14, 16, 14]], ![[0, 1], [12, 7, 1, 9, 7], [7, 10, 10, 1, 5], [9, 18, 2, 20, 5], [1, 12, 6, 10, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 4, 4, 21], [], [], []]
 b := ![[], [2, 16, 0, 5, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 5
  hpos := by decide
  P := [3, 11, 22, 0, 5, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26013, -45885, -134895, 316020, 310155]
  a := ![0, -3, -1, -4, 1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1131, -1995, -5865, 13740, 13485]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 6436343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀



lemma PB397I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB397I0 : PrimesBelowBoundCertificateInterval O 1 23 397 where
  m := 9
  g := ![5, 5, 5, 3, 2, 2, 1, 4, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB397I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1, I19N2, I19N3]
    · exact ![I23N0]
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
    · exact ![2197, 169]
    · exact ![1419857]
    · exact ![361, 19, 19, 19]
    · exact ![6436343]
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
      exact NI3N0
      exact NI3N0
      exact NI3N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
      exact NI19N3
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
  β := ![I2N0, I2N1, I2N2, I3N0, I5N0, I7N0, I7N1, I7N2, I11N1, I13N1, I19N0, I19N1, I19N2, I19N3]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N0, I3N0, I3N0], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [I11N1], [I13N1], [], [I19N0, I19N1, I19N2, I19N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
