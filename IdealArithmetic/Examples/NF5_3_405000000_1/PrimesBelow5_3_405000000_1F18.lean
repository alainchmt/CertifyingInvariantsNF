
import IdealArithmetic.Examples.NF5_3_405000000_1.RI5_3_405000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp967 : Fact (Nat.Prime 967) := {out := by norm_num}

def I967N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39881, 254720, -45601, 8709, -33412]] i)))

def SI967N0: IdealEqSpanCertificate' Table ![![-39881, 254720, -45601, 8709, -33412]] 
 ![![967, 0, 0, 0, 0], ![0, 967, 0, 0, 0], ![523, 599, 1, 0, 0], ![31, 479, 0, 1, 0], ![866, 879, 0, 0, 1]] where
  M :=![![![-39881, 254720, -45601, 8709, -33412], ![-17418, 111185, -19861, 3805, -14570], ![-7610, 48472, -8530, 1669, -6310], ![-3338, 20968, -3311, 752, -2606], ![-5046, 32030, -5457, 1117, -4111]]]
  hmulB := by decide  
  f := ![![![101, -32, -485, 235, -112]], ![![-470, 1019, -335, -731, 1186]], ![![-235, 607, -460, -327, 672]], ![![-227, 511, -211, -338, 572]], ![![-342, 917, -762, -454, 987]]]
  g := ![![![54265, 54568, -45601, 8709, -33412], ![23650, 23777, -19861, 3805, -14570], ![10203, 10243, -8530, 1669, -6310], ![4097, 4069, -3311, 752, -2606], ![6592, 6597, -5457, 1117, -4111]]]
  hle1 := by decide   
  hle2 := by decide  


def P967P0 : CertificateIrreducibleZModOfList' 967 2 2 9 [844, 832, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [135, 966], [0, 1]]
 g := ![![[803, 278], [99, 258], [344, 722], [377], [939], [324], [179, 851], [649, 625], [135, 1]], ![[620, 689], [117, 709], [147, 245], [377], [939], [324], [958, 116], [895, 342], [270, 966]]]
 h' := ![![[135, 966], [573, 227], [731, 932], [415, 836], [163, 413], [97, 864], [743, 18], [533, 580], [166, 942], [0, 1]], ![[0, 1], [274, 740], [841, 35], [136, 131], [799, 554], [697, 103], [272, 949], [506, 387], [659, 25], [135, 966]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [461]]
 b := ![[], [155, 714]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI967N0 : CertifiedPrimeIdeal' SI967N0 967 where
  n := 2
  hpos := by decide
  P := [844, 832, 1]
  hirr := P967P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5771, -13501, 9483, -58, -11259]
  a := ![5, -6, -8, 4, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4962, 4375, 9483, -58, -11259]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI967N0 : Ideal.IsPrime I967N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI967N0 B_one_repr
lemma NI967N0 : Nat.card (O ⧸ I967N0) = 935089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI967N0

def I967N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2075, -25080, 54100, 3066, 19468]] i)))

def SI967N1: IdealEqSpanCertificate' Table ![![-2075, -25080, 54100, 3066, 19468]] 
 ![![967, 0, 0, 0, 0], ![0, 967, 0, 0, 0], ![697, 506, 1, 0, 0], ![273, 916, 0, 1, 0], ![187, 370, 0, 0, 1]] where
  M :=![![![-2075, -25080, 54100, 3066, 19468], ![-6132, -73815, 159330, 9032, 57332], ![-18064, -217396, 469269, 26602, 168856], ![-53204, -640284, 1382114, 78353, 497324], ![-33468, -402784, 869442, 49288, 312853]]]
  hmulB := by decide  
  f := ![![![-14157, 91776, -16456, 3138, -12044]], ![![-6276, 40295, -7206, 1356, -5260]], ![![-13491, 87254, -15635, 2972, -11436]], ![![-9943, 64088, -11474, 2171, -8384]], ![![-5141, 33178, -5942, 1126, -4343]]]
  g := ![![![-43627, -38688, 54100, 3066, 19468], ![-128486, -113941, 159330, 9032, 57332], ![-378425, -335586, 469269, 26602, 168856], ![-1114557, -988388, 1382114, 78353, 497324], ![-701131, -621762, 869442, 49288, 312853]]]
  hle1 := by decide   
  hle2 := by decide  


def P967P1 : CertificateIrreducibleZModOfList' 967 2 2 9 [188, 148, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [819, 966], [0, 1]]
 g := ![![[474, 820], [256, 71], [629, 292], [244], [118], [654], [6, 807], [199, 30], [819, 1]], ![[956, 147], [385, 896], [928, 675], [244], [118], [654], [478, 160], [594, 937], [671, 966]]]
 h' := ![![[819, 966], [222, 906], [689, 245], [78, 560], [347, 482], [636, 192], [806, 852], [301, 298], [748, 442], [0, 1]], ![[0, 1], [547, 61], [208, 722], [360, 407], [569, 485], [263, 775], [420, 115], [679, 669], [121, 525], [819, 966]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111]]
 b := ![[], [239, 539]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI967N1 : CertifiedPrimeIdeal' SI967N1 967 where
  n := 2
  hpos := by decide
  P := [188, 148, 1]
  hirr := P967P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![158, -13993, 15916, -4686, 2679]
  a := ![-6, -55, 11, -7, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10667, -4929, 15916, -4686, 2679]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI967N1 : Ideal.IsPrime I967N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI967N1 B_one_repr
lemma NI967N1 : Nat.card (O ⧸ I967N1) = 935089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI967N1

def I967N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -64, 235, -87, 24]] i)))

def SI967N2: IdealEqSpanCertificate' Table ![![-13, -64, 235, -87, 24]] 
 ![![967, 0, 0, 0, 0], ![829, 1, 0, 0, 0], ![296, 0, 1, 0, 0], ![234, 0, 0, 1, 0], ![845, 0, 0, 0, 1]] where
  M :=![![![-13, -64, 235, -87, 24], ![174, -283, -109, 361, -474], ![-722, 2792, -3466, 117, 1218], ![-234, -5360, 14105, -6136, 3138], ![2266, -7286, 7295, 1097, -4487]]]
  hmulB := by decide  
  f := ![![![574321, 6880672, -14874553, -843713, -5351556]], ![![494105, 5919721, -12797124, -725876, -4604142]], ![![180938, 2168004, -4686572, -265827, -1686138]], ![![154108, 1847108, -3992477, -226448, -1436430]], ![![511381, 6127126, -13245184, -751284, -4765355]]]
  g := ![![![-17, -64, 235, -87, 24], ![603, -283, -109, 361, -474], ![-2426, 2792, -3466, 117, 1218], ![-980, -5360, 14105, -6136, 3138], ![7671, -7286, 7295, 1097, -4487]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI967N2 : Nat.card (O ⧸ I967N2) = 967 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI967N2)

lemma isPrimeI967N2 : Ideal.IsPrime I967N2 := prime_ideal_of_norm_prime hp967.out _ NI967N2
def MulI967N0 : IdealMulLeCertificate' Table 
  ![![-39881, 254720, -45601, 8709, -33412]] ![![-2075, -25080, 54100, 3066, 19468]]
  ![![-574321, -6880672, 14874553, 843713, 5351556]] where
 M := ![![![-574321, -6880672, 14874553, 843713, 5351556]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI967N1 : IdealMulLeCertificate' Table 
  ![![-574321, -6880672, 14874553, 843713, 5351556]] ![![-13, -64, 235, -87, 24]]
  ![![967, 0, 0, 0, 0]] where
 M := ![![![-967, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC967 : ContainsPrimesAboveP 967 ![I967N0, I967N1, I967N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI967N0
    exact isPrimeI967N1
    exact isPrimeI967N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 967 (by decide) (𝕀 ⊙ MulI967N0 ⊙ MulI967N1)
instance hp971 : Fact (Nat.Prime 971) := {out := by norm_num}

def I971N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91, -565, 1585, 98, 558]] i)))

def SI971N0: IdealEqSpanCertificate' Table ![![-91, -565, 1585, 98, 558]] 
 ![![971, 0, 0, 0, 0], ![0, 971, 0, 0, 0], ![451, 211, 1, 0, 0], ![968, 596, 0, 1, 0], ![449, 172, 0, 0, 1]] where
  M :=![![![-91, -565, 1585, 98, 558], ![-196, -2127, 4751, 273, 1704], ![-546, -6466, 14028, 797, 5046], ![-1594, -19136, 41339, 2342, 14874], ![-1004, -12026, 26003, 1475, 9353]]]
  hmulB := by decide  
  f := ![![![8213, -20953, 3595, -810, 2676]], ![![1620, -4111, 701, -137, 492]], ![![4167, -10626, 1822, -406, 1350]], ![![9182, -23412, 4015, -892, 2970]], ![![4087, -10423, 1788, -399, 1325]]]
  g := ![![![-1092, -504, 1585, 98, 558], ![-3267, -1504, 4751, 273, 1704], ![-9644, -4438, 14028, 797, 5046], ![-28415, -13075, 41339, 2342, 14874], ![-17874, -8225, 26003, 1475, 9353]]]
  hle1 := by decide   
  hle2 := by decide  


def P971P0 : CertificateIrreducibleZModOfList' 971 2 2 9 [405, 165, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [806, 970], [0, 1]]
 g := ![![[396, 585], [529, 281], [916], [532, 186], [183], [522], [106, 153], [555, 455], [806, 1]], ![[0, 386], [772, 690], [916], [914, 785], [183], [522], [107, 818], [247, 516], [641, 970]]]
 h' := ![![[806, 970], [346, 467], [636, 530], [102, 753], [81, 900], [951, 315], [765, 542], [497, 89], [797, 603], [0, 1]], ![[0, 1], [0, 504], [576, 441], [145, 218], [144, 71], [439, 656], [667, 429], [377, 882], [344, 368], [806, 970]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [806]]
 b := ![[], [719, 403]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI971N0 : CertifiedPrimeIdeal' SI971N0 971 where
  n := 2
  hpos := by decide
  P := [405, 165, 1]
  hirr := P971P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![545, -599, 157, -88, -196]
  a := ![1, -3, -1, 0, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![106, 54, 157, -88, -196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI971N0 : Ideal.IsPrime I971N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI971N0 B_one_repr
lemma NI971N0 : Nat.card (O ⧸ I971N0) = 942841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI971N0

def I971N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8967, -57206, 10242, -1956, 7504]] i)))

def SI971N1: IdealEqSpanCertificate' Table ![![8967, -57206, 10242, -1956, 7504]] 
 ![![971, 0, 0, 0, 0], ![500, 1, 0, 0, 0], ![518, 0, 1, 0, 0], ![257, 0, 0, 1, 0], ![576, 0, 0, 0, 1]] where
  M :=![![![8967, -57206, 10242, -1956, 7504], ![3912, -24961, 4462, -854, 3272], ![1708, -10884, 1925, -374, 1420], ![748, -4720, 774, -167, 596], ![1136, -7208, 1246, -250, 931]]]
  hmulB := by decide  
  f := ![![![693, -1814, 906, 412, -856]], ![![356, -929, 458, 214, -440]], ![![366, -968, 501, 206, -444]], ![![211, -562, 312, 129, -284]], ![![416, -1056, 466, 282, -533]]]
  g := ![![![20069, -57206, 10242, -1956, 7504], ![8762, -24961, 4462, -854, 3272], ![3836, -10884, 1925, -374, 1420], ![1709, -4720, 774, -167, 596], ![2562, -7208, 1246, -250, 931]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI971N1 : Nat.card (O ⧸ I971N1) = 971 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI971N1)

lemma isPrimeI971N1 : Ideal.IsPrime I971N1 := prime_ideal_of_norm_prime hp971.out _ NI971N1

def I971N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, 61, -72, 13, 8]] i)))

def SI971N2: IdealEqSpanCertificate' Table ![![-15, 61, -72, 13, 8]] 
 ![![971, 0, 0, 0, 0], ![556, 1, 0, 0, 0], ![613, 0, 1, 0, 0], ![964, 0, 0, 1, 0], ![316, 0, 0, 0, 1]] where
  M :=![![![-15, 61, -72, 13, 8], ![-26, -21, 172, -114, 94], ![228, -630, 483, 212, -496], ![-424, 2636, -4458, 1051, 280], ![-602, 1314, -424, -900, 1457]]]
  hmulB := by decide  
  f := ![![![-7898895, 50426413, -9030762, 1723911, -6615542]], ![![-4526502, 28897113, -5175124, 987896, -3791070]], ![![-4988185, 31844489, -5702963, 1088657, -4177742]], ![![-7842628, 50067204, -8966430, 1711631, -6568416]], ![![-2571626, 16417216, -2940124, 561250, -2153807]]]
  g := ![![![-5, 61, -72, 13, 8], ![-14, -21, 172, -114, 94], ![7, -630, 483, 212, -496], ![170, 2636, -4458, 1051, 280], ![-66, 1314, -424, -900, 1457]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI971N2 : Nat.card (O ⧸ I971N2) = 971 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI971N2)

lemma isPrimeI971N2 : Ideal.IsPrime I971N2 := prime_ideal_of_norm_prime hp971.out _ NI971N2

def I971N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-353, 850, -145, 33, -108]] i)))

def SI971N3: IdealEqSpanCertificate' Table ![![-353, 850, -145, 33, -108]] 
 ![![971, 0, 0, 0, 0], ![675, 1, 0, 0, 0], ![745, 0, 1, 0, 0], ![103, 0, 0, 1, 0], ![472, 0, 0, 0, 1]] where
  M :=![![![-353, 850, -145, 33, -108], ![-66, 145, -23, 5, -18], ![-10, 16, -2, 3, -6], ![-6, 20, -29, 4, 6], ![-94, 230, -35, 1, -19]]]
  hmulB := by decide  
  f := ![![![2233, 26386, -57325, -3257, -20616]], ![![1559, 18423, -40024, -2274, -14394]], ![![1733, 20482, -44495, -2528, -16002]], ![![295, 3498, -7590, -431, -2730]], ![![1122, 13266, -28815, -1637, -10363]]]
  g := ![![![-431, 850, -145, 33, -108], ![-75, 145, -23, 5, -18], ![-7, 16, -2, 3, -6], ![5, 20, -29, 4, 6], ![-124, 230, -35, 1, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI971N3 : Nat.card (O ⧸ I971N3) = 971 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI971N3)

lemma isPrimeI971N3 : Ideal.IsPrime I971N3 := prime_ideal_of_norm_prime hp971.out _ NI971N3
def MulI971N0 : IdealMulLeCertificate' Table 
  ![![-91, -565, 1585, 98, 558]] ![![8967, -57206, 10242, -1956, 7504]]
  ![![388095, -2427053, 369193, -88150, 297062]] where
 M := ![![![388095, -2427053, 369193, -88150, 297062]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI971N1 : IdealMulLeCertificate' Table 
  ![![388095, -2427053, 369193, -88150, 297062]] ![![-15, 61, -72, 13, 8]]
  ![![2233, 26386, -57325, -3257, -20616]] where
 M := ![![![2233, 26386, -57325, -3257, -20616]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI971N2 : IdealMulLeCertificate' Table 
  ![![2233, 26386, -57325, -3257, -20616]] ![![-353, 850, -145, 33, -108]]
  ![![971, 0, 0, 0, 0]] where
 M := ![![![971, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC971 : ContainsPrimesAboveP 971 ![I971N0, I971N1, I971N2, I971N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI971N0
    exact isPrimeI971N1
    exact isPrimeI971N2
    exact isPrimeI971N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 971 (by decide) (𝕀 ⊙ MulI971N0 ⊙ MulI971N1 ⊙ MulI971N2)
instance hp977 : Fact (Nat.Prime 977) := {out := by norm_num}

def I977N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2003987, 5125344, -876391, 196651, -654144]] i)))

def SI977N0: IdealEqSpanCertificate' Table ![![-2003987, 5125344, -876391, 196651, -654144]] 
 ![![977, 0, 0, 0, 0], ![0, 977, 0, 0, 0], ![0, 0, 977, 0, 0], ![626, 446, 39, 1, 0], ![373, 611, 160, 0, 1]] where
  M :=![![![-2003987, 5125344, -876391, 196651, -654144], ![-393302, 1005891, -171999, 38595, -128382], ![-77190, 197416, -33762, 7575, -25194], ![-15150, 38736, -6605, 1476, -4938], ![-503842, 1288614, -220331, 49443, -164473]]]
  hmulB := by decide  
  f := ![![![57, -256, -93, -21, -12]], ![![42, 63, -427, -27, -150]], ![![54, 588, -1368, -73, -462]], ![![58, -110, -313, -29, -96]], ![![57, 39, -529, -37, -175]]]
  g := ![![![121687, 324566, 98380, 196651, -654144], ![23882, 63699, 19308, 38595, -128382], ![4686, 12500, 3789, 7575, -25194], ![924, 2454, 743, 1476, -4938], ![30597, 81607, 24736, 49443, -164473]]]
  hle1 := by decide   
  hle2 := by decide  


def P977P0 : CertificateIrreducibleZModOfList' 977 3 2 9 [579, 336, 823, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [696, 779, 205], [435, 197, 772], [0, 1]]
 g := ![![[748, 520, 616], [207, 162], [388, 375], [550, 558], [491, 677, 772], [433, 205], [764, 873, 62], [34, 312, 268], [1]], ![[893, 488, 830, 930], [249, 301], [754, 723], [491, 633], [877, 930, 640, 676], [749, 581], [714, 615, 822, 306], [457, 531, 108, 856], [343, 399, 853, 916]], ![[871, 474, 609, 94], [70, 488], [741, 306], [393, 863], [709, 575, 586, 862], [159, 121], [775, 817, 217, 349], [835, 547, 237, 863], [25, 230, 82, 61]]]
 h' := ![![[696, 779, 205], [921, 164, 880], [746, 124, 46], [376, 66, 350], [18, 106, 436], [203, 475, 434], [225, 688, 921], [831, 527, 471], [398, 641, 154], [0, 1]], ![[435, 197, 772], [69, 273, 833], [312, 752, 287], [797, 544, 412], [263, 809, 152], [609, 559, 174], [591, 293, 67], [837, 294, 537], [340, 571, 538], [696, 779, 205]], ![[0, 1], [758, 540, 241], [715, 101, 644], [614, 367, 215], [181, 62, 389], [196, 920, 369], [448, 973, 966], [146, 156, 946], [805, 742, 285], [435, 197, 772]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [679, 100], []]
 b := ![[], [283, 522, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI977N0 : CertifiedPrimeIdeal' SI977N0 977 where
  n := 3
  hpos := by decide
  P := [579, 336, 823, 1]
  hirr := P977P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10219909, -29995470, 23171340, 14467880, -21152500]
  a := ![-8, 28, 13, -9, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1184023, 6593150, 2910260, 14467880, -21152500]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI977N0 : Ideal.IsPrime I977N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI977N0 B_one_repr
lemma NI977N0 : Nat.card (O ⧸ I977N0) = 932574833 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI977N0

def I977N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, -256, -93, -21, -12]] i)))

def SI977N1: IdealEqSpanCertificate' Table ![![57, -256, -93, -21, -12]] 
 ![![977, 0, 0, 0, 0], ![0, 977, 0, 0, 0], ![103, 938, 1, 0, 0], ![109, 536, 0, 1, 0], ![716, 444, 0, 0, 1]] where
  M :=![![![57, -256, -93, -21, -12], ![42, 63, -427, -27, -150], ![54, 588, -1368, -73, -462], ![146, 1756, -3789, -298, -1362], ![126, 1018, -2367, -139, -929]]]
  hmulB := by decide  
  f := ![![![-2003987, 5125344, -876391, 196651, -654144]], ![![-393302, 1005891, -171999, 38595, -128382]], ![![-588951, 1506278, -257561, 57794, -192246]], ![![-439365, 1123704, -192144, 43115, -143418]], ![![-1647886, 4214586, -720659, 161707, -537905]]]
  g := ![![![21, 106, -93, -21, -12], ![158, 493, -427, -27, -150], ![491, 1564, -1368, -73, -462], ![1431, 4422, -3789, -298, -1362], ![946, 2772, -2367, -139, -929]]]
  hle1 := by decide   
  hle2 := by decide  


def P977P1 : CertificateIrreducibleZModOfList' 977 2 2 9 [369, 165, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [812, 976], [0, 1]]
 g := ![![[342, 50], [699], [725], [61], [407, 396], [704], [526, 912], [580, 865], [812, 1]], ![[885, 927], [699], [725], [61], [526, 581], [704], [504, 65], [497, 112], [647, 976]]]
 h' := ![![[812, 976], [372, 894], [350, 896], [358, 227], [275, 914], [877, 702], [329, 41], [920, 338], [311, 477], [0, 1]], ![[0, 1], [389, 83], [37, 81], [29, 750], [900, 63], [333, 275], [403, 936], [839, 639], [743, 500], [812, 976]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [183]]
 b := ![[], [954, 580]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI977N1 : CertifiedPrimeIdeal' SI977N1 977 where
  n := 2
  hpos := by decide
  P := [369, 165, 1]
  hirr := P977P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9699, -47202, 70058, -9376, -11002]
  a := ![10, -11, -15, 12, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1733, -57166, 70058, -9376, -11002]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI977N1 : Ideal.IsPrime I977N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI977N1 B_one_repr
lemma NI977N1 : Nat.card (O ⧸ I977N1) = 954529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI977N1
def MulI977N0 : IdealMulLeCertificate' Table 
  ![![-2003987, 5125344, -876391, 196651, -654144]] ![![57, -256, -93, -21, -12]]
  ![![977, 0, 0, 0, 0]] where
 M := ![![![977, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC977 : ContainsPrimesAboveP 977 ![I977N0, I977N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI977N0
    exact isPrimeI977N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 977 (by decide) (𝕀 ⊙ MulI977N0)
instance hp983 : Fact (Nat.Prime 983) := {out := by norm_num}

def I983N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![983, 0, 0, 0, 0]] i)))

def SI983N0: IdealEqSpanCertificate' Table ![![983, 0, 0, 0, 0]] 
 ![![983, 0, 0, 0, 0], ![0, 983, 0, 0, 0], ![0, 0, 983, 0, 0], ![0, 0, 0, 983, 0], ![0, 0, 0, 0, 983]] where
  M :=![![![983, 0, 0, 0, 0], ![0, 983, 0, 0, 0], ![0, 0, 983, 0, 0], ![0, 0, 0, 983, 0], ![0, 0, 0, 0, 983]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P983P0 : CertificateIrreducibleZModOfList' 983 5 2 9 [205, 976, 737, 910, 737, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [833, 579, 522, 796, 587], [146, 872, 220, 334, 510], [535, 107, 145, 49, 296], [698, 407, 96, 787, 573], [0, 1]]
 g := ![![[720, 434, 868, 373, 50], [82, 325, 160, 593, 46], [76, 707, 59, 746, 770], [700, 367, 823, 21], [142, 280, 878, 665, 505], [914, 431, 883, 334], [332, 574, 522, 328, 152], [626, 246, 1], []], ![[804, 346, 47, 833, 963, 48, 916, 260], [272, 458, 17, 61, 932, 362, 370, 505], [227, 680, 364, 74, 428, 765, 631, 151], [484, 867, 236, 843], [486, 380, 846, 405, 472, 951, 530, 913], [21, 165, 315, 287], [542, 303, 851, 89, 816, 924, 779, 212], [318, 926, 548, 246, 32, 579, 955, 600], [750, 37, 685, 408, 131, 350, 527, 906]], ![[261, 341, 234, 14, 452, 614, 60, 698], [158, 720, 745, 115, 943, 119, 281, 163], [793, 133, 783, 827, 607, 321, 465, 346], [131, 924, 614, 827], [247, 924, 771, 628, 130, 489, 291, 879], [568, 773, 423, 165], [159, 493, 160, 102, 425, 975, 444, 505], [228, 171, 9, 41, 244, 488, 742, 623], [367, 879, 25, 863, 212, 450, 621, 65]], ![[606, 745, 645, 472, 748, 153, 129, 565], [174, 725, 957, 740, 777, 609, 295, 191], [511, 577, 960, 886, 187, 51, 492, 734], [279, 54, 250, 112], [550, 428, 652, 189, 453, 176, 370, 342], [969, 706, 592, 922], [591, 173, 452, 261, 49, 379, 703, 84], [454, 144, 168, 677, 802, 464, 769, 248], [260, 546, 377, 76, 657, 181, 2, 830]], ![[976, 361, 290, 493, 183, 236, 319, 745], [275, 43, 55, 258, 196, 583, 325, 802], [914, 818, 865, 5, 715, 124, 435, 282], [408, 202, 300, 718], [890, 751, 647, 569, 647, 357, 900, 368], [27, 494, 883, 59], [523, 650, 158, 313, 978, 545, 172, 42], [226, 118, 224, 42, 199, 135, 296, 856], [377, 590, 126, 207, 968, 455, 573, 79]]]
 h' := ![![[833, 579, 522, 796, 587], [884, 88, 380, 493, 284], [148, 106, 605, 254, 631], [900, 439, 173, 408, 653], [380, 432, 180, 190, 612], [607, 816, 824, 958, 407], [750, 297, 210, 779, 298], [443, 153, 199, 57, 175], [0, 0, 0, 1], [0, 1]], ![[146, 872, 220, 334, 510], [233, 217, 857, 115, 257], [846, 483, 32, 741, 252], [132, 661, 84, 973, 769], [740, 453, 491, 118, 930], [959, 154, 911, 147, 5], [378, 284, 597, 338, 642], [126, 971, 137, 240, 476], [220, 17, 58, 908, 286], [833, 579, 522, 796, 587]], ![[535, 107, 145, 49, 296], [66, 197, 561, 920, 971], [171, 288, 206, 71, 837], [959, 167, 342, 496, 594], [374, 954, 359, 532, 360], [599, 453, 334, 438, 540], [738, 735, 549, 150, 682], [29, 318, 198, 561, 239], [414, 312, 666, 280, 630], [146, 872, 220, 334, 510]], ![[698, 407, 96, 787, 573], [533, 863, 256, 930, 549], [96, 374, 833, 306, 370], [332, 926, 505, 643, 467], [716, 712, 781, 853, 657], [659, 146, 549, 625, 223], [52, 14, 844, 624, 389], [142, 939, 69, 299, 641], [383, 150, 865, 175, 108], [535, 107, 145, 49, 296]], ![[0, 1], [291, 601, 895, 491, 888], [241, 715, 290, 594, 859], [696, 756, 862, 429, 466], [941, 398, 155, 273, 390], [6, 397, 331, 781, 791], [511, 636, 749, 75, 938], [546, 568, 380, 809, 435], [897, 504, 377, 602, 942], [698, 407, 96, 787, 573]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82, 857, 347, 602], [], [], []]
 b := ![[], [289, 374, 335, 702, 215], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI983N0 : CertifiedPrimeIdeal' SI983N0 983 where
  n := 5
  hpos := by decide
  P := [205, 976, 737, 910, 737, 1]
  hirr := P983P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11433319247201, -29059091927332, 18056683280092, 13096704121568, -25951191848964]
  a := ![-6, 6, 10, -16, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11631047047, -29561639804, 18368955524, 13323198496, -26399991708]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI983N0 : Ideal.IsPrime I983N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI983N0 B_one_repr
lemma NI983N0 : Nat.card (O ⧸ I983N0) = 917841286185143 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI983N0

def PBC983 : ContainsPrimesAboveP 983 ![I983N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI983N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![983, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 983 (by decide) 𝕀



lemma PB984I18_primes (p : ℕ) :
  p ∈ Set.range ![967, 971, 977, 983] ↔ Nat.Prime p ∧ 953 < p ∧ p ≤ 983 := by
  rw [← List.mem_ofFn']
  convert primes_range 953 983 (by omega)

def PB984I18 : PrimesBelowBoundCertificateInterval O 953 983 984 where
  m := 4
  g := ![3, 4, 2, 1]
  P := ![967, 971, 977, 983]
  hP := PB984I18_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I967N0, I967N1, I967N2]
    · exact ![I971N0, I971N1, I971N2, I971N3]
    · exact ![I977N0, I977N1]
    · exact ![I983N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC967
    · exact PBC971
    · exact PBC977
    · exact PBC983
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![935089, 935089, 967]
    · exact ![942841, 971, 971, 971]
    · exact ![932574833, 954529]
    · exact ![917841286185143]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI967N0
      exact NI967N1
      exact NI967N2
    · dsimp ; intro j
      fin_cases j
      exact NI971N0
      exact NI971N1
      exact NI971N2
      exact NI971N3
    · dsimp ; intro j
      fin_cases j
      exact NI977N0
      exact NI977N1
    · dsimp ; intro j
      fin_cases j
      exact NI983N0
  β := ![I967N2, I971N1, I971N2, I971N3]
  Il := ![[I967N2], [I971N1, I971N2, I971N3], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
