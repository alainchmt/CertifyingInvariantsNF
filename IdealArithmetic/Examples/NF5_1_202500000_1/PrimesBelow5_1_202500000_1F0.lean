
import IdealArithmetic.Examples.NF5_1_202500000_1.RI5_1_202500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32, -64, 30, -8, -3]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![32, -64, 30, -8, -3]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![32, -64, 30, -8, -3], ![-30, 97, -47, 73, -35], ![-350, 562, -268, -275, 257], ![1460, -2760, 1318, 273, -550], ![-740, 1694, -811, 471, -84]]]
  hmulB := by decide  
  f := ![![![3791, -5750, 213, 307, 902]], ![![4510, -6827, 235, 357, 1065]], ![![10650, -16082, 506, 821, 2493]], ![![7140, -10728, 274, 521, 1642]], ![![11465, -17236, 452, 842, 2642]]]
  g := ![![![16, -64, 30, -8, -3], ![-15, 97, -47, 73, -35], ![-175, 562, -268, -275, 257], ![730, -2760, 1318, 273, -550], ![-370, 1694, -811, 471, -84]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12827, 6323, 547, 65, -916]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-12827, 6323, 547, 65, -916]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-12827, 6323, 547, 65, -916], ![-9160, 4512, 393, 48, -656], ![-6560, 3256, 265, 34, -464], ![960, -517, -13, -18, 68], ![-3280, 1605, 149, 31, -247]]]
  hmulB := by decide  
  f := ![![![-7886, 12251, -787, -794, -2032]], ![![-10160, 15758, -983, -1009, -2604]], ![![-26040, 40325, -2444, -2552, -6640]], ![![-24123, 37299, -2195, -2333, -6120]], ![![-35843, 55416, -3256, -3464, -9091]]]
  g := ![![![-5988, 6323, 547, 65, -916], ![-4276, 4512, 393, 48, -656], ![-3065, 3256, 265, 34, -464], ![455, -517, -13, -18, 68], ![-1532, 1605, 149, 31, -247]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67237, 33145, 2867, 343, -4803]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-67237, 33145, 2867, 343, -4803]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-67237, 33145, 2867, 343, -4803], ![-48030, 23677, 2048, 245, -3431], ![-34310, 16914, 1463, 175, -2451], ![4900, -2415, -209, -25, 350], ![-17260, 8509, 736, 88, -1233]]]
  hmulB := by decide  
  f := ![![![4, -8, 3, 1, 1]], ![![7, -12, 2, 3, 3]], ![![27, -49, 9, -1, 13]], ![![50, -83, 22, 16, -3]], ![![27, -36, -10, 11, 18]]]
  g := ![![![-49223, 33145, 2867, 343, -4803], ![-35162, 23677, 2048, 245, -3431], ![-25118, 16914, 1463, 175, -2451], ![3587, -2415, -209, -25, 350], ![-12636, 8509, 736, 88, -1233]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![32, -64, 30, -8, -3]] ![![-12827, 6323, 547, 65, -916]]
  ![![-18864, 10569, -41, 79, -1051]] where
 M := ![![![-18864, 10569, -41, 79, -1051]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-18864, 10569, -41, 79, -1051]] ![![-12827, 6323, 547, 65, -916]]
  ![![148948568, -73450938, -6333482, -754245, 10630153]] where
 M := ![![![148948568, -73450938, -6333482, -754245, 10630153]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![148948568, -73450938, -6333482, -754245, 10630153]] ![![-67237, 33145, 2867, 343, -4803]]
  ![![-6456876788336, 3182951386338, 275323569079, 32939829253, -461237403843]] where
 M := ![![![-6456876788336, 3182951386338, 275323569079, 32939829253, -461237403843]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-6456876788336, 3182951386338, 275323569079, 32939829253, -461237403843]] ![![-67237, 33145, 2867, 343, -4803]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![279939880630102882, -137997837084615770, -11936738084918836, -1428116411427122, 19997089599216470]]]
 hmul := by decide  
 g := ![![![![139969940315051441, -68998918542307885, -5968369042459418, -714058205713561, 9998544799608235]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, -300, 23, 21, 51]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![191, -300, 23, 21, 51]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 2, 0, 1, 0], ![1, 1, 0, 0, 1]] where
  M :=![![![191, -300, 23, 21, 51], ![510, -799, 59, 55, 135], ![1350, -2110, 150, 143, 355], ![1100, -1714, 116, 113, 286], ![1730, -2696, 183, 179, 450]]]
  hmulB := by decide  
  f := ![![![-1387, 684, 59, 7, -99]], ![![-990, 487, 43, 5, -71]], ![![-699, 346, 29, 4, -50]], ![![-1089, 536, 47, 4, -77]], ![![-909, 445, 41, 5, -66]]]
  g := ![![![32, -131, 23, 21, 51], ![87, -348, 59, 55, 135], ![234, -917, 150, 143, 355], ![195, -742, 116, 113, 286], ![306, -1168, 183, 179, 450]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2], [0, 1]]
 g := ![![[2, 1]], ![[1, 2]]]
 h' := ![![[2, 2], [0, 1]], ![[0, 1], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15604, -27233, 9216, 3909, -2207]
  a := ![1, 3, 1, 2, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1562, -10948, 9216, 3909, -2207]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-897, 649, -303, -2334, 1628]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-897, 649, -303, -2334, 1628]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-897, 649, -303, -2334, 1628], ![16280, -29495, 14076, 5690, -7708], ![-77080, 157042, -75065, 9064, 15052], ![113800, -264587, 126671, -81135, 18128], ![87020, -137781, 65617, 71556, -65703]]]
  hmulB := by decide  
  f := ![![![5757901, -2838495, -245487, -29356, 411332]], ![![3290407, -1622182, -140263, -16762, 235080]], ![![4818294, -2375664, -205347, -24516, 344284]], ![![1779767, -877774, -75804, -9025, 127220]], ![![2412507, -1189900, -102742, -12226, 172461]]]
  g := ![![![-78, 649, -303, -2334, 1628], ![6547, -29495, 14076, 5690, -7708], ![-36036, 157042, -75065, 9064, 15052], ![62684, -264587, 126671, -81135, 18128], ![29238, -137781, 65617, 71556, -65703]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![191, -300, 23, 21, 51]] ![![-897, 649, -303, -2334, 1628]]
  ![![-347, 1267, -610, 1199, -621]] where
 M := ![![![-347, 1267, -610, 1199, -621]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-347, 1267, -610, 1199, -621]] ![![-897, 649, -303, -2334, 1628]]
  ![![150363599, -365068800, 174859455, -139227053, 43024363]] where
 M := ![![![150363599, -365068800, 174859455, -139227053, 43024363]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![150363599, -365068800, 174859455, -139227053, 43024363]] ![![-897, 649, -303, -2334, 1628]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-31656421566843, 69235297277469, -33122993992464, 13531574252037, 339989027259]]]
 hmul := by decide  
 g := ![![![![-10552140522281, 23078432425823, -11040997997488, 4510524750679, 113329675753]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1123125, 1831602, -872703, -813149, 782253]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-1123125, 1831602, -872703, -813149, 782253]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-1123125, 1831602, -872703, -813149, 782253], ![7822530, -15172783, 7247819, 663145, -2470343], ![-24703430, 54095902, -25880510, 10699005, 182237], ![13262900, -46480420, 22336278, -41837899, 21398010], ![55906250, -101374778, 48379923, 19358179, -26361418]]]
  hmulB := by decide  
  f := ![![![-4664138945, 2299213502, 198879911, 23793807, -333176283]], ![![-666352566, 328483325, 28413125, 3399185, -47600211]], ![![-476002110, 234652258, 20295788, 2427669, -34003471]], ![![67983700, -33508044, -2899854, -347451, 4855338]], ![![-239458474, 118049806, 10209031, 1220621, -17106868]]]
  g := ![![![-224625, 1831602, -872703, -813149, 782253], ![1564506, -15172783, 7247819, 663145, -2470343], ![-4940686, 54095902, -25880510, 10699005, 182237], ![2652580, -46480420, 22336278, -41837899, 21398010], ![11181250, -101374778, 48379923, 19358179, -26361418]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-1123125, 1831602, -872703, -813149, 782253]] ![![-1123125, 1831602, -872703, -813149, 782253]]
  ![![70096046739125, -118562490819976, 56523890838540, 41954271249638, -43583360604966]] where
 M := ![![![70096046739125, -118562490819976, 56523890838540, 41954271249638, -43583360604966]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![70096046739125, -118562490819976, 56523890838540, 41954271249638, -43583360604966]] ![![-1123125, 1831602, -872703, -813149, 782253]]
  ![![-4282666194129937424405, 7453223221356095264126, -3554816990245631822873, -2129846321757130633921, 2404680708898963756541]] where
 M := ![![![-4282666194129937424405, 7453223221356095264126, -3554816990245631822873, -2129846321757130633921, 2404680708898963756541]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-4282666194129937424405, 7453223221356095264126, -3554816990245631822873, -2129846321757130633921, 2404680708898963756541]] ![![-1123125, 1831602, -872703, -813149, 782253]]
  ![![257117946497430575027873429145, -458009131541748941224421291992, 218523013170896231649084503444, 106050543589403153484994867068, -131375231689766801818600238932]] where
 M := ![![![257117946497430575027873429145, -458009131541748941224421291992, 218523013170896231649084503444, 106050543589403153484994867068, -131375231689766801818600238932]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![257117946497430575027873429145, -458009131541748941224421291992, 218523013170896231649084503444, 106050543589403153484994867068, -131375231689766801818600238932]] ![![-1123125, 1831602, -872703, -813149, 782253]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-15207992516759647335396377414624218605, 27630271555164419044041845653882029050, -13186591086217497126333867459474640155, -5154940038887732463035597979541824185, 7104901905045191438452209942802541425]]]
 hmul := by decide  
 g := ![![![![-3041598503351929467079275482924843721, 5526054311032883808808369130776405810, -2637318217243499425266773491894928031, -1030988007777546492607119595908364837, 1420980381009038287690441988560508285]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8927605761, 4400910233, 380676349, 45544280, -637730258]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-8927605761, 4400910233, 380676349, 45544280, -637730258]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![1, 2, 6, 4, 1]] where
  M :=![![![-8927605761, 4400910233, 380676349, 45544280, -637730258], ![-6377302580, 3143724861, 271930496, 32533880, -455553138], ![-4555531380, 2245673162, 194249511, 23240094, -325417618], ![650677600, -320754947, -27745129, -3319439, 46480188], ![-2291669220, 1129690399, 97717607, 11690976, -163701987]]]
  hmulB := by decide  
  f := ![![![-7, 37, -19, 42, -26]], ![![-260, 445, -206, -148, 142]], ![![1420, -2810, 1381, 26, -450]], ![![-2960, 6377, -2993, 1117, 52]], ![![-701, 1558, -666, 408, -165]]]
  g := ![![![-1184267929, 810910107, 601008271, 370923616, -637730258], ![-845964206, 579261591, 429321332, 264963776, -455553138], ![-604301966, 413786914, 306679317, 189272938, -325417618], ![86313916, -59102189, -43803751, -27034313, 46480188], ![-303995319, 208156339, 154275647, 95214132, -163701987]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [3, 2, 5, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 3, 3, 5], [1, 2, 1, 2], [1, 1, 3], [0, 1]]
 g := ![![[0, 6, 2, 1], []], ![[2, 6, 0, 2, 0, 3], [5, 4, 1, 6, 6, 6]], ![[2, 3, 6, 5, 2, 2], [5, 0, 1, 4, 0, 1]], ![[5, 0, 2, 0, 3], [0, 4, 6]]]
 h' := ![![[0, 3, 3, 5], [0, 0, 0, 1], [0, 1]], ![[1, 2, 1, 2], [6, 6, 6, 4], [0, 3, 3, 5]], ![[1, 1, 3], [0, 3, 1, 1], [1, 2, 1, 2]], ![[0, 1], [1, 5, 0, 1], [1, 1, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2, 0, 6], []]
 b := ![[], [], [2, 1, 4, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [3, 2, 5, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![243293324676, -468961209718, 218556786837, 20294717161, -71457216289]
  a := ![1, -6, -3, -7, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![44964362995, -46578111020, 92471440653, 43731940331, -71457216289]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 37, -19, 42, -26]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-7, 37, -19, 42, -26]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-7, 37, -19, 42, -26], ![-260, 445, -206, -148, 142], ![1420, -2810, 1381, 26, -450], ![-2960, 6377, -2993, 1117, 52], ![-1060, 1331, -545, -1514, 1079]]]
  hmulB := by decide  
  f := ![![![-8927605761, 4400910233, 380676349, 45544280, -637730258]], ![![-6012532232, 2963909399, 256376556, 30673000, -429496310]], ![![-7027651455, 3464317761, 299661608, 35851642, -502009844]], ![![-6283907315, 3097685174, 267948088, 32057423, -448881586]], ![![-6704242575, 3304891652, 285871336, 34201768, -478907611]]]
  g := ![![![-20, 37, -19, 42, -26], ![-140, 445, -206, -148, 142], ![1125, -2810, 1381, 26, -450], ![-2764, 6377, -2993, 1117, 52], ![-212, 1331, -545, -1514, 1079]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-8927605761, 4400910233, 380676349, 45544280, -637730258]] ![![-7, 37, -19, 42, -26]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6599, -10135, 518, 601, 1637]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![6599, -10135, 518, 601, 1637]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![6, 2, 5, 2, 1]] where
  M :=![![![6599, -10135, 518, 601, 1637], ![16370, -25105, 1241, 1471, 4041], ![40410, -61880, 2952, 3581, 9925], ![29420, -44933, 2007, 2543, 7162], ![46810, -71513, 3218, 4057, 11406]]]
  hmulB := by decide  
  f := ![![![-291, 141, 14, 1, -21]], ![![-210, 107, 7, 5, -17]], ![![-170, 108, -10, -13, 3]], ![![100, -161, 71, 11, -26]], ![![-266, 127, 14, 0, -19]]]
  g := ![![![-293, -1219, -697, -243, 1637], ![-716, -3017, -1724, -601, 4041], ![-1740, -7430, -4243, -1479, 9925], ![-1232, -5387, -3073, -1071, 7162], ![-1966, -8575, -4892, -1705, 11406]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [10, 6, 10, 7, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 3, 9, 6], [6, 8, 10, 7], [1, 10, 3, 9], [0, 1]]
 g := ![![[8, 2, 10, 3], [4, 1], []], ![[0, 8, 3, 4, 2, 7], [7, 1, 0, 8, 3, 6], [6, 10, 3]], ![[5, 5, 0, 10, 9, 8], [4, 7, 5, 10, 5, 2], [10, 6, 5]], ![[2, 3, 0, 8, 9, 4], [2, 3, 5, 8, 1, 4], [0, 4, 4]]]
 h' := ![![[8, 3, 9, 6], [4, 10, 9, 6], [0, 0, 1], [0, 1]], ![[6, 8, 10, 7], [3, 7, 7, 5], [4, 0, 3, 1], [8, 3, 9, 6]], ![[1, 10, 3, 9], [6, 0, 7, 3], [2, 9, 9, 7], [6, 8, 10, 7]], ![[0, 1], [3, 5, 10, 8], [1, 2, 9, 3], [1, 10, 3, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 2, 3], []]
 b := ![[], [], [0, 5, 9, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [10, 6, 10, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54150135608, -98487414664, 46729971610, 17806566282, -24715843224]
  a := ![-1, 7, 5, 9, -28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![18404108632, -4459611656, 15482653430, 6112568430, -24715843224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-291, 141, 14, 1, -21]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-291, 141, 14, 1, -21]] 
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-291, 141, 14, 1, -21], ![-210, 107, 7, 5, -17], ![-170, 108, -10, -13, 3], ![100, -161, 71, 11, -26], ![-110, 119, -36, 27, -12]]]
  hmulB := by decide  
  f := ![![![6599, -10135, 518, 601, 1637]], ![![2688, -4125, 207, 243, 665]], ![![7873, -12075, 598, 708, 1944]], ![![6274, -9613, 465, 559, 1544]], ![![7255, -11108, 528, 642, 1781]]]
  g := ![![![-52, 141, 14, 1, -21], ![-38, 107, 7, 5, -17], ![-23, 108, -10, -13, 3], ![-1, -161, 71, 11, -26], ![-18, 119, -36, 27, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![6599, -10135, 518, 601, 1637]] ![![-291, 141, 14, 1, -21]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1383, 2646, -1264, -196, 484]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-1383, 2646, -1264, -196, 484]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![8, 5, 4, 1, 0], ![1, 4, 9, 0, 1]] where
  M :=![![![-1383, 2646, -1264, -196, 484], ![4840, -10383, 4966, -1652, -300], ![-3000, 12192, -5865, 12936, -6908], ![-33040, 51562, -24550, -28723, 25872], ![48620, -97738, 46710, -2986, -11121]]]
  hmulB := by decide  
  f := ![![![-6251, 8866, 428, -156, -1140]], ![![-11400, 15565, 1470, 28, -1764]], ![![-17640, 22088, 4659, 1120, -1652]], ![![-13616, 17875, 2624, 425, -1716]], ![![-16307, 20456, 4269, 1018, -1545]]]
  g := ![![![-23, 130, -372, -196, 484], ![1412, -71, 1098, -1652, -300], ![-7660, -1912, 351, 12936, -6908], ![13144, 7053, -10962, -28723, 25872], ![6433, -2948, 12211, -2986, -11121]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [8, 7, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 8, 11], [12, 4, 2], [0, 1]]
 g := ![![[1, 3, 3], [8, 3], [1]], ![[9, 2, 9, 5], [4, 3], [3, 1, 12, 5]], ![[0, 8, 1, 7], [11, 12], [4, 10, 2, 8]]]
 h' := ![![[5, 8, 11], [0, 6, 9], [5, 6, 4], [0, 1]], ![[12, 4, 2], [3, 6, 11], [10, 12, 4], [5, 8, 11]], ![[0, 1], [0, 1, 6], [6, 8, 5], [12, 4, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 4], []]
 b := ![[], [1, 2, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [8, 7, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3986392, 5205460, 283902, -2502710, -231040]
  a := ![0, 4, -2, -6, -16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1251256, 1434090, 951854, -2502710, -231040]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![93, -166, 39, -11, 19]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![93, -166, 39, -11, 19]] 
 ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![93, -166, 39, -11, 19], ![190, -257, 17, 119, -25], ![-250, 546, -534, -229, 451], ![2380, -4568, 1966, 35, -458], ![30, 550, -607, 841, -202]]]
  hmulB := by decide  
  f := ![![![2228856241, -1098726410, -95039239, -11370535, 159215035]], ![![465374064, -229408593, -19843719, -2374111, 33243305]], ![![1630541163, -803783844, -69526867, -8318224, 116475286]], ![![1016206922, -500944548, -43331432, -5184191, 72591232]], ![![1072713312, -528799670, -45740885, -5472459, 76627682]]]
  g := ![![![2, -166, 39, -11, 19], ![-1, -257, 17, 119, -25], ![164, 546, -534, -229, 451], ![-280, -4568, 1966, 35, -458], ![43, 550, -607, 841, -202]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3331433813, -1642246852, -142053661, -16995437, 237975861]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![3331433813, -1642246852, -142053661, -16995437, 237975861]] 
 ![![13, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![3331433813, -1642246852, -142053661, -16995437, 237975861], ![2379758610, -1173112109, -101474049, -12140587, 169994113], ![1699941130, -837988950, -72486780, -8672811, 121431765], ![-242811740, 119699678, 10353108, 1238319, -17345622], ![855155010, -421546236, -36464875, -4363201, 61085572]]]
  hmulB := by decide  
  f := ![![![238161, 20940, -13103, 1019727, -670491]], ![![-442482, 926271, -442903, 103289, 55881]], ![![2805060, -5270714, 2516652, 589795, -1095469]], ![![-4191143, 9560470, -4576087, 2607234, -440797]], ![![-2496299, 3856748, -1835988, -2250794, 2002769]]]
  g := ![![![817232745, -1642246852, -142053661, -16995437, 237975861], ![583777368, -1173112109, -101474049, -12140587, 169994113], ![417010942, -837988950, -72486780, -8672811, 121431765], ![-59564845, 119699678, 10353108, 1238319, -17345622], ![209776553, -421546236, -36464875, -4363201, 61085572]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-1383, 2646, -1264, -196, 484]] ![![93, -166, 39, -11, 19]]
  ![![238161, 20940, -13103, 1019727, -670491]] where
 M := ![![![238161, 20940, -13103, 1019727, -670491]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![238161, 20940, -13103, 1019727, -670491]] ![![3331433813, -1642246852, -142053661, -16995437, 237975861]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3811308961, -1878804806, -162515597, -19443435, 272255195]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![3811308961, -1878804806, -162515597, -19443435, 272255195]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![8, 9, 0, 16, 1]] where
  M :=![![![3811308961, -1878804806, -162515597, -19443435, 272255195], ![2722551950, -1342096309, -116090603, -13889129, 194481455], ![1944814550, -958706566, -82927598, -9921493, 138924939], ![-277782580, 136934384, 11844750, 1417111, -19842986], ![978342870, -482279266, -41716895, -4991027, 69886470]]]
  hmulB := by decide  
  f := ![![![-143, 238, -31, -19, -49]], ![![-490, 807, -117, -73, -125]], ![![-1250, 1958, -112, -213, -417]], ![![-1460, 2464, -374, -1, -426]], ![![-1832, 3069, -456, -70, -517]]]
  g := ![![![96074553, -254653033, -9559741, -257383915, 272255195], ![68629430, -181907612, -6828859, -183858377, 194481455], ![49024414, -129943001, -4878094, -131336501, 138924939], ![-7002276, 18560074, 696750, 18759111, -19842986], ![24661830, -65368088, -2453935, -66069091, 69886470]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [2, 3, 6, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 7, 7, 7], [5, 7, 14, 9], [0, 2, 13, 1], [0, 1]]
 g := ![![[3, 13, 2, 9], [8, 11, 1], [1], []], ![[9, 3, 7, 0, 2, 7], [13, 12, 13], [9, 0, 15], [8, 15, 15]], ![[12, 7, 7, 5, 1, 8], [7, 7, 16], [1, 3, 4], [5, 1, 13]], ![[0, 0, 13, 2], [8, 4, 2], [7, 11, 8], [6, 8, 1]]]
 h' := ![![[11, 7, 7, 7], [5, 0, 1, 14], [15, 14, 11, 16], [0, 0, 1], [0, 1]], ![[5, 7, 14, 9], [4, 10, 12, 16], [8, 12, 9, 8], [3, 15, 12, 7], [11, 7, 7, 7]], ![[0, 2, 13, 1], [7, 16, 10, 4], [2, 0, 5, 4], [15, 2, 11, 15], [5, 7, 14, 9]], ![[0, 1], [3, 8, 11], [11, 8, 9, 6], [5, 0, 10, 12], [0, 2, 13, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [11, 1, 9], []]
 b := ![[], [], [6, 13, 8, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [2, 3, 6, 1, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![34408012243, -63743749120, 30266454050, 8917370933, -14288800209]
  a := ![13, 6, 4, 7, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8748141995, 3815026633, 1780379650, 13972833781, -14288800209]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![143, -238, 31, 19, 49]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![143, -238, 31, 19, 49]] 
 ![![17, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![143, -238, 31, 19, 49], ![490, -807, 117, 73, 125], ![1250, -1958, 112, 213, 417], ![1460, -2464, 374, 1, 426], ![2230, -3582, 467, 365, 456]]]
  hmulB := by decide  
  f := ![![![-3811308961, 1878804806, 162515597, 19443435, -272255195]], ![![-832734049, 410500631, 35508082, 4248202, -59485120]], ![![-1907958014, 940537942, 81356022, 9733469, -136292147]], ![![-207854493, 102462966, 8862991, 1060372, -14847777]], ![![-2523690673, 1244066596, 107611086, 12874636, -180276095]]]
  g := ![![![3, -238, 31, 19, 49], ![31, -807, 117, 73, 125], ![84, -1958, 112, 213, 417], ![69, -2464, 374, 1, 426], ![227, -3582, 467, 365, 456]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![3811308961, -1878804806, -162515597, -19443435, 272255195]] ![![143, -238, 31, 19, 49]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![237441, -551877, 264210, -168919, 37605]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![237441, -551877, 264210, -168919, 37605]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![14, 17, 2, 1, 0], ![12, 9, 13, 0, 1]] where
  M :=![![![237441, -551877, 264210, -168919, 37605], ![376050, -308135, 144487, 903863, -638071], ![-6380710, 11595536, -5534008, -2156823, 2977381], ![18077260, -36194831, 17297013, -810083, -4313646], ![-3246650, 9936089, -4769688, 7256855, -3460490]]]
  hmulB := by decide  
  f := ![![![-94972181, 46820351, 4049150, 484149, -6784797]], ![![-67847970, 33454813, 2891773, 345205, -4848201]], ![![-48482010, 23922644, 2063974, 244935, -3467381]], ![![-135425576, 66772492, 5772590, 689438, -9676393]], ![![-126577358, 62420650, 5393895, 643279, -9046102]]]
  g := ![![![113213, 104279, 5957, -168919, 37605], ![-243220, -522693, 349036, 903863, -638071], ![-627040, 1129742, -2101385, -2156823, 2977381], ![4272746, 863126, 3947083, -810083, -4313646], ![-3332460, -4330844, 1352788, 7256855, -3460490]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [8, 0, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 0, 15], [5, 18, 4], [0, 1]]
 g := ![![[18, 10, 5], [14, 8, 4], [13, 1], []], ![[8, 15, 4, 15], [18, 0, 7, 12], [3, 1], [18, 16]], ![[15, 8, 12, 9], [4, 15, 2, 11], [], [10, 16]]]
 h' := ![![[8, 0, 15], [2, 17, 9], [10, 11, 17], [0, 0, 1], [0, 1]], ![[5, 18, 4], [7, 7, 18], [11, 9, 15], [15, 5, 18], [8, 0, 15]], ![[0, 1], [10, 14, 11], [4, 18, 6], [2, 14], [5, 18, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 15], []]
 b := ![[], [1, 16, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [8, 0, 6, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-153107, 182866, -89239, -252323, 193393]
  a := ![-1, -2, -1, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![55721, 143780, -110458, -252323, 193393]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-94972181, 46820351, 4049150, 484149, -6784797]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-94972181, 46820351, 4049150, 484149, -6784797]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![8, 16, 1, 0, 0], ![8, 1, 0, 1, 0], ![4, 7, 0, 0, 1]] where
  M :=![![![-94972181, 46820351, 4049150, 484149, -6784797], ![-67847970, 33454813, 2891773, 345205, -4848201], ![-48482010, 23922644, 2063974, 244935, -3467381], ![6904100, -3384675, -296979, -37119, 489870], ![-24405770, 12060449, 1036586, 121513, -1748612]]]
  hmulB := by decide  
  f := ![![![237441, -551877, 264210, -168919, 37605]], ![![376050, -308135, 144487, 903863, -638071]], ![![80822, 118440, -58344, 576507, -364785]], ![![1071202, -2153578, 1029220, -66188, -244783]], ![![17656, 293244, -142181, 679380, -409293]]]
  g := ![![![-5478915, 1528599, 4049150, 484149, -6784797], ![-3913210, 1093613, 2891773, 345205, -4848201], ![-2793882, 785568, 2063974, 244935, -3467381], ![400916, -106578, -296979, -37119, 489870], ![-1404006, 399676, 1036586, 121513, -1748612]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [3, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 18], [0, 1]]
 g := ![![[3, 7], [18, 5], [5], [1]], ![[16, 12], [11, 14], [5], [1]]]
 h' := ![![[10, 18], [3, 11], [13, 9], [16, 10], [0, 1]], ![[0, 1], [18, 8], [8, 10], [2, 9], [10, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [4, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [3, 9, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5519, -7267, 2289, 6308, -3792]
  a := ![3, -3, 0, -7, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2531, -1245, 2289, 6308, -3792]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![237441, -551877, 264210, -168919, 37605]] ![![-94972181, 46820351, 4049150, 484149, -6784797]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -18, 1, 1, 3]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![11, -18, 1, 1, 3]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![10, 2, 1, 0, 0], ![8, 2, 0, 1, 0], ![13, 8, 0, 0, 1]] where
  M :=![![![11, -18, 1, 1, 3], ![30, -47, 3, 3, 7], ![70, -106, 2, 7, 19], ![60, -96, 10, 1, 14], ![90, -138, 9, 11, 18]]]
  hmulB := by decide  
  f := ![![![-67, 46, 1, -1, -7]], ![![-70, 67, -1, -3, -11]], ![![-40, 32, 0, -1, -5]], ![![-32, 26, 0, -1, -4]], ![![-67, 56, 0, -2, -9]]]
  g := ![![![-2, -2, 1, 1, 3], ![-5, -5, 3, 3, 7], ![-11, -12, 2, 7, 19], ![-10, -10, 10, 1, 14], ![-14, -14, 9, 11, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [2, 6, 1] where
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
 g := ![![[3, 12], [19, 9], [15, 13], [1]], ![[0, 11], [11, 14], [6, 10], [1]]]
 h' := ![![[17, 22], [8, 9], [16, 3], [21, 17], [0, 1]], ![[0, 1], [0, 14], [21, 20], [11, 6], [17, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [8, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [2, 6, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17549, -29964, 11102, 6720, -5096]
  a := ![1, -4, -3, -5, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3521, -1080, 11102, 6720, -5096]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26003, 40900, -3202, -2892, -6974]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-26003, 40900, -3202, -2892, -6974]] 
 ![![23, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-26003, 40900, -3202, -2892, -6974], ![-69740, 109395, -8228, -7594, -18542], ![-185420, 290152, -21033, -19810, -48918], ![-151880, 236840, -16232, -15777, -39620], ![-238780, 372476, -25670, -24872, -62357]]]
  hmulB := by decide  
  f := ![![![-31581, 15556, 1358, 200, -2286]], ![![-2367, 1183, 90, 10, -164]], ![![-30854, 15112, 1383, 186, -2246]], ![![-1347, 804, -30, 71, -110]], ![![-8662, 4348, 314, 4, -573]]]
  g := ![![![2099, 40900, -3202, -2892, -6974], ![5249, 109395, -8228, -7594, -18542], ![13064, 290152, -21033, -19810, -48918], ![9647, 236840, -16232, -15777, -39620], ![15326, 372476, -25670, -24872, -62357]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, 84, -39, -1, 11]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-43, 84, -39, -1, 11]] 
 ![![23, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-43, 84, -39, -1, 11], ![110, -251, 123, -65, 7], ![70, 42, -14, 383, -253], ![-1300, 2226, -1056, -715, 766], ![1310, -2724, 1311, -257, -202]]]
  hmulB := by decide  
  f := ![![![-1008261, 496932, 43005, 5153, -72007]], ![![-294332, 145057, 12555, 1505, -21019]], ![![-460720, 227046, 19654, 2357, -32899]], ![![-478997, 236058, 20433, 2450, -34205]], ![![-712622, 351192, 30399, 3645, -50888]]]
  g := ![![![-14, 84, -39, -1, 11], ![43, -251, 123, -65, 7], ![-9, 42, -14, 383, -253], ![-369, 2226, -1056, -715, 766], ![461, -2724, 1311, -257, -202]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2

def I23N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1373230763, -676941330, -58555058, -7005552, 98094700]] i)))

def SI23N3: IdealEqSpanCertificate' Table ![![1373230763, -676941330, -58555058, -7005552, 98094700]] 
 ![![23, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![1373230763, -676941330, -58555058, -7005552, 98094700], ![980947000, -483562985, -41827936, -5004312, 70072492], ![700724920, -345426036, -29879165, -3574756, 50055244], ![-100086240, 49338038, 4267714, 510591, -7149512], ![352501080, -173767262, -15030774, -1798288, 25180391]]]
  hmulB := by decide  
  f := ![![![100101, -155642, 10150, 10152, 25868]], ![![72178, -112197, 7284, 7304, 18636]], ![![76777, -119230, 7609, 7708, 19760]], ![![113887, -176876, 11304, 11439, 29324]], ![![113886, -176774, 11186, 11384, 29263]]]
  g := ![![![429388131, -676941330, -58555058, -7005552, 98094700], ![306727034, -483562985, -41827936, -5004312, 70072492], ![219105901, -345426036, -29879165, -3574756, 50055244], ![-31295427, 49338038, 4267714, 510591, -7149512], ![110221664, -173767262, -15030774, -1798288, 25180391]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N3 : Nat.card (O ⧸ I23N3) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N3)

lemma isPrimeI23N3 : Ideal.IsPrime I23N3 := prime_ideal_of_norm_prime hp23.out _ NI23N3
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![11, -18, 1, 1, 3]] ![![-26003, 40900, -3202, -2892, -6974]]
  ![![-84353, 125210, -1393, -5323, -18567]] where
 M := ![![![-84353, 125210, -1393, -5323, -18567]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-84353, 125210, -1393, -5323, -18567]] ![![-43, 84, -39, -1, 11]]
  ![![-100101, 155642, -10150, -10152, -25868]] where
 M := ![![![-100101, 155642, -10150, -10152, -25868]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N2 : IdealMulLeCertificate' Table 
  ![![-100101, 155642, -10150, -10152, -25868]] ![![1373230763, -676941330, -58555058, -7005552, 98094700]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2, I23N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
    exact isPrimeI23N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1 ⊙ MulI23N2)


lemma PB886I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB886I0 : PrimesBelowBoundCertificateInterval O 1 23 886 where
  m := 9
  g := ![5, 4, 5, 2, 2, 3, 2, 2, 4]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB886I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1, I23N2, I23N3]
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
    · exact ![9, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![2401, 7]
    · exact ![14641, 11]
    · exact ![2197, 13, 13]
    · exact ![83521, 17]
    · exact ![6859, 361]
    · exact ![529, 23, 23, 23]
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
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
      exact NI23N3
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I11N1, I13N1, I13N2, I17N1, I19N1, I23N0, I23N1, I23N2, I23N3]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N1], [I13N1, I13N2], [I17N1], [I19N1], [I23N0, I23N1, I23N2, I23N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
