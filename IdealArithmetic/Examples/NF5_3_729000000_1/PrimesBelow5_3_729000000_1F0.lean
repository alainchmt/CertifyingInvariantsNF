
import IdealArithmetic.Examples.NF5_3_729000000_1.RI5_3_729000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![592, 818, 57, 275, 323]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![592, 818, 57, 275, 323]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![592, 818, 57, 275, 323], ![3230, 4705, 316, 1587, 1973], ![19730, 28100, 1917, 9465, 11495], ![9880, 14170, 962, 4775, 5842], ![20710, 29582, 2014, 9966, 12141]]]
  hmulB := by decide  
  f := ![![![-69, -38, -19, 0, 26]], ![![130, 61, -6, -43, 13]], ![![130, 200, 203, 35, -245]], ![![-310, -182, -12, 123, -10]], ![![-25, 0, 7, -2, -5]]]
  g := ![![![296, 818, 57, 275, 323], ![1615, 4705, 316, 1587, 1973], ![9865, 28100, 1917, 9465, 11495], ![4940, 14170, 962, 4775, 5842], ![10355, 29582, 2014, 9966, 12141]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65067, 30771, 5035, 9063, -15838]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![65067, 30771, 5035, 9063, -15838]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![65067, 30771, 5035, 9063, -15838], ![-158380, -74913, -12256, -22065, 38540], ![385400, 182215, 29822, 53665, -93850], ![-14660, -6961, -1135, -2052, 3544], ![222560, 105199, 17221, 30981, -54219]]]
  hmulB := by decide  
  f := ![![![346, 97, 9, 26, -46]], ![![-57, 4, -9, -47, 32]], ![![723, 296, 195, 158, -328]], ![![-17, -100, -38, 97, 6]], ![![503, 155, 33, 44, -91]]]
  g := ![![![18018, 30771, 5035, 9063, -15838], ![-43843, -74913, -12256, -22065, 38540], ![106774, 182215, 29822, 53665, -93850], ![-4028, -6961, -1135, -2052, 3544], ![61689, 105199, 17221, 30981, -54219]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4523, 2139, 350, 630, -1101]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![4523, 2139, 350, 630, -1101]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![4523, 2139, 350, 630, -1101], ![-11010, -5208, -852, -1534, 2679], ![26790, 12665, 2073, 3730, -6525], ![-1020, -485, -79, -143, 246], ![15470, 7311, 1197, 2153, -3770]]]
  hmulB := by decide  
  f := ![![![-56, -20, -4, -1, 9]], ![![17, 1, -6, -2, 6]], ![![-13, 30, 15, -33, -3]], ![![-30, -7, 15, 18, -21]], ![![-40, -11, -2, -5, 7]]]
  g := ![![![1017, 2139, 350, 630, -1101], ![-2475, -5208, -852, -1534, 2679], ![6026, 12665, 2073, 3730, -6525], ![-228, -485, -79, -143, 246], ![3481, 7311, 1197, 2153, -3770]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![592, 818, 57, 275, 323]] ![![65067, 30771, 5035, 9063, -15838]]
  ![![-1211996, -611145, -94576, -182406, 262037]] where
 M := ![![![-1211996, -611145, -94576, -182406, 262037]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-1211996, -611145, -94576, -182406, 262037]] ![![65067, 30771, 5035, 9063, -15838]]
  ![![42475637648, 20090969158, 3286917775, 5917639046, -10335809019]] where
 M := ![![![42475637648, 20090969158, 3286917775, 5917639046, -10335809019]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![42475637648, 20090969158, 3286917775, 5917639046, -10335809019]] ![![4523, 2139, 350, 630, -1101]]
  ![![-106958691506276, -50584719500636, -8276708878618, -14898910870867, 26032630048905]] where
 M := ![![![-106958691506276, -50584719500636, -8276708878618, -14898910870867, 26032630048905]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-106958691506276, -50584719500636, -8276708878618, -14898910870867, 26032630048905]] ![![4523, 2139, 350, 630, -1101]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![269352245105784482, 127386590139605904, 20843093609307936, 37519656697603050, -65557566119416650]]]
 hmul := by decide  
 g := ![![![![134676122552892241, 63693295069802952, 10421546804653968, 18759828348801525, -32778783059708325]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14587, -7005, -1137, -2069, 3593]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-14587, -7005, -1137, -2069, 3593]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-14587, -7005, -1137, -2069, 3593], ![35930, 17182, 2795, 5071, -8821], ![-88210, -42055, -6852, -12405, 21605], ![3640, 1687, 279, 495, -872], ![-50940, -24287, -3957, -7164, 12477]]]
  hmulB := by decide  
  f := ![![![111, 57, -13, -55, 27]], ![![90, 96, 83, 11, -101]], ![![-1010, -595, -38, 415, -35]], ![![-80, -165, -229, -99, 296]], ![![-3, 0, -4, 3, 8]]]
  g := ![![![-6060, -7005, -1137, -2069, 3593], ![14917, 17182, 2795, 5071, -8821], ![-36605, -42055, -6852, -12405, 21605], ![1504, 1687, 279, 495, -872], ![-21139, -24287, -3957, -7164, 12477]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, -15, -3, -4, 8]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-47, -15, -3, -4, 8]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-47, -15, -3, -4, 8], ![80, 22, 5, 6, -16], ![-160, -65, -12, -20, 20], ![-20, -13, -1, -5, -2], ![-100, -47, -7, -14, 7]]]
  hmulB := by decide  
  f := ![![![-789, -373, -61, -110, 192]], ![![114, 54, 9, 16, -28]], ![![-2086, -987, -162, -290, 508]], ![![-203, -96, -16, -29, 50]], ![![-1163, -550, -90, -162, 283]]]
  g := ![![![-5, -15, -3, -4, 8], ![12, 22, 5, 6, -16], ![-2, -65, -12, -20, 20], ![5, -13, -1, -5, -2], ![5, -47, -7, -14, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-14587, -7005, -1137, -2069, 3593]] ![![-14587, -7005, -1137, -2069, 3593]]
  ![![-129172891, -61115034, -9997584, -18001774, 31449158]] where
 M := ![![![-129172891, -61115034, -9997584, -18001774, 31449158]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-129172891, -61115034, -9997584, -18001774, 31449158]] ![![-47, -15, -3, -4, 8]]
  ![![-3343723, -1181787, -227821, -326302, 653390]] where
 M := ![![![-3343723, -1181787, -227821, -326302, 653390]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-3343723, -1181787, -227821, -326302, 653390]] ![![-47, -15, -3, -4, 8]]
  ![![40250421, 12497492, 2608658, 3324640, -7171278]] where
 M := ![![![40250421, 12497492, 2608658, 3324640, -7171278]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![40250421, 12497492, 2608658, 3324640, -7171278]] ![![-47, -15, -3, -4, 8]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-658720707, -204544515, -42693393, -54415200, 117368430]]]
 hmul := by decide  
 g := ![![![![-219573569, -68181505, -14231131, -18138400, 39122810]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13005, 6206, 1010, 1831, -3173]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![13005, 6206, 1010, 1831, -3173]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![13005, 6206, 1010, 1831, -3173], ![-31730, -15017, -2460, -4423, 7813], ![78130, 37490, 6065, 11075, -18725], ![-2860, -1136, -216, -321, 866], ![45320, 21936, 3522, 6492, -10697]]]
  hmulB := by decide  
  f := ![![![4025, 1870, -824, -2215, 1435]], ![![2870, 2695, 1990, -57, -2371]], ![![-23710, -13318, 495, 10473, -2713]], ![![-4148, -5408, -5740, -1609, 7198]], ![![-1028, -556, 62, 478, -171]]]
  g := ![![![2601, 6206, 1010, 1831, -3173], ![-6346, -15017, -2460, -4423, 7813], ![15626, 37490, 6065, 11075, -18725], ![-572, -1136, -216, -321, 866], ![9064, 21936, 3522, 6492, -10697]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![13005, 6206, 1010, 1831, -3173]] ![![13005, 6206, 1010, 1831, -3173]]
  ![![-97912075, -46304516, -7576862, -13638100, 23837590]] where
 M := ![![![-97912075, -46304516, -7576862, -13638100, 23837590]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-97912075, -46304516, -7576862, -13638100, 23837590]] ![![13005, 6206, 1010, 1831, -3173]]
  ![![723240074045, 342050278782, 55966067160, 100745582673, -176026723413]] where
 M := ![![![723240074045, 342050278782, 55966067160, 100745582673, -176026723413]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![723240074045, 342050278782, 55966067160, 100745582673, -176026723413]] ![![13005, 6206, 1010, 1831, -3173]]
  ![![-5340552827108775, -2525742465821720, -413264179410824, -743916434114620, 1299837000551660]] where
 M := ![![![-5340552827108775, -2525742465821720, -413264179410824, -743916434114620, 1299837000551660]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-5340552827108775, -2525742465821720, -413264179410824, -743916434114620, 1299837000551660]] ![![13005, 6206, 1010, 1831, -3173]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![39435802453174922005, 18650643191351341910, 3051632728126625330, 5493244895850594475, -9598268032425643825]]]
 hmul := by decide  
 g := ![![![![7887160490634984401, 3730128638270268382, 610326545625325066, 1098648979170118895, -1919653606485128765]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2516441, -1190118, -194728, -350530, 612476]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-2516441, -1190118, -194728, -350530, 612476]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![6, 2, 3, 4, 1]] where
  M :=![![![-2516441, -1190118, -194728, -350530, 612476], ![6124760, 2896625, 473948, 853154, -1490704], ![-14907040, -7050090, -1153541, -2076490, 3628220], ![565840, 267606, 43786, 78819, -137720], ![-8609540, -4071770, -666226, -1199274, 2095473]]]
  hmulB := by decide  
  f := ![![![33, 10, -4, -6, 4]], ![![40, 51, 32, -18, -32]], ![![-320, -170, 73, 210, -140]], ![![-160, -154, -110, 5, 128]], ![![-186, -138, -25, 84, 5]]]
  g := ![![![-884471, -345010, -290308, -400062, 612476], ![2152712, 839719, 706580, 973710, -1490704], ![-5239480, -2043790, -1719743, -2369910, 3628220], ![198880, 77578, 65278, 89957, -137720], ![-3026054, -1180388, -993235, -1368738, 2095473]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [4, 0, 3, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 3, 3, 6], [3, 5, 5, 2], [4, 5, 6, 6], [0, 1]]
 g := ![![[4, 1, 5, 1], []], ![[6, 2, 6, 1, 6, 3], [2, 0, 1, 5, 4, 6]], ![[5, 3, 3, 6, 3, 4], [0, 1, 0, 0, 2, 1]], ![[1, 6, 0, 3, 0, 6], [4, 2, 3, 3, 6, 6]]]
 h' := ![![[5, 3, 3, 6], [0, 0, 0, 1], [0, 1]], ![[3, 5, 5, 2], [5, 1, 0, 2], [5, 3, 3, 6]], ![[4, 5, 6, 6], [6, 5, 3, 3], [3, 5, 5, 2]], ![[0, 1], [6, 1, 4, 1], [4, 5, 6, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6, 4, 2], []]
 b := ![[], [], [4, 1, 2, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [4, 0, 3, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16627082104, 22408615244, 1731601324, 6528685858, 8512379712]
  a := ![0, -9, 16, 2, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4921028024, 769122260, -3400791116, -3931547570, 8512379712]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, -10, 4, 6, -4]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-33, -10, 4, 6, -4]] 
 ![![7, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-33, -10, 4, 6, -4], ![-40, -51, -32, 18, 32], ![320, 170, -73, -210, 140], ![160, 154, 110, -5, -128], ![-20, 2, -6, -10, 17]]]
  hmulB := by decide  
  f := ![![![2516441, 1190118, 194728, 350530, -612476]], ![![203509, 96247, 15748, 28348, -49532]], ![![3927035, 1857240, 303883, 547020, -955800]], ![![1357132, 641838, 105018, 189043, -330312]], ![![2308409, 1091732, 178630, 321552, -561843]]]
  g := ![![![-5, -10, 4, 6, -4], ![15, -51, -32, 18, 32], ![85, 170, -73, -210, 140], ![-64, 154, 110, -5, -128], ![-1, 2, -6, -10, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-2516441, -1190118, -194728, -350530, 612476]] ![![-33, -10, 4, 6, -4]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4491, -1577, -419, -263, 899]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-4491, -1577, -419, -263, 899]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![1, 5, 4, 7, 1]] where
  M :=![![![-4491, -1577, -419, -263, 899], ![8990, 3040, 111, -331, -679], ![-6790, 1745, 3354, -1275, -2665], ![-7160, -3581, 235, 2581, -692], ![-7240, -2067, -305, -652, 1131]]]
  hmulB := by decide  
  f := ![![![20239, 29333, 1977, 9891, 12233]], ![![122330, 174578, 11893, 58811, 71579]], ![![715790, 1027975, 69724, 346435, 424445]], ![![363280, 520685, 35365, 175453, 214516]], ![![617599, 885739, 60134, 298475, 365161]]]
  g := ![![![-490, -552, -365, -596, 899], ![879, 585, 257, 402, -679], ![-375, 1370, 1274, 1580, -2665], ![-588, -11, 273, 675, -692], ![-761, -702, -439, -779, 1131]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [4, 4, 4, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 7, 2, 7], [4, 10], [3, 4, 9, 4], [0, 1]]
 g := ![![[8, 7, 5, 3], [8, 1], []], ![[8, 8, 7, 9, 7, 2], [2, 4, 2, 3, 3, 10], [10, 2, 5]], ![[0, 7, 8, 8], [1, 10], []], ![[3, 3, 10, 10, 3, 9], [8, 7, 5, 10, 5, 1], [10, 2, 5]]]
 h' := ![![[1, 7, 2, 7], [1, 8, 8, 5], [0, 0, 1], [0, 1]], ![[4, 10], [6, 9, 8, 7], [5, 10, 7, 6], [1, 7, 2, 7]], ![[3, 4, 9, 4], [8, 7, 2, 6], [5, 3, 1], [4, 10]], ![[0, 1], [2, 9, 4, 4], [2, 9, 2, 5], [3, 4, 9, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6], []]
 b := ![[], [], [8, 9, 4, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [4, 4, 4, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![138924674320434, 196148017899690, 11247546055204, 63864394780222, 83655265017194]
  a := ![3, -125, 119, -69, -298]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5024491754840, -20193482471480, -29397592183052, -47429314576376, 83655265017194]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20239, 29333, 1977, 9891, 12233]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![20239, 29333, 1977, 9891, 12233]] 
 ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![20239, 29333, 1977, 9891, 12233], ![122330, 174578, 11893, 58811, 71579], ![715790, 1027975, 69724, 346435, 424445], ![363280, 520685, 35365, 175453, 214516], ![755580, 1084211, 73581, 365368, 447251]]]
  hmulB := by decide  
  f := ![![![-4491, -1577, -419, -263, 899]], ![![409, 133, -28, -54, 20]], ![![-4700, -1275, -76, -355, 575]], ![![-2284, -899, -131, 139, 264]], ![![-1883, -618, -142, -131, 348]]]
  g := ![![![-9557, 29333, 1977, 9891, 12233], ![-56469, 174578, 11893, 58811, 71579], ![-333500, 1027975, 69724, 346435, 424445], ![-168765, 520685, 35365, 175453, 214516], ![-351606, 1084211, 73581, 365368, 447251]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-4491, -1577, -419, -263, 899]] ![![20239, 29333, 1977, 9891, 12233]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10337, -3210, -670, -854, 1842]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-10337, -3210, -670, -854, 1842]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![10, 4, 10, 1, 0], ![4, 7, 2, 0, 1]] where
  M :=![![![-10337, -3210, -670, -854, 1842], ![18420, 5721, 1194, 1522, -3282], ![-32820, -10190, -2127, -2710, 5850], ![-3360, -1042, -218, -277, 600], ![-19040, -5910, -1234, -1572, 3395]]]
  hmulB := by decide  
  f := ![![![-29, -14, -2, -2, 6]], ![![60, 25, -2, 6, -6]], ![![-60, -10, 1, -50, 30]], ![![-50, -10, 0, -37, 24]], ![![8, 5, -2, -6, 5]]]
  g := ![![![-705, -976, 322, -854, 1842], ![1256, 1739, -574, 1522, -3282], ![-2240, -3100, 1021, -2710, 5850], ![-230, -318, 104, -277, 600], ![-1300, -1799, 592, -1572, 3395]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [3, 5, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 12, 9], [11, 0, 4], [0, 1]]
 g := ![![[10, 2, 4], [0, 10], [1]], ![[2, 12], [2, 10], [0, 11, 11, 1]], ![[7, 3, 3, 3], [4, 1], [7, 3, 6, 12]]]
 h' := ![![[9, 12, 9], [9, 0, 11], [10, 8, 7], [0, 1]], ![[11, 0, 4], [8, 6], [1, 10, 7], [9, 12, 9]], ![[0, 1], [10, 7, 2], [10, 8, 12], [11, 0, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 12], []]
 b := ![[], [6, 11, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [3, 5, 6, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9245865, -12281510, -374264, -3421870, -5611410]
  a := ![1, -9, 11, -3, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3647575, 3129680, 3466712, -3421870, -5611410]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![187, 54, 12, 14, -36]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![187, 54, 12, 14, -36]] 
 ![![13, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![187, 54, 12, 14, -36], ![-360, -135, -24, -38, 48], ![480, 10, 27, -10, -180], ![0, -70, -2, -25, -48], ![220, -78, 10, -34, -139]]]
  hmulB := by decide  
  f := ![![![-41, -14, 0, -18, 12]], ![![-16, -3, 4, -6, 0]], ![![-77, -48, -17, 4, 24]], ![![9, 4, -6, -15, 12]], ![![-20, -10, -2, -2, 5]]]
  g := ![![![-23, 54, 12, 14, -36], ![66, -135, -24, -38, 48], ![31, 10, 27, -10, -180], ![49, -70, -2, -25, -48], ![72, -78, 10, -34, -139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![503, 721, 49, 243, 297]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![503, 721, 49, 243, 297]] 
 ![![13, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![503, 721, 49, 243, 297], ![2970, 4258, 289, 1435, 1755], ![17550, 25155, 1708, 8475, 10365], ![8880, 12729, 865, 4289, 5244], ![18500, 26519, 1801, 8936, 10927]]]
  hmulB := by decide  
  f := ![![![-3589, -1067, -229, -281, 621]], ![![-2007, -599, -128, -158, 348]], ![![-3580, -1055, -228, -275, 615]], ![![-1758, -525, -113, -139, 306]], ![![-1026, -299, -65, -78, 175]]]
  g := ![![![-656, 721, 49, 243, 297], ![-3874, 4258, 289, 1435, 1755], ![-22885, 25155, 1708, 8475, 10365], ![-11581, 12729, 865, 4289, 5244], ![-24127, 26519, 1801, 8936, 10927]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-10337, -3210, -670, -854, 1842]] ![![187, 54, 12, 14, -36]]
  ![![-693779, -215444, -44966, -57316, 123606]] where
 M := ![![![-693779, -215444, -44966, -57316, 123606]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-693779, -215444, -44966, -57316, 123606]] ![![503, 721, 49, 243, 297]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-247897, -362791, -24349, -122395, -151515]]]
 hmul := by decide  
 g := ![![![![-19069, -27907, -1873, -9415, -11655]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28457, -8783, -1841, -2332, 5066]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-28457, -8783, -1841, -2332, 5066]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![11, 15, 13, 1, 0], ![10, 2, 3, 0, 1]] where
  M :=![![![-28457, -8783, -1841, -2332, 5066], ![50660, 15732, 3279, 4186, -8926], ![-89260, -26945, -5752, -7100, 16190], ![-9140, -2569, -585, -659, 1822], ![-51560, -15303, -3315, -4008, 9531]]]
  hmulB := by decide  
  f := ![![![-561, -231, 171, 342, -274]], ![![-2740, -2378, -1531, 272, 1778]], ![![17780, 9435, -1416, -8470, 3410]], ![![11097, 5271, -2053, -5977, 3668]], ![![2530, 1272, -335, -1284, 661]]]
  g := ![![![-3145, 945, 781, -2332, 5066], ![5522, -1718, -1433, 4186, -8926], ![-10180, 2775, 2234, -7100, 16190], ![-1183, 216, 148, -659, 1822], ![-6046, 1515, 1188, -4008, 9531]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [12, 14, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 2, 2], [12, 14, 15], [0, 1]]
 g := ![![[6, 4, 15], [1, 1], [8, 1], []], ![[11, 15, 9, 4], [7, 15], [8, 9], [6, 4]], ![[15, 13, 6, 15], [16, 13], [12, 4], [10, 4]]]
 h' := ![![[13, 2, 2], [7, 16, 7], [6, 12, 16], [0, 0, 1], [0, 1]], ![[12, 14, 15], [10, 16, 11], [14, 2, 10], [12, 5, 14], [13, 2, 2]], ![[0, 1], [10, 2, 16], [7, 3, 8], [7, 12, 2], [12, 14, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 10], []]
 b := ![[], [5, 14, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [12, 14, 9, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1274879196, 1668741022, 57385602, 445856335, 744458025]
  a := ![1, 45, -57, 10, 141]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-651418867, -382824709, -468948284, 445856335, 744458025]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-137, -42, -6, -8, 20]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-137, -42, -6, -8, 20]] 
 ![![17, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-137, -42, -6, -8, 20], ![200, 45, 2, 28, -28], ![-280, -70, -67, -120, 140], ![40, 58, 42, -13, -44], ![-240, -74, -18, -24, 47]]]
  hmulB := by decide  
  f := ![![![-201, -598, -26, -208, -388]], ![![-311, -529, -32, -180, -256]], ![![-986, -1558, -99, -528, -708]], ![![-631, -1028, -64, -349, -480]], ![![-1151, -1840, -116, -624, -845]]]
  g := ![![![5, -42, -6, -8, 20], ![-7, 45, 2, 28, -28], ![12, -70, -67, -120, 140], ![-3, 58, 42, -13, -44], ![9, -74, -18, -24, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7857, -2392, -508, -632, 1436]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![-7857, -2392, -508, -632, 1436]] 
 ![![17, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-7857, -2392, -508, -632, 1436], ![14360, 4767, 940, 1296, -2356], ![-23560, -5560, -1477, -1320, 5420], ![-1760, 352, -88, 175, 928], ![-12920, -2152, -784, -404, 3587]]]
  hmulB := by decide  
  f := ![![![-1121, 24, 1260, 1224, -1756]], ![![-2088, -737, 868, 1408, -1324]], ![![2232, 1272, -13, -968, 212]], ![![1458, 1968, 2144, 639, -2696]], ![![-530, 56, 680, 628, -941]]]
  g := ![![![1943, -2392, -508, -632, 1436], ![-4208, 4767, 940, 1296, -2356], ![3136, -5560, -1477, -1320, 5420], ![-1042, 352, -88, 175, 928], ![226, -2152, -784, -404, 3587]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-28457, -8783, -1841, -2332, 5066]] ![![-137, -42, -6, -8, 20]]
  ![![1348369, 418689, 87391, 111384, -240246]] where
 M := ![![![1348369, 418689, 87391, 111384, -240246]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![1348369, 418689, 87391, 111384, -240246]] ![![-7857, -2392, -508, -632, 1436]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-3732750673, -1159085585, -241929227, -308352800, 665087770]]]
 hmul := by decide  
 g := ![![![![-219573569, -68181505, -14231131, -18138400, 39122810]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![301, 140, 16, 42, -66]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![301, 140, 16, 42, -66]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![13, 14, 13, 8, 1]] where
  M :=![![![301, 140, 16, 42, -66], ![-660, -303, -52, -146, 186], ![1860, 980, 321, 370, -690], ![-360, -224, -56, 81, 60], ![1080, 520, 92, 156, -275]]]
  hmulB := by decide  
  f := ![![![79, 124, 8, 42, 54]], ![![540, 755, 52, 254, 306]], ![![3060, 4420, 299, 1490, 1830]], ![![1560, 2240, 152, 755, 924]], ![![3373, 4854, 329, 1636, 2005]]]
  g := ![![![61, 56, 46, 30, -66], ![-162, -153, -130, -86, 186], ![570, 560, 489, 310, -690], ![-60, -56, -44, -21, 60], ![245, 230, 193, 124, -275]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [15, 14, 1, 13, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 11, 18, 14], [5, 12, 7, 14], [12, 14, 13, 10], [0, 1]]
 g := ![![[2, 7, 11, 11], [3, 14, 14, 17], [1], []], ![[17, 5, 9, 6, 9, 10], [13, 5, 3, 1, 17, 8], [16, 11, 11], [9, 8, 6]], ![[3, 14, 17, 18], [0, 6, 6, 4, 11, 13], [12, 12, 9], [4, 4, 6]], ![[5, 5, 8, 17, 5, 10], [3, 13, 18, 14, 14, 13], [2, 14, 5], [18, 5, 5]]]
 h' := ![![[8, 11, 18, 14], [12, 11, 11, 7], [4, 5, 18, 6], [0, 0, 1], [0, 1]], ![[5, 12, 7, 14], [17, 12, 14, 13], [13, 13, 9, 14], [5, 6, 8, 12], [8, 11, 18, 14]], ![[12, 14, 13, 10], [0, 5, 2], [0, 18, 9, 10], [3, 4, 7, 16], [5, 12, 7, 14]], ![[0, 1], [12, 10, 11, 18], [0, 2, 2, 8], [7, 9, 3, 10], [12, 14, 13, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [16, 16, 11], []]
 b := ![[], [], [13, 4, 6, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [15, 14, 1, 13, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18984675790, 25847649638, 3967243541, 7794425673, 6482354258]
  a := ![-1, -6, 21, 13, -50]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3436101556, -3416068946, -4226492727, -2319179389, 6482354258]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 124, 8, 42, 54]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![79, 124, 8, 42, 54]] 
 ![![19, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![79, 124, 8, 42, 54], ![540, 755, 52, 254, 306], ![3060, 4420, 299, 1490, 1830], ![1560, 2240, 152, 755, 924], ![3240, 4664, 316, 1572, 1927]]]
  hmulB := by decide  
  f := ![![![301, 140, 16, 42, -66]], ![![92, 43, 4, 10, -18]], ![![288, 140, 27, 46, -78]], ![![187, 84, 8, 33, -42]], ![![342, 160, 20, 48, -77]]]
  g := ![![![-133, 124, 8, 42, 54], ![-786, 755, 52, 254, 306], ![-4642, 4420, 299, 1490, 1830], ![-2349, 2240, 152, 755, 924], ![-4894, 4664, 316, 1572, 1927]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![301, 140, 16, 42, -66]] ![![79, 124, 8, 42, 54]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3667, 1742, 284, 514, -886]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![3667, 1742, 284, 514, -886]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![1, 0, 14, 1, 0], ![19, 12, 1, 0, 1]] where
  M :=![![![3667, 1742, 284, 514, -886], ![-8860, -4145, -686, -1218, 2198], ![21980, 10670, 1707, 3150, -5110], ![-680, -182, -46, -43, 280], ![12820, 6350, 998, 1888, -2871]]]
  hmulB := by decide  
  f := ![![![-135651, -42122, -8792, -11206, 24170]], ![![241700, 75053, 15666, 19966, -43066]], ![![-430660, -133730, -27911, -35570, 76730]], ![![-269957, -83828, -17496, -22297, 48098]], ![![-15543, -4826, -1007, -1284, 2769]]]
  g := ![![![869, 538, -262, 514, -886], ![-2148, -1327, 616, -1218, 2198], ![5040, 3130, -1621, 3150, -5110], ![-259, -154, 12, -43, 280], ![2847, 1774, -981, 1888, -2871]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [5, 19, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 5, 8], [1, 17, 15], [0, 1]]
 g := ![![[22, 12, 16], [0, 5, 13], [17, 6, 1], []], ![[13, 15, 18, 1], [4, 12, 11, 6], [21, 18, 3, 12], [4, 18]], ![[17, 2, 14, 21], [21, 16, 11, 14], [0, 15, 19, 7], [20, 18]]]
 h' := ![![[5, 5, 8], [0, 1, 4], [7, 15, 6], [0, 0, 1], [0, 1]], ![[1, 17, 15], [2, 1, 7], [20, 0, 15], [5, 22, 17], [5, 5, 8]], ![[0, 1], [19, 21, 12], [3, 8, 2], [16, 1, 5], [1, 17, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 10], []]
 b := ![[], [10, 22, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [5, 19, 17, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7577605, 10216242, 5894458, 2916574, -4898612]
  a := ![0, -2, -18, -26, 44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4249333, 2999982, -1306042, 2916574, -4898612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-135651, -42122, -8792, -11206, 24170]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-135651, -42122, -8792, -11206, 24170]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![9, 21, 1, 0, 0], ![11, 1, 0, 1, 0], ![1, 13, 0, 0, 1]] where
  M :=![![![-135651, -42122, -8792, -11206, 24170], ![241700, 75053, 15666, 19966, -43066], ![-430660, -133730, -27911, -35570, 76730], ![-44120, -13702, -2862, -3645, 7864], ![-249860, -77586, -16194, -20640, 44519]]]
  hmulB := by decide  
  f := ![![![3667, 1742, 284, 514, -886]], ![![-8860, -4145, -686, -1218, 2198]], ![![-5699, -2639, -441, -774, 1438]], ![![1339, 645, 104, 191, -316]], ![![-4291, -1991, -332, -584, 1079]]]
  g := ![![![1851, -6978, -8792, -11206, 24170], ![-3298, 12433, 15666, 19966, -43066], ![5873, -22153, -27911, -35570, 76730], ![603, -2269, -2862, -3645, 7864], ![3409, -12853, -16194, -20640, 44519]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [18, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 22], [0, 1]]
 g := ![![[21, 9], [17, 4], [4, 8], [1]], ![[0, 14], [0, 19], [16, 15], [1]]]
 h' := ![![[13, 22], [16, 20], [20, 2], [5, 13], [0, 1]], ![[0, 1], [0, 3], [0, 21], [13, 10], [13, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [21, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [18, 10, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![31357, 30588, -751, 53, 13912]
  a := ![13, -7, 18, 8, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1027, -5850, -751, 53, 13912]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![3667, 1742, 284, 514, -886]] ![![-135651, -42122, -8792, -11206, 24170]]
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


lemma PB1321I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1321I0 : PrimesBelowBoundCertificateInterval O 1 23 1321 where
  m := 9
  g := ![5, 5, 5, 2, 2, 3, 3, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1321I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1]
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
    · exact ![14641, 11]
    · exact ![2197, 13, 13]
    · exact ![4913, 17, 17]
    · exact ![130321, 19]
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
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I11N1, I13N1, I13N2, I17N1, I17N2, I19N1, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N1], [I13N1, I13N2], [I17N1, I17N2], [I19N1], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
