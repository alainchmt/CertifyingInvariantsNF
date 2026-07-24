
import IdealArithmetic.Examples.NF5_1_121500000_2.RI5_1_121500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![155396, -18444, 10227, 22977, 40036]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![155396, -18444, 10227, 22977, 40036]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![291, 49, 1, 0, 0], ![267, 219, 0, 1, 0], ![82, 212, 0, 0, 1]] where
  M :=![![![155396, -18444, 10227, 22977, 40036], ![68931, -8185, 4533, 10185, 17754], ![30555, -3624, 2000, 4491, 7848], ![-32220, 3834, -2122, -4771, -8310], ![-92043, 10926, -6053, -13599, -23705]]]
  hmulB := by decide  
  f := ![![![-110, 570, -175, 243, 98]], ![![729, -737, 813, -615, 1164]], ![![6, 401, -40, 129, 252]], ![![417, -9, 418, -217, 912]], ![![473, -368, 515, -363, 821]]]
  g := ![![![-39352, -45142, 10227, 22977, 40036], ![-17445, -20015, 4533, 10185, 17754], ![-7698, -8839, 2000, 4491, 7848], ![8169, 9371, -2122, -4771, -8310], ![23293, 26724, -6053, -13599, -23705]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 2 2 8 [154, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [251, 310], [0, 1]]
 g := ![![[271, 256], [251, 3], [126, 267], [273], [237, 249], [70, 292], [179], [1]], ![[150, 55], [71, 308], [278, 44], [273], [225, 62], [277, 19], [179], [1]]]
 h' := ![![[251, 310], [221, 295], [189, 25], [135, 122], [200, 133], [105, 210], [193, 276], [157, 251], [0, 1]], ![[0, 1], [248, 16], [244, 286], [279, 189], [306, 178], [256, 101], [116, 35], [25, 60], [251, 310]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [158]]
 b := ![[], [193, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 2
  hpos := by decide
  P := [154, 60, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1027, -5668, -648, -3110, -5340]
  a := ![-17, -13, -9, -20, -34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4681, 5914, -648, -3110, -5340]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 96721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8798, -11294, -11911, -24223, -18792]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![-8798, -11294, -11911, -24223, -18792]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![165, 301, 1, 0, 0], ![275, 115, 0, 1, 0], ![94, 182, 0, 0, 1]] where
  M :=![![![-8798, -11294, -11911, -24223, -18792], ![-72669, 19775, -35517, -87759, -88962], ![-263277, 179034, -67984, -209493, -259668], ![-68412, 102078, 12682, 983, -35178], ![107199, -51378, 39961, 106551, 118489]]]
  hmulB := by decide  
  f := ![![![-24869461618684, 2951270210996, -1636856591461, -3677383584785, -6407331476886]], ![![-11032150754355, 1309190298679, -726113373789, -1631295872463, -2842307078052]], ![![-23887564089264, 2834747988953, -1572230124358, -3532192912305, -6154356843024]], ![![-26053520996221, 3091783070605, -1714788933806, -3852467411895, -6712390791660]], ![![-13925559871787, 1652552461778, -916551585049, -2059136866999, -3587760743189]]]
  g := ![![![33390, 31446, -11911, -24223, -18792], ![123099, 118951, -35517, -87759, -88962], ![298950, 295799, -67984, -209493, -259668], ![2815, 8277, 12682, 983, -35178], ![-150887, -147582, 39961, 106551, 118489]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P1 : CertificateIrreducibleZModOfList' 311 2 2 8 [64, 242, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 310], [0, 1]]
 g := ![![[169, 277], [251, 13], [230, 35], [80], [22, 107], [154, 28], [96], [1]], ![[0, 34], [215, 298], [157, 276], [80], [252, 204], [220, 283], [96], [1]]]
 h' := ![![[69, 310], [108, 39], [208, 293], [6, 103], [147, 154], [96, 284], [129, 280], [247, 69], [0, 1]], ![[0, 1], [0, 272], [210, 18], [271, 208], [199, 157], [99, 27], [167, 31], [32, 242], [69, 310]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [192, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N1 : CertifiedPrimeIdeal' SI311N1 311 where
  n := 2
  hpos := by decide
  P := [64, 242, 1]
  hirr := P311P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24178, -206479, 8415, -120120, -67475]
  a := ![-101, -111, -50, -167, -205]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![122223, 75096, 8415, -120120, -67475]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N1 B_one_repr
lemma NI311N1 : Nat.card (O ⧸ I311N1) = 96721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N1

def I311N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-205960181, 24441388, -13555874, -30454804, -53063278]] i)))

def SI311N2: IdealEqSpanCertificate' Table ![![-205960181, 24441388, -13555874, -30454804, -53063278]] 
 ![![311, 0, 0, 0, 0], ![272, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![85, 0, 0, 1, 0], ![155, 0, 0, 0, 1]] where
  M :=![![![-205960181, 24441388, -13555874, -30454804, -53063278], ![-91364412, 10842257, -6013416, -13509822, -23538990], ![-40529466, 4809636, -2667565, -5992992, -10441962], ![42685710, -5065524, 2809482, 6311831, 10997484], ![122002866, -14478138, 8029980, 18040248, 31432643]]]
  hmulB := by decide  
  f := ![![![515789, -315208, 154334, 447004, 529558]], ![![455420, -279875, 135404, 393130, 466666]], ![![62932, -45608, 14859, 47408, 60434]], ![![138085, -86996, 39868, 117067, 140246]], ![![252599, -151762, 77030, 221512, 260865]]]
  g := ![![![14213339, 24441388, -13555874, -30454804, -53063278], ![6305068, 10842257, -6013416, -13509822, -23538990], ![2796962, 4809636, -2667565, -5992992, -10441962], ![-2945755, -5065524, 2809482, 6311831, 10997484], ![-8419433, -14478138, 8029980, 18040248, 31432643]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N2 : Nat.card (O ⧸ I311N2) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N2)

lemma isPrimeI311N2 : Ideal.IsPrime I311N2 := prime_ideal_of_norm_prime hp311.out _ NI311N2
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![155396, -18444, 10227, 22977, 40036]] ![![-8798, -11294, -11911, -24223, -18792]]
  ![![515789, -315208, 154334, 447004, 529558]] where
 M := ![![![515789, -315208, 154334, 447004, 529558]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI311N1 : IdealMulLeCertificate' Table 
  ![![515789, -315208, 154334, 447004, 529558]] ![![-205960181, 24441388, -13555874, -30454804, -53063278]]
  ![![311, 0, 0, 0, 0]] where
 M := ![![![311, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC311 : ContainsPrimesAboveP 311 ![I311N0, I311N1, I311N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI311N0
    exact isPrimeI311N1
    exact isPrimeI311N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 311 (by decide) (𝕀 ⊙ MulI311N0 ⊙ MulI311N1)
instance hp313 : Fact (Nat.Prime 313) := {out := by norm_num}

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, -1752, 236, -564, -966]] i)))

def SI313N0: IdealEqSpanCertificate' Table ![![41, -1752, 236, -564, -966]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![270, 30, 1, 0, 0], ![215, 52, 0, 1, 0], ![12, 6, 0, 0, 1]] where
  M :=![![![41, -1752, 236, -564, -966], ![-1692, 5417, -2316, 2622, -486], ![7866, -480, 8039, -4572, 17190], ![-1440, -16092, 316, -4153, -12924], ![-2124, 18654, -4218, 6948, 6551]]]
  hmulB := by decide  
  f := ![![![2633, -2580, 568, 2076, 2802]], ![![6228, -8323, -504, 1230, 4050]], ![![2880, -3078, 419, 1872, 2790]], ![![2815, -3148, 292, 1595, 2562]], ![![204, -228, 18, 108, 179]]]
  g := ![![![221, 84, 236, -564, -966], ![210, -187, -2316, 2622, -486], ![-4428, -342, 8039, -4572, 17190], ![3071, 856, 316, -4153, -12924], ![-1392, -816, -4218, 6948, 6551]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P0 : CertificateIrreducibleZModOfList' 313 2 2 8 [244, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [310, 312], [0, 1]]
 g := ![![[68, 261], [287], [286], [174, 33], [49, 291], [23, 108], [9], [1]], ![[224, 52], [287], [286], [75, 280], [115, 22], [12, 205], [9], [1]]]
 h' := ![![[310, 312], [40, 218], [39, 66], [112, 278], [251, 71], [22, 149], [61, 185], [69, 310], [0, 1]], ![[0, 1], [12, 95], [154, 247], [217, 35], [38, 242], [201, 164], [132, 128], [78, 3], [310, 312]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [179]]
 b := ![[], [56, 246]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N0 : CertifiedPrimeIdeal' SI313N0 313 where
  n := 2
  hpos := by decide
  P := [244, 3, 1]
  hirr := P313P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![415, -698, 75, -385, -76]
  a := ![-6, -7, -3, -11, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![204, 56, 75, -385, -76]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N0 : Ideal.IsPrime I313N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N0 B_one_repr
lemma NI313N0 : Nat.card (O ⧸ I313N0) = 97969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N0

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, -151, -13, -30, -156]] i)))

def SI313N1: IdealEqSpanCertificate' Table ![![-29, -151, -13, -30, -156]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![142, 11, 1, 0, 0], ![157, 4, 0, 1, 0], ![221, 224, 0, 0, 1]] where
  M :=![![![-29, -151, -13, -30, -156], ![-90, 808, -181, 300, 288], ![900, -1761, 1108, -1050, 936], ![-480, -986, -378, -35, -1662], ![117, 1974, -99, 543, 1453]]]
  hmulB := by decide  
  f := ![![![4933, -629, 365, 840, 1380]], ![![2520, -572, 211, 570, 900]], ![![2332, -309, 173, 402, 660]], ![![2503, -323, 185, 427, 702]], ![![5276, -851, 408, 999, 1615]]]
  g := ![![![131, 112, -13, -30, -156], ![-272, -201, -181, 300, 288], ![-634, -701, 1108, -1050, 936], ![1361, 1200, -378, -35, -1662], ![-1253, -1037, -99, 543, 1453]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P1 : CertificateIrreducibleZModOfList' 313 2 2 8 [211, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [285, 312], [0, 1]]
 g := ![![[12, 57], [6], [49], [85, 214], [75, 208], [312, 2], [158], [1]], ![[294, 256], [6], [49], [40, 99], [198, 105], [256, 311], [158], [1]]]
 h' := ![![[285, 312], [74, 87], [62, 257], [219, 306], [138, 98], [211, 258], [228, 193], [102, 285], [0, 1]], ![[0, 1], [142, 226], [65, 56], [102, 7], [211, 215], [186, 55], [145, 120], [260, 28], [285, 312]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [167]]
 b := ![[], [230, 240]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N1 : CertifiedPrimeIdeal' SI313N1 313 where
  n := 2
  hpos := by decide
  P := [211, 28, 1]
  hirr := P313P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4828, -71557, 2827, -27428, -35385]
  a := ![65, 55, 33, 82, 129]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![37475, 25346, 2827, -27428, -35385]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N1 : Ideal.IsPrime I313N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N1 B_one_repr
lemma NI313N1 : Nat.card (O ⧸ I313N1) = 97969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N1

def I313N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![74, -165, 94, -93, 66]] i)))

def SI313N2: IdealEqSpanCertificate' Table ![![74, -165, 94, -93, 66]] 
 ![![313, 0, 0, 0, 0], ![272, 1, 0, 0, 0], ![197, 0, 1, 0, 0], ![219, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![74, -165, 94, -93, 66], ![-279, -226, -258, 87, -756], ![261, 3657, -139, 981, 2790], ![630, -2376, 902, -1087, -36], ![-846, 966, -966, 774, -1297]]]
  hmulB := by decide  
  f := ![![![5102, -7101, -292, 1389, 3732]], ![![4447, -6220, -272, 1179, 3234]], ![![3127, -4512, -261, 708, 2208]], ![![3480, -4911, -230, 896, 2520]], ![![204, -228, 18, 108, 179]]]
  g := ![![![147, -165, 94, -93, 66], ![326, -226, -258, 87, -756], ![-3883, 3657, -139, 981, 2790], ![2261, -2376, 902, -1087, -36], ![-726, 966, -966, 774, -1297]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N2 : Nat.card (O ⧸ I313N2) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N2)

lemma isPrimeI313N2 : Ideal.IsPrime I313N2 := prime_ideal_of_norm_prime hp313.out _ NI313N2
def MulI313N0 : IdealMulLeCertificate' Table 
  ![![41, -1752, 236, -564, -966]] ![![-29, -151, -13, -30, -156]]
  ![![526589, -3188183, 886893, -1279428, -756306]] where
 M := ![![![526589, -3188183, 886893, -1279428, -756306]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI313N1 : IdealMulLeCertificate' Table 
  ![![526589, -3188183, 886893, -1279428, -756306]] ![![74, -165, 94, -93, 66]]
  ![![313, 0, 0, 0, 0]] where
 M := ![![![993744952, 6186339206, 325319993, 1349054727, 5946440982]]]
 hmul := by decide  
 g := ![![![![3174904, 19764662, 1039361, 4310079, 18998214]]]]
 hle2 := by decide  


def PBC313 : ContainsPrimesAboveP 313 ![I313N0, I313N1, I313N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI313N0
    exact isPrimeI313N1
    exact isPrimeI313N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 313 (by decide) (𝕀 ⊙ MulI313N0 ⊙ MulI313N1)
instance hp317 : Fact (Nat.Prime 317) := {out := by norm_num}

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-276643, 32826, -18210, -40910, -71276]] i)))

def SI317N0: IdealEqSpanCertificate' Table ![![-276643, 32826, -18210, -40910, -71276]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![48, 47, 1, 0, 0], ![258, 63, 0, 1, 0], ![152, 303, 0, 0, 1]] where
  M :=![![![-276643, 32826, -18210, -40910, -71276], ![-122730, 14563, -8084, -18162, -31632], ![-54486, 6486, -3599, -8094, -14076], ![57318, -6784, 3774, 8473, 14760], ![163890, -19452, 10794, 24252, 42241]]]
  hmulB := by decide  
  f := ![![![-299, 974, -410, 470, -76]], ![![1410, -133, 1444, -822, 3048]], ![![156, 83, 149, -60, 396]], ![![30, 805, -58, 235, 552]], ![![1216, 317, 1198, -574, 2889]]]
  g := ![![![69357, 79062, -18210, -40910, -71276], ![30786, 35089, -8084, -18162, -31632], ![13710, 15617, -3599, -8094, -14076], ![-14364, -16373, 3774, 8473, 14760], ![-41110, -46857, 10794, 24252, 42241]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P0 : CertificateIrreducibleZModOfList' 317 2 2 8 [316, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [218, 316], [0, 1]]
 g := ![![[218, 316], [23], [145, 160], [191, 181], [222, 135], [90, 240], [291], [1]], ![[0, 1], [23], [155, 157], [24, 136], [171, 182], [105, 77], [291], [1]]]
 h' := ![![[218, 316], [126, 203], [145, 96], [191, 124], [222, 205], [90, 197], [292, 157], [1, 218], [0, 1]], ![[0, 1], [0, 114], [151, 221], [278, 193], [215, 112], [241, 120], [282, 160], [292, 99], [218, 316]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [163, 173]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N0 : CertifiedPrimeIdeal' SI317N0 317 where
  n := 2
  hpos := by decide
  P := [316, 99, 1]
  hirr := P317P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6665, -19983, -3184, -9241, -24490]
  a := ![-33, -20, -16, -29, -65]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![19725, 25654, -3184, -9241, -24490]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N0 : Ideal.IsPrime I317N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N0 B_one_repr
lemma NI317N0 : Nat.card (O ⧸ I317N0) = 100489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N0

def I317N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-775, -10090, 912, -3474, -7346]] i)))

def SI317N1: IdealEqSpanCertificate' Table ![![-775, -10090, 912, -3474, -7346]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![224, 146, 1, 0, 0], ![44, 25, 0, 1, 0], ![223, 155, 0, 0, 1]] where
  M :=![![![-775, -10090, 912, -3474, -7346], ![-10422, 39089, -13564, 17088, 1194], ![51264, -24102, 56177, -33702, 98946], ![-11640, -93092, -2852, -18691, -83772], ![-8208, 116754, -22502, 40692, 51865]]]
  hmulB := by decide  
  f := ![![![242064507137929, -28725904083058, 15932185832676, 35793458606250, 62365143234806]], ![![107380375818750, -12742877560379, 7067554523192, 15878061110388, 27665321933082]], ![![220654948428280, -26185222108548, 14523052903645, 32627682001854, 56849216049494]], ![![41909082946258, -4973369748243, 2758369268884, 6196988742377, 10797394428806]], ![![222337393284449, -26384878597369, 14633787948690, 32876460813042, 57282678665225]]]
  g := ![![![5003, 3414, 912, -3474, -7346], ![6340, 4439, -13564, 17088, 1194], ![-104462, -71672, 56177, -33702, 98946], ![63504, 43455, -2852, -18691, -83772], ![-26259, -17837, -22502, 40692, 51865]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P1 : CertificateIrreducibleZModOfList' 317 2 2 8 [145, 211, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 316], [0, 1]]
 g := ![![[137, 223], [254], [249, 316], [90, 34], [281, 251], [175, 283], [141], [1]], ![[0, 94], [254], [143, 1], [207, 283], [259, 66], [58, 34], [141], [1]]]
 h' := ![![[106, 316], [80, 77], [33, 184], [264, 203], [148, 273], [302, 85], [263, 56], [172, 106], [0, 1]], ![[0, 1], [0, 240], [200, 133], [226, 114], [239, 44], [119, 232], [176, 261], [313, 211], [106, 316]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [207, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N1 : CertifiedPrimeIdeal' SI317N1 317 where
  n := 2
  hpos := by decide
  P := [145, 211, 1]
  hirr := P317P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-809, -1986, -2326, 1650, -4428]
  a := ![18, 2, 10, -2, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4527, 3100, -2326, 1650, -4428]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N1 : Ideal.IsPrime I317N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N1 B_one_repr
lemma NI317N1 : Nat.card (O ⧸ I317N1) = 100489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N1

def I317N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1126065331, 133630680, -74115294, -166508396, -290117814]] i)))

def SI317N2: IdealEqSpanCertificate' Table ![![-1126065331, 133630680, -74115294, -166508396, -290117814]] 
 ![![317, 0, 0, 0, 0], ![124, 1, 0, 0, 0], ![157, 0, 1, 0, 0], ![286, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-1126065331, 133630680, -74115294, -166508396, -290117814], ![-499525188, 59278879, -32877716, -73863510, -128696934], ![-221590530, 26296248, -14584631, -32766024, -57090258], ![233379582, -27695260, 15360562, 34509241, 60127572], ![667037646, -79157658, 43903040, 98633148, 171854597]]]
  hmulB := by decide  
  f := ![![![-5879, -3580, -5578, -12292, -10158]], ![![-2416, -1357, -2232, -4934, -4110]], ![![-3289, -1472, -2845, -6356, -5376]], ![![-5380, -3100, -5002, -11071, -9192]], ![![10, -178, -92, -160, -91]]]
  g := ![![![138429575, 133630680, -74115294, -166508396, -290117814], ![61407680, 59278879, -32877716, -73863510, -128696934], ![27240589, 26296248, -14584631, -32766024, -57090258], ![-28689842, -27695260, 15360562, 34509241, 60127572], ![-82000338, -79157658, 43903040, 98633148, 171854597]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI317N2 : Nat.card (O ⧸ I317N2) = 317 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI317N2)

lemma isPrimeI317N2 : Ideal.IsPrime I317N2 := prime_ideal_of_norm_prime hp317.out _ NI317N2
def MulI317N0 : IdealMulLeCertificate' Table 
  ![![-276643, 32826, -18210, -40910, -71276]] ![![-775, -10090, 912, -3474, -7346]]
  ![![-5879, -3580, -5578, -12292, -10158]] where
 M := ![![![-5879, -3580, -5578, -12292, -10158]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI317N1 : IdealMulLeCertificate' Table 
  ![![-5879, -3580, -5578, -12292, -10158]] ![![-1126065331, 133630680, -74115294, -166508396, -290117814]]
  ![![317, 0, 0, 0, 0]] where
 M := ![![![317, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC317 : ContainsPrimesAboveP 317 ![I317N0, I317N1, I317N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI317N0
    exact isPrimeI317N1
    exact isPrimeI317N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 317 (by decide) (𝕀 ⊙ MulI317N0 ⊙ MulI317N1)
instance hp331 : Fact (Nat.Prime 331) := {out := by norm_num}

def I331N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![260, -255, 102, 51, 264]] i)))

def SI331N0: IdealEqSpanCertificate' Table ![![260, -255, 102, 51, 264]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![259, 165, 1, 0, 0], ![325, 85, 0, 1, 0], ![208, 295, 0, 0, 1]] where
  M :=![![![260, -255, 102, 51, 264], ![153, -916, -204, -27, -486], ![-81, 2403, -943, 153, 1296], ![0, -1272, 528, -1501, -252], ![-918, 684, -552, 612, -1435]]]
  hmulB := by decide  
  f := ![![![-9507809968, 1128296091, -625784412, -1405895505, -2449578162]], ![![-4217686515, 500514758, -277599414, -623658501, -1086638544]], ![![-9547770490, 1133038224, -628414531, -1411804365, -2459873532]], ![![-10412601445, 1235668103, -685335918, -1539684703, -2682687306]], ![![-9716646331, 1153078796, -639529590, -1436775603, -2503382455]]]
  g := ![![![-295, -300, 102, 51, 264], ![492, 539, -204, -27, -486], ![-227, -717, -943, 153, 1296], ![1219, 343, 528, -1501, -252], ![730, 1399, -552, 612, -1435]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P0 : CertificateIrreducibleZModOfList' 331 2 2 8 [120, 233, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [98, 330], [0, 1]]
 g := ![![[104, 80], [276, 85], [214], [97, 323], [81], [223], [140, 5], [1]], ![[0, 251], [0, 246], [214], [306, 8], [81], [223], [299, 326], [1]]]
 h' := ![![[98, 330], [311, 61], [184, 167], [276, 144], [274, 181], [323, 9], [81, 47], [211, 98], [0, 1]], ![[0, 1], [0, 270], [0, 164], [155, 187], [138, 150], [212, 322], [53, 284], [216, 233], [98, 330]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [197, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N0 : CertifiedPrimeIdeal' SI331N0 331 where
  n := 2
  hpos := by decide
  P := [120, 233, 1]
  hirr := P331P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12432, -29770, 4422, 922, -3558]
  a := ![55, 37, 28, 56, 97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2092, 640, 4422, 922, -3558]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N0 : Ideal.IsPrime I331N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N0 B_one_repr
lemma NI331N0 : Nat.card (O ⧸ I331N0) = 109561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N0

def I331N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![845, -639, 185, 610, 796]] i)))

def SI331N1: IdealEqSpanCertificate' Table ![![845, -639, 185, 610, 796]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![221, 81, 1, 0, 0], ![161, 323, 0, 1, 0], ![233, 236, 0, 0, 1]] where
  M :=![![![845, -639, 185, 610, 796], ![1830, -2156, -29, 552, 1272], ![1656, -4785, -1604, -2334, -504], ![-2082, 278, -1172, -2795, -2718], ![-1665, 2550, 351, 87, -815]]]
  hmulB := by decide  
  f := ![![![-733867, 87097, -48303, -108512, -189068]], ![![-325536, 38608, -21415, -48150, -83868]], ![![-570083, 67652, -37520, -84298, -146872]], ![![-674165, 79985, -44362, -99699, -173686]], ![![-747380, 88681, -49184, -110521, -192549]]]
  g := ![![![-978, -1210, 185, 610, 796], ![-1139, -1445, -29, 552, 1272], ![2566, 3015, -1604, -2334, -504], ![4049, 4953, -1172, -2795, -2718], ![292, 418, 351, 87, -815]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P1 : CertificateIrreducibleZModOfList' 331 2 2 8 [31, 185, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 330], [0, 1]]
 g := ![![[38, 299], [185, 1], [109], [294, 259], [197], [293], [290, 132], [1]], ![[0, 32], [0, 330], [109], [43, 72], [197], [293], [33, 199], [1]]]
 h' := ![![[146, 330], [223, 300], [146, 330], [154, 289], [76, 119], [15, 292], [278, 151], [300, 146], [0, 1]], ![[0, 1], [0, 31], [0, 1], [311, 42], [238, 212], [279, 39], [147, 180], [101, 185], [146, 330]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [165]]
 b := ![[], [101, 248]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N1 : CertifiedPrimeIdeal' SI331N1 331 where
  n := 2
  hpos := by decide
  P := [31, 185, 1]
  hirr := P331P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-395, -874, -210, -1424, -698]
  a := ![-3, -5, -1, -8, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1323, 1936, -210, -1424, -698]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N1 : Ideal.IsPrime I331N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N1 B_one_repr
lemma NI331N1 : Nat.card (O ⧸ I331N1) = 109561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N1

def I331N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16380142199026, -1943838852046, 1078107123453, 2422089668153, 4220155720172]] i)))

def SI331N2: IdealEqSpanCertificate' Table ![![16380142199026, -1943838852046, 1078107123453, 2422089668153, 4220155720172]] 
 ![![331, 0, 0, 0, 0], ![85, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![143, 0, 0, 1, 0], ![72, 0, 0, 0, 1]] where
  M :=![![![16380142199026, -1943838852046, 1078107123453, 2422089668153, 4220155720172], ![7266269004459, -862291415341, 478250816107, 1074444584661, 1872070848402], ![3223333753983, -382514468310, 212153169320, 476626105419, 830454962760], ![-3394821449520, 402864990374, -223440135202, -501983551681, -874636800162], ![-9702964111077, 1151455121082, -638629054599, -1434752448321, -2499857388199]]]
  hmulB := by decide  
  f := ![![![-623780, 582948, -75221, -339805, -522586]], ![![-163265, 154553, -18582, -86968, -135622]], ![![-106539, 108636, -7807, -48960, -83964]], ![![-263170, 249298, -29897, -140040, -218516]], ![![-133641, 121560, -17949, -76119, -113905]]]
  g := ![![![-1601376724508, -1943838852046, 1078107123453, 2422089668153, 4220155720172], ![-710374422662, -862291415341, 478250816107, 1074444584661, 1872070848402], ![-315123738624, -382514468310, 212153169320, 476626105419, 830454962760], ![331888941321, 402864990374, -223440135202, -501983551681, -874636800162], ![948593772717, 1151455121082, -638629054599, -1434752448321, -2499857388199]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI331N2 : Nat.card (O ⧸ I331N2) = 331 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI331N2)

lemma isPrimeI331N2 : Ideal.IsPrime I331N2 := prime_ideal_of_norm_prime hp331.out _ NI331N2
def MulI331N0 : IdealMulLeCertificate' Table 
  ![![260, -255, 102, 51, 264]] ![![845, -639, 185, 610, 796]]
  ![![-623780, 582948, -75221, -339805, -522586]] where
 M := ![![![-623780, 582948, -75221, -339805, -522586]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI331N1 : IdealMulLeCertificate' Table 
  ![![-623780, 582948, -75221, -339805, -522586]] ![![16380142199026, -1943838852046, 1078107123453, 2422089668153, 4220155720172]]
  ![![331, 0, 0, 0, 0]] where
 M := ![![![331, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC331 : ContainsPrimesAboveP 331 ![I331N0, I331N1, I331N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI331N0
    exact isPrimeI331N1
    exact isPrimeI331N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 331 (by decide) (𝕀 ⊙ MulI331N0 ⊙ MulI331N1)
instance hp337 : Fact (Nat.Prime 337) := {out := by norm_num}

def I337N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![451249, -6016059, 1122875, -2109208, -2632494]] i)))

def SI337N0: IdealEqSpanCertificate' Table ![![451249, -6016059, 1122875, -2109208, -2632494]] 
 ![![337, 0, 0, 0, 0], ![0, 337, 0, 0, 0], ![0, 0, 337, 0, 0], ![184, 39, 107, 1, 0], ![272, 273, 243, 0, 1]] where
  M :=![![![451249, -6016059, 1122875, -2109208, -2632494], ![-6327624, 15396422, -8125267, 8307108, -4757766], ![24921324, 14457387, 23703530, -9556980, 64115946], ![-1614678, -58994498, 4879368, -17286487, -39236070], ![-10105875, 60608052, -16956785, 24375801, 14165761]]]
  hmulB := by decide  
  f := ![![![-883994891429, 104904071903, -58182717711, -130714060198, -227751142362]], ![![-392142180594, 46535689214, -25809988295, -57985059774, -101030934102]], ![![-173955179322, 20643339585, -11449370560, -25722306786, -44817556338]], ![![-582725813996, 69152334835, -38353809355, -86166173441, -150132620814]], ![![-1155041216281, 137069261449, -76022426918, -170792985983, -297583118501]]]
  g := ![![![3277697, 2358795, 2571229, -2109208, -2632494], ![-714312, 2938544, 768995, 8307108, -4757766], ![-46457364, -50790723, -43127224, -9556980, 64115946], ![41101810, 33610165, 33794951, -17286487, -39236070], ![-24772523, -14116620, -18004295, 24375801, 14165761]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P0 : CertificateIrreducibleZModOfList' 337 3 2 8 [311, 312, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [99, 44, 204], [156, 292, 133], [0, 1]]
 g := ![![[276, 176, 301], [22, 179], [154, 255], [104, 56], [201, 287, 131], [13, 312], [9, 255, 1], []], ![[312, 57, 308, 22], [241, 216], [298, 95], [41, 110], [231, 271, 334, 247], [327, 179], [291, 325, 178, 275], [41, 165]], ![[233, 332, 283, 199], [92, 298], [256, 285], [242, 74], [170, 88, 69, 332], [89, 18], [27, 165, 109, 20], [112, 165]]]
 h' := ![![[99, 44, 204], [179, 88, 214], [142, 300, 193], [267, 169, 170], [171, 301, 122], [163, 249, 192], [234, 115, 271], [0, 0, 1], [0, 1]], ![[156, 292, 133], [30, 284, 234], [29, 147, 280], [104, 0, 203], [330, 109, 309], [310, 52, 31], [75, 299, 144], [83, 210, 292], [99, 44, 204]], ![[0, 1], [51, 302, 226], [78, 227, 201], [103, 168, 301], [35, 264, 243], [280, 36, 114], [177, 260, 259], [288, 127, 44], [156, 292, 133]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146, 269], []]
 b := ![[], [246, 113, 225], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N0 : CertifiedPrimeIdeal' SI337N0 337 where
  n := 3
  hpos := by decide
  P := [311, 312, 82, 1]
  hirr := P337P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1831013, 9716129, 1083927, 1439910, 10220811]
  a := ![39, 22, 23, 31, 75]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9030187, -8417572, -7823868, 1439910, 10220811]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI337N0 : Ideal.IsPrime I337N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N0 B_one_repr
lemma NI337N0 : Nat.card (O ⧸ I337N0) = 38272753 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N0

def I337N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -9, 13, -30, -24]] i)))

def SI337N1: IdealEqSpanCertificate' Table ![![-19, -9, 13, -30, -24]] 
 ![![337, 0, 0, 0, 0], ![78, 1, 0, 0, 0], ![319, 0, 1, 0, 0], ![195, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![-19, -9, 13, -30, -24], ![-90, 104, -39, 60, -108], ![180, 561, 164, 270, 684], ![180, -534, 158, -73, -18], ![-117, 246, -201, 117, -121]]]
  hmulB := by decide  
  f := ![![![-3802157077, 451203693, -250250125, -562215228, -979582152]], ![![-885029370, 105026834, -58250805, -130867026, -228017664]], ![![-3601294681, 427367262, -237029777, -532514220, -927832260]], ![![-2197722921, 260804769, -144649583, -324971659, -566218098]], ![![-455893736, 54101115, -30005984, -67411839, -117455791]]]
  g := ![![![10, -9, 13, -30, -24], ![-9, 104, -39, 60, -108], ![-524, 561, 164, 270, 684], ![19, -534, 158, -73, -18], ![80, 246, -201, 117, -121]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI337N1 : Nat.card (O ⧸ I337N1) = 337 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI337N1)

lemma isPrimeI337N1 : Ideal.IsPrime I337N1 := prime_ideal_of_norm_prime hp337.out _ NI337N1

def I337N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16820, 15376, -2201, -9493, -14290]] i)))

def SI337N2: IdealEqSpanCertificate' Table ![![-16820, 15376, -2201, -9493, -14290]] 
 ![![337, 0, 0, 0, 0], ![291, 1, 0, 0, 0], ![243, 0, 1, 0, 0], ![201, 0, 0, 1, 0], ![124, 0, 0, 0, 1]] where
  M :=![![![-16820, 15376, -2201, -9493, -14290], ![-28479, 43331, 5883, 1185, -14088], ![3555, 76068, 44516, 81117, 49374], ![54798, -21150, 23256, 59795, 63474], ![19809, -47016, -13467, -17649, -67]]]
  hmulB := by decide  
  f := ![![![624616192318, -74123484854, 41110947523, 92360396363, 160925196188]], ![![540179208171, -64103309917, 35553479646, 79874915808, 139170975906]], ![![450755633799, -53491374072, 29667804701, 66652080930, 116132017860]], ![![372161428902, -44164564380, 24494896485, 55030557176, 95883122622]], ![![228731184925, -27143632730, 15054614107, 33821894405, 58929965731]]]
  g := ![![![-820, 15376, -2201, -9493, -14290], ![-37266, 43331, 5883, 1185, -14088], ![-164322, 76068, 44516, 81117, 49374], ![-57363, -21150, 23256, 59795, 63474], ![60919, -47016, -13467, -17649, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI337N2 : Nat.card (O ⧸ I337N2) = 337 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI337N2)

lemma isPrimeI337N2 : Ideal.IsPrime I337N2 := prime_ideal_of_norm_prime hp337.out _ NI337N2
def MulI337N0 : IdealMulLeCertificate' Table 
  ![![451249, -6016059, 1122875, -2109208, -2632494]] ![![-19, -9, 13, -30, -24]]
  ![![663333437, 478925046, 620520468, -225354374, 1763448414]] where
 M := ![![![663333437, 478925046, 620520468, -225354374, 1763448414]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI337N1 : IdealMulLeCertificate' Table 
  ![![663333437, 478925046, 620520468, -225354374, 1763448414]] ![![-16820, 15376, -2201, -9493, -14290]]
  ![![337, 0, 0, 0, 0]] where
 M := ![![![-7443885160, 9421432838, -8592808813, 7094812809, -10847854760]]]
 hmul := by decide  
 g := ![![![![-22088680, 27956774, -25497949, 21052857, -32189480]]]]
 hle2 := by decide  


def PBC337 : ContainsPrimesAboveP 337 ![I337N0, I337N1, I337N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI337N0
    exact isPrimeI337N1
    exact isPrimeI337N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 337 (by decide) (𝕀 ⊙ MulI337N0 ⊙ MulI337N1)
instance hp347 : Fact (Nat.Prime 347) := {out := by norm_num}

def I347N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2450, 1228, -889, -2407, -2686]] i)))

def SI347N0: IdealEqSpanCertificate' Table ![![-2450, 1228, -889, -2407, -2686]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![244, 246, 1, 0, 0], ![59, 76, 0, 1, 0], ![194, 343, 0, 0, 1]] where
  M :=![![![-2450, 1228, -889, -2407, -2686], ![-7221, 6185, -1179, -4497, -6384], ![-13491, 18552, 1688, -1413, -7830], ![2904, 2862, 3446, 7145, 5694], ![8001, -8304, 501, 3537, 6227]]]
  hmulB := by decide  
  f := ![![![1100, -1234, 1209, -965, 1612]], ![![-2895, -6875, -2199, -477, -10626]], ![![-1283, -5588, -730, -967, -6316]], ![![-418, -1784, -239, -306, -2030]], ![![-2278, -7481, -1530, -992, -9669]]]
  g := ![![![2529, 3816, -889, -2407, -2686], ![5142, 8149, -1179, -4497, -6384], ![3392, 6906, 1688, -1413, -7830], ![-6813, -9628, 3446, 7145, 5694], ![-4412, -7309, 501, 3537, 6227]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P0 : CertificateIrreducibleZModOfList' 347 2 2 8 [51, 231, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 346], [0, 1]]
 g := ![![[127, 271], [126, 185], [137], [209, 196], [313, 330], [219], [56, 270], [1]], ![[333, 76], [72, 162], [137], [43, 151], [76, 17], [219], [146, 77], [1]]]
 h' := ![![[116, 346], [167, 273], [188, 78], [98, 22], [346, 333], [89, 315], [267, 185], [296, 116], [0, 1]], ![[0, 1], [258, 74], [214, 269], [221, 325], [110, 14], [194, 32], [213, 162], [219, 231], [116, 346]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [170, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N0 : CertifiedPrimeIdeal' SI347N0 347 where
  n := 2
  hpos := by decide
  P := [51, 231, 1]
  hirr := P347P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4045, -5296, 2096, 1758, 2622]
  a := ![23, 15, 11, 22, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3227, -4478, 2096, 1758, 2622]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N0 : Ideal.IsPrime I347N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N0 B_one_repr
lemma NI347N0 : Nat.card (O ⧸ I347N0) = 120409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N0

def I347N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1019, 862, -238, -802, -1044]] i)))

def SI347N1: IdealEqSpanCertificate' Table ![![-1019, 862, -238, -802, -1044]] 
 ![![347, 0, 0, 0, 0], ![247, 1, 0, 0, 0], ![63, 0, 1, 0, 0], ![59, 0, 0, 1, 0], ![341, 0, 0, 0, 1]] where
  M :=![![![-1019, 862, -238, -802, -1044], ![-2406, 2927, 60, -702, -1680], ![-2106, 6450, 2225, 3294, 828], ![2850, -432, 1594, 3809, 3720], ![2142, -3444, -506, -180, 1033]]]
  hmulB := by decide  
  f := ![![![-22885, -30154, -19906, 3574, -69084]], ![![-16259, -20487, -14246, 2828, -48516]], ![![-3303, -9060, -2353, -936, -12816]], ![![-4699, -5098, -4208, 1071, -13524]], ![![-21973, -27946, -19224, 3742, -65723]]]
  g := ![![![589, 862, -238, -802, -1044], ![-331, 2927, 60, -702, -1680], ![-6375, 6450, 2225, 3294, 828], ![-4277, -432, 1594, 3809, 3720], ![1565, -3444, -506, -180, 1033]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI347N1 : Nat.card (O ⧸ I347N1) = 347 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI347N1)

lemma isPrimeI347N1 : Ideal.IsPrime I347N1 := prime_ideal_of_norm_prime hp347.out _ NI347N1

def I347N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![184887128, -21940587, 12168888, 27338767, 47634016]] i)))

def SI347N2: IdealEqSpanCertificate' Table ![![184887128, -21940587, 12168888, 27338767, 47634016]] 
 ![![347, 0, 0, 0, 0], ![258, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![67, 0, 0, 1, 0], ![113, 0, 0, 0, 1]] where
  M :=![![![184887128, -21940587, 12168888, 27338767, 47634016], ![82016301, -9732770, 5398180, 12127581, 21130554], ![36382743, -4317321, 2394811, 5380161, 9373824], ![-38318070, 4547144, -2521950, -5665811, -9872028], ![-109519992, 12996636, -7208442, -16194540, -28216613]]]
  hmulB := by decide  
  f := ![![![-1857044, 2801999, -2194946, 1908575, -2433574]], ![![-1364241, 2112082, -1618402, 1418643, -1755360]], ![![-322341, 216651, -351191, 248103, -585390]], ![![-407770, 677903, -488888, 438404, -496514]], ![![-547814, 884231, -653864, 580799, -683043]]]
  g := ![![![-6048749, -21940587, 12168888, 27338767, 47634016], ![-2683344, -9732770, 5398180, 12127581, 21130554], ![-1190634, -4317321, 2394811, 5380161, 9373824], ![1253557, 4547144, -2521950, -5665811, -9872028], ![3583187, 12996636, -7208442, -16194540, -28216613]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI347N2 : Nat.card (O ⧸ I347N2) = 347 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI347N2)

lemma isPrimeI347N2 : Ideal.IsPrime I347N2 := prime_ideal_of_norm_prime hp347.out _ NI347N2

def I347N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-278, 6007, -946, 2009, 3012]] i)))

def SI347N3: IdealEqSpanCertificate' Table ![![-278, 6007, -946, 2009, 3012]] 
 ![![347, 0, 0, 0, 0], ![290, 1, 0, 0, 0], ![221, 0, 1, 0, 0], ![46, 0, 0, 1, 0], ![281, 0, 0, 0, 1]] where
  M :=![![![-278, 6007, -946, 2009, 3012], ![6027, -17170, 8016, -8685, 3018], ![-26055, -5403, -25855, 12987, -61164], ![3480, 56808, -2744, 15563, 42060], ![8514, -62448, 15544, -24048, -18815]]]
  hmulB := by decide  
  f := ![![![16165130, -1918915, 1064300, 2391313, 4165818]], ![![13530437, -1606166, 890834, 2001565, 3486852]], ![![10304555, -1223248, 678439, 1524352, 2655528]], ![![2133268, -253238, 140448, 315565, 549744]], ![![13062890, -1550647, 860052, 1932397, 3366355]]]
  g := ![![![-7124, 6007, -946, 2009, 3012], ![7969, -17170, 8016, -8685, 3018], ![68716, -5403, -25855, 12987, -61164], ![-81842, 56808, -2744, 15563, 42060], ![60739, -62448, 15544, -24048, -18815]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI347N3 : Nat.card (O ⧸ I347N3) = 347 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI347N3)

lemma isPrimeI347N3 : Ideal.IsPrime I347N3 := prime_ideal_of_norm_prime hp347.out _ NI347N3
def MulI347N0 : IdealMulLeCertificate' Table 
  ![![-2450, 1228, -889, -2407, -2686]] ![![-1019, 862, -238, -802, -1044]]
  ![![-11199146, 6038814, -3798887, -10510305, -11970010]] where
 M := ![![![-11199146, 6038814, -3798887, -10510305, -11970010]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI347N1 : IdealMulLeCertificate' Table 
  ![![-11199146, 6038814, -3798887, -10510305, -11970010]] ![![184887128, -21940587, 12168888, 27338767, 47634016]]
  ![![179319458555, -19269179631, 11421732685, 24946582900, 44252463402]] where
 M := ![![![179319458555, -19269179631, 11421732685, 24946582900, 44252463402]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI347N2 : IdealMulLeCertificate' Table 
  ![![179319458555, -19269179631, 11421732685, 24946582900, 44252463402]] ![![-278, 6007, -946, 2009, 3012]]
  ![![347, 0, 0, 0, 0]] where
 M := ![![![181674626, -173037796, 17357287, 89493729, 144961332]]]
 hmul := by decide  
 g := ![![![![523558, -498668, 50021, 257907, 417756]]]]
 hle2 := by decide  


def PBC347 : ContainsPrimesAboveP 347 ![I347N0, I347N1, I347N2, I347N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI347N0
    exact isPrimeI347N1
    exact isPrimeI347N2
    exact isPrimeI347N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 347 (by decide) (𝕀 ⊙ MulI347N0 ⊙ MulI347N1 ⊙ MulI347N2)
instance hp349 : Fact (Nat.Prime 349) := {out := by norm_num}

def I349N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27007, 37385, -29181, 24816, -35972]] i)))

def SI349N0: IdealEqSpanCertificate' Table ![![-27007, 37385, -29181, 24816, -35972]] 
 ![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![0, 0, 349, 0, 0], ![175, 71, 93, 1, 0], ![41, 243, 216, 0, 1]] where
  M :=![![![-27007, 37385, -29181, 24816, -35972], ![74448, 150914, 62201, 7278, 256812], ![21834, -1265265, 158192, -375396, -726768], ![-224922, 608914, -304544, 330239, -140418], ![262629, -101838, 276289, -186603, 524167]]]
  hmulB := by decide  
  f := ![![![779367876796475, -92487936951101, 51296383728261, 115243131539562, 200795192338228]], ![![345729394618686, -41027862968986, 22755194588461, 51122119973568, 89073212222688]], ![![153366359920704, -18200055004923, 10094257004582, 22677890783406, 39513083173344]], ![![501540719707787, -59518063091606, 33010374149918, 74161541493485, 129216212622370]], ![![425879060545312, -50539259922301, 28030480036411, 62973645765471, 109722854150109]]]
  g := ![![![-8295, 20105, 15567, 24816, -35972], ![-33606, -179860, -160705, 7278, 256812], ![273678, 578775, 550292, -375396, -726768], ![-149741, 32331, -1967, 330239, -140418], ![32743, -327294, -273896, -186603, 524167]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P0 : CertificateIrreducibleZModOfList' 349 3 2 8 [232, 142, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [296, 140, 8], [15, 208, 341], [0, 1]]
 g := ![![[95, 53, 256], [228, 14], [309, 33, 48], [77, 295, 93], [262, 106, 42], [343, 121], [255, 311, 1], []], ![[121, 72, 248, 170], [55, 300], [169, 292, 192, 8], [335, 260, 206, 294], [129, 150, 252, 284], [53, 77], [108, 70, 286, 253], [157, 64]], ![[189, 262, 33, 288], [158, 3], [60, 23, 92, 216], [200, 51, 291, 10], [286, 123, 65, 211], [286, 20], [136, 44, 36, 250], [173, 64]]]
 h' := ![![[296, 140, 8], [10, 316, 333], [206, 155, 70], [284, 72, 311], [291, 132, 267], [278, 154, 316], [170, 177, 11], [0, 0, 1], [0, 1]], ![[15, 208, 341], [45, 311, 247], [275, 345, 95], [337, 284, 1], [303, 170, 54], [316, 342, 301], [38, 210, 214], [238, 19, 208], [296, 140, 8]], ![[0, 1], [119, 71, 118], [63, 198, 184], [181, 342, 37], [306, 47, 28], [82, 202, 81], [54, 311, 124], [224, 330, 140], [15, 208, 341]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [331, 102], []]
 b := ![[], [178, 121, 249], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N0 : CertifiedPrimeIdeal' SI349N0 349 where
  n := 3
  hpos := by decide
  P := [232, 142, 38, 1]
  hirr := P349P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-237200, 1065632, -268152, 320060, 195200]
  a := ![21, 15, 10, 23, 38]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-184100, -197972, -206868, 320060, 195200]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI349N0 : Ideal.IsPrime I349N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N0 B_one_repr
lemma NI349N0 : Nat.card (O ⧸ I349N0) = 42508549 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N0

def I349N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9092, -11115, -6974, 471, -26154]] i)))

def SI349N1: IdealEqSpanCertificate' Table ![![-9092, -11115, -6974, 471, -26154]] 
 ![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![331, 140, 1, 0, 0], ![71, 279, 0, 1, 0], ![107, 203, 0, 0, 1]] where
  M :=![![![-9092, -11115, -6974, 471, -26154], ![1413, 127852, -10644, 38031, 81288], ![114093, -442185, 165883, -193635, -15678], ![-97524, -10836, -100648, 57889, -226440], ![62766, 221214, 37554, 31932, 272923]]]
  hmulB := by decide  
  f := ![![![6432269515900372, -763320320417103, 423358692543836, 951123216632649, 1657200448041840]], ![![2853369649897947, -338610661453862, 187802896215546, 421920461035443, 735137955670374]], ![![7248764246796109, -860214117865354, 477098689116813, 1071856200984978, 1867560948409464]], ![![3585811362671057, -425529849385707, 236010696762098, 530224740905341, 923843160197586]], ![![3620849996841629, -429687899883427, 238316867284696, 535405813986366, 932870462318977]]]
  g := ![![![14511, 17602, -6974, 471, -26154], ![-22560, -73049, -10644, 38031, 81288], ![-112801, 96106, 165883, -193635, -15678], ![152825, 125777, -100648, 57889, -226440], ![-125609, -198707, 37554, 31932, 272923]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P1 : CertificateIrreducibleZModOfList' 349 2 2 8 [339, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [333, 348], [0, 1]]
 g := ![![[138, 281], [345], [23, 64], [0, 85], [116, 139], [327], [121, 256], [1]], ![[179, 68], [345], [46, 285], [36, 264], [335, 210], [327], [213, 93], [1]]]
 h' := ![![[333, 348], [161, 242], [230, 272], [0, 8], [113, 145], [174, 103], [163, 26], [10, 333], [0, 1]], ![[0, 1], [128, 107], [66, 77], [221, 341], [236, 204], [271, 246], [96, 323], [266, 16], [333, 348]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [132, 191]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N1 : CertifiedPrimeIdeal' SI349N1 349 where
  n := 2
  hpos := by decide
  P := [339, 16, 1]
  hirr := P349P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2515, -3087, -6112, 3522, -10447]
  a := ![-23, -14, -24, -21, -53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8276, 5704, -6112, 3522, -10447]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI349N1 : Ideal.IsPrime I349N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N1 B_one_repr
lemma NI349N1 : Nat.card (O ⧸ I349N1) = 121801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N1
def MulI349N0 : IdealMulLeCertificate' Table 
  ![![-27007, 37385, -29181, 24816, -35972]] ![![-9092, -11115, -6974, 471, -26154]]
  ![![349, 0, 0, 0, 0]] where
 M := ![![![-7708949320, 9756914126, -8898784201, 7347447093, -11234128520]]]
 hmul := by decide  
 g := ![![![![-22088680, 27956774, -25497949, 21052857, -32189480]]]]
 hle2 := by decide  


def PBC349 : ContainsPrimesAboveP 349 ![I349N0, I349N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI349N0
    exact isPrimeI349N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 349 (by decide) (𝕀 ⊙ MulI349N0)
instance hp353 : Fact (Nat.Prime 353) := {out := by norm_num}

def I353N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1432208, -169960, 94265, 211777, 368992]] i)))

def SI353N0: IdealEqSpanCertificate' Table ![![1432208, -169960, 94265, 211777, 368992]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![0, 0, 353, 0, 0], ![183, 163, 143, 1, 0], ![215, 304, 275, 0, 1]] where
  M :=![![![1432208, -169960, 94265, 211777, 368992], ![635331, -75395, 41817, 93945, 163686], ![281835, -33444, 18550, 41679, 72612], ![-296826, 35226, -19536, -43889, -76470], ![-848385, 100674, -55839, -125451, -218579]]]
  hmulB := by decide  
  f := ![![![-26, -2, -11, -43, -34]], ![![-129, 59, -45, -93, -156]], ![![-279, 486, -34, -81, -90]], ![![-186, 223, -40, -98, -126]], ![![-344, 428, -72, -169, -225]]]
  g := ![![![-330471, -416043, -372982, 211777, 368992], ![-146598, -184558, -165456, 93945, 163686], ![-65034, -81873, -73399, 41679, 72612], ![68487, 86221, 77297, -43889, -76470], ![195761, 246451, 220943, -125451, -218579]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P0 : CertificateIrreducibleZModOfList' 353 3 2 8 [273, 253, 158, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [150, 154, 158], [45, 198, 195], [0, 1]]
 g := ![![[46, 48, 270], [135, 254], [166, 184], [213, 156], [254, 244], [187, 258, 49], [1, 195, 1], []], ![[337, 331, 48, 313], [84, 312], [85, 86], [76, 187], [1, 127], [143, 144, 279, 211], [201, 154, 89, 141], [60, 254]], ![[259, 208, 294, 112], [200, 259], [346, 309], [192, 198], [298, 11], [275, 48, 229, 7], [97, 316, 97, 320], [23, 254]]]
 h' := ![![[150, 154, 158], [48, 148, 254], [292, 276, 158], [255, 180, 193], [152, 131, 266], [134, 203, 226], [80, 168, 7], [0, 0, 1], [0, 1]], ![[45, 198, 195], [230, 34, 252], [131, 277, 56], [96, 96, 290], [271, 335, 295], [292, 281, 221], [344, 129, 43], [119, 155, 198], [150, 154, 158]], ![[0, 1], [18, 171, 200], [337, 153, 139], [292, 77, 223], [200, 240, 145], [259, 222, 259], [101, 56, 303], [335, 198, 154], [45, 198, 195]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94, 49], []]
 b := ![[], [269, 118, 203], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N0 : CertifiedPrimeIdeal' SI353N0 353 where
  n := 3
  hpos := by decide
  P := [273, 253, 158, 1]
  hirr := P353P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-192249, -521478, -230942, 3540, -793588]
  a := ![-12, -7, -9, -11, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![480967, 680318, 616146, 3540, -793588]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N0 : Ideal.IsPrime I353N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N0 B_one_repr
lemma NI353N0 : Nat.card (O ⧸ I353N0) = 43986977 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N0

def I353N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26, -2, -11, -43, -34]] i)))

def SI353N1: IdealEqSpanCertificate' Table ![![-26, -2, -11, -43, -34]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![243, 201, 1, 0, 0], ![155, 191, 0, 1, 0], ![266, 88, 0, 0, 1]] where
  M :=![![![-26, -2, -11, -43, -34], ![-129, 59, -45, -93, -156], ![-279, 486, -34, -81, -90], ![24, -30, 90, 17, 42], ![99, -72, -21, 135, 59]]]
  hmulB := by decide  
  f := ![![![1432208, -169960, 94265, 211777, 368992]], ![![635331, -75395, 41817, 93945, 163686]], ![![1348470, -160023, 88754, 199395, 347418]], ![![971795, -115323, 63962, 143697, 250372]], ![![1235207, -146582, 81299, 182647, 318237]]]
  g := ![![![52, 38, -11, -43, -34], ![189, 115, -45, -93, -156], ![126, 87, -34, -81, -90], ![-101, -71, 90, 17, 42], ![-89, -76, -21, 135, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P1 : CertificateIrreducibleZModOfList' 353 2 2 8 [130, 279, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 352], [0, 1]]
 g := ![![[347, 334], [22], [338], [328], [232], [271, 167], [155, 181], [1]], ![[0, 19], [22], [338], [328], [232], [274, 186], [135, 172], [1]]]
 h' := ![![[74, 352], [306, 263], [65, 166], [52, 53], [156, 143], [70, 244], [324, 251], [223, 74], [0, 1]], ![[0, 1], [0, 90], [347, 187], [91, 300], [148, 210], [123, 109], [189, 102], [51, 279], [74, 352]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [151]]
 b := ![[], [207, 252]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N1 : CertifiedPrimeIdeal' SI353N1 353 where
  n := 2
  hpos := by decide
  P := [130, 279, 1]
  hirr := P353P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9391, -4484, 4289, 6089, 10584]
  a := ![27, 23, 14, 37, 51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13575, -8388, 4289, 6089, 10584]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N1 : Ideal.IsPrime I353N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N1 B_one_repr
lemma NI353N1 : Nat.card (O ⧸ I353N1) = 124609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N1
def MulI353N0 : IdealMulLeCertificate' Table 
  ![![1432208, -169960, 94265, 211777, 368992]] ![![-26, -2, -11, -43, -34]]
  ![![353, 0, 0, 0, 0]] where
 M := ![![![353, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC353 : ContainsPrimesAboveP 353 ![I353N0, I353N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI353N0
    exact isPrimeI353N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 353 (by decide) (𝕀 ⊙ MulI353N0)
instance hp359 : Fact (Nat.Prime 359) := {out := by norm_num}

def I359N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![568, -69, 38, 83, 146]] i)))

def SI359N0: IdealEqSpanCertificate' Table ![![568, -69, 38, 83, 146]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![314, 350, 1, 0, 0], ![112, 159, 0, 1, 0], ![247, 0, 0, 0, 1]] where
  M :=![![![568, -69, 38, 83, 146], ![249, -28, 14, 39, 60], ![117, 9, 11, 21, 54], ![-114, -8, -2, -25, -36], ![-342, 54, -30, -42, -91]]]
  hmulB := by decide  
  f := ![![![-100, 61, -32, -89, -104]], ![![-267, 250, -28, -147, -222]], ![![-349, 299, -55, -221, -308]], ![![-149, 130, -22, -92, -130]], ![![-68, 41, -22, -61, -71]]]
  g := ![![![-158, -74, 38, 83, 146], ![-65, -31, 14, 39, 60], ![-53, -20, 11, 21, 54], ![34, 13, -2, -25, -36], ![101, 48, -30, -42, -91]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P0 : CertificateIrreducibleZModOfList' 359 2 2 8 [201, 309, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 358], [0, 1]]
 g := ![![[173, 91], [277, 345], [49, 229], [27], [333], [255, 264], [72, 346], [1]], ![[56, 268], [295, 14], [11, 130], [27], [333], [172, 95], [140, 13], [1]]]
 h' := ![![[50, 358], [327, 74], [203, 143], [156, 128], [103, 130], [82, 232], [247, 303], [158, 50], [0, 1]], ![[0, 1], [78, 285], [173, 216], [94, 231], [141, 229], [194, 127], [319, 56], [145, 309], [50, 358]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [243]]
 b := ![[], [14, 301]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N0 : CertifiedPrimeIdeal' SI359N0 359 where
  n := 2
  hpos := by decide
  P := [201, 309, 1]
  hirr := P359P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22412, -34109, -13712, -16737, -63198]
  a := ![-41, -22, -23, -31, -85]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![60634, 20686, -13712, -16737, -63198]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N0 : Ideal.IsPrime I359N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N0 B_one_repr
lemma NI359N0 : Nat.card (O ⧸ I359N0) = 128881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N0

def I359N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46394, -5506, 3053, 6859, 11952]] i)))

def SI359N1: IdealEqSpanCertificate' Table ![![46394, -5506, 3053, 6859, 11952]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![197, 251, 1, 0, 0], ![315, 4, 0, 1, 0], ![337, 81, 0, 0, 1]] where
  M :=![![![46394, -5506, 3053, 6859, 11952], ![20577, -2441, 1353, 3039, 5298], ![9117, -1074, 598, 1341, 2340], ![-9618, 1146, -632, -1421, -2478], ![-27477, 3258, -1807, -4059, -7075]]]
  hmulB := by decide  
  f := ![![![28, -80, 47, -43, 18]], ![![-129, -25, -123, 99, -312]], ![![-74, -57, -60, 47, -204]], ![![24, -74, 41, -38, 12]], ![![-4, -79, 15, -17, -55]]]
  g := ![![![-18784, -4923, 3053, 6859, 11952], ![-8325, -2182, 1353, 3039, 5298], ![-3676, -964, 598, 1341, 2340], ![3893, 1020, -632, -1421, -2478], ![11118, 2914, -1807, -4059, -7075]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P1 : CertificateIrreducibleZModOfList' 359 2 2 8 [61, 346, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 358], [0, 1]]
 g := ![![[194, 115], [127, 300], [62, 41], [98], [30], [91, 99], [252, 169], [1]], ![[253, 244], [78, 59], [236, 318], [98], [30], [301, 260], [295, 190], [1]]]
 h' := ![![[13, 358], [151, 111], [167, 194], [290, 339], [237, 226], [193, 87], [65, 278], [298, 13], [0, 1]], ![[0, 1], [158, 248], [176, 165], [30, 20], [303, 133], [247, 272], [89, 81], [108, 346], [13, 358]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [153, 225]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N1 : CertifiedPrimeIdeal' SI359N1 359 where
  n := 2
  hpos := by decide
  P := [61, 346, 1]
  hirr := P359P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4182, -10836, -2747, -12330, -11644]
  a := ![-17, -18, -9, -30, -34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![23245, 4655, -2747, -12330, -11644]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N1 : Ideal.IsPrime I359N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N1 B_one_repr
lemma NI359N1 : Nat.card (O ⧸ I359N1) = 128881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N1

def I359N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 11, 1, 0, -10]] i)))

def SI359N2: IdealEqSpanCertificate' Table ![![-11, 11, 1, 0, -10]] 
 ![![359, 0, 0, 0, 0], ![117, 1, 0, 0, 0], ![312, 0, 1, 0, 0], ![140, 0, 0, 1, 0], ![161, 0, 0, 0, 1]] where
  M :=![![![-11, 11, 1, 0, -10], ![0, 52, 11, 36, 30], ![108, -75, 88, 84, 126], ![42, -62, -4, 49, 6], ![-9, 36, -19, -33, 17]]]
  hmulB := by decide  
  f := ![![![20468489, -2429005, 1347193, 3026622, 5273470]], ![![6696081, -794627, 440722, 990132, 1725168]], ![![17799990, -2112333, 1171558, 2632038, 4585962]], ![![7970324, -945842, 524590, 1178551, 2053462]], ![![9145688, -1085323, 601950, 1352349, 2356281]]]
  g := ![![![0, 11, 1, 0, -10], ![-54, 52, 11, 36, 30], ![-141, -75, 88, 84, 126], ![2, -62, -4, 49, 6], ![10, 36, -19, -33, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI359N2 : Nat.card (O ⧸ I359N2) = 359 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI359N2)

lemma isPrimeI359N2 : Ideal.IsPrime I359N2 := prime_ideal_of_norm_prime hp359.out _ NI359N2
def MulI359N0 : IdealMulLeCertificate' Table 
  ![![568, -69, 38, 83, 146]] ![![46394, -5506, 3053, 6859, 11952]]
  ![![20468489, -2429005, 1347193, 3026622, 5273470]] where
 M := ![![![20468489, -2429005, 1347193, 3026622, 5273470]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI359N1 : IdealMulLeCertificate' Table 
  ![![20468489, -2429005, 1347193, 3026622, 5273470]] ![![-11, 11, 1, 0, -10]]
  ![![359, 0, 0, 0, 0]] where
 M := ![![![359, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC359 : ContainsPrimesAboveP 359 ![I359N0, I359N1, I359N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI359N0
    exact isPrimeI359N1
    exact isPrimeI359N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 359 (by decide) (𝕀 ⊙ MulI359N0 ⊙ MulI359N1)


lemma PB687I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313, 317, 331, 337, 347, 349, 353, 359] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 359 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 359 (by omega)

def PB687I7 : PrimesBelowBoundCertificateInterval O 307 359 687 where
  m := 9
  g := ![3, 3, 3, 3, 3, 4, 2, 2, 3]
  P := ![311, 313, 317, 331, 337, 347, 349, 353, 359]
  hP := PB687I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1, I311N2]
    · exact ![I313N0, I313N1, I313N2]
    · exact ![I317N0, I317N1, I317N2]
    · exact ![I331N0, I331N1, I331N2]
    · exact ![I337N0, I337N1, I337N2]
    · exact ![I347N0, I347N1, I347N2, I347N3]
    · exact ![I349N0, I349N1]
    · exact ![I353N0, I353N1]
    · exact ![I359N0, I359N1, I359N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC311
    · exact PBC313
    · exact PBC317
    · exact PBC331
    · exact PBC337
    · exact PBC347
    · exact PBC349
    · exact PBC353
    · exact PBC359
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![96721, 96721, 311]
    · exact ![97969, 97969, 313]
    · exact ![100489, 100489, 317]
    · exact ![109561, 109561, 331]
    · exact ![38272753, 337, 337]
    · exact ![120409, 347, 347, 347]
    · exact ![42508549, 121801]
    · exact ![43986977, 124609]
    · exact ![128881, 128881, 359]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI311N0
      exact NI311N1
      exact NI311N2
    · dsimp ; intro j
      fin_cases j
      exact NI313N0
      exact NI313N1
      exact NI313N2
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
      exact NI317N1
      exact NI317N2
    · dsimp ; intro j
      fin_cases j
      exact NI331N0
      exact NI331N1
      exact NI331N2
    · dsimp ; intro j
      fin_cases j
      exact NI337N0
      exact NI337N1
      exact NI337N2
    · dsimp ; intro j
      fin_cases j
      exact NI347N0
      exact NI347N1
      exact NI347N2
      exact NI347N3
    · dsimp ; intro j
      fin_cases j
      exact NI349N0
      exact NI349N1
    · dsimp ; intro j
      fin_cases j
      exact NI353N0
      exact NI353N1
    · dsimp ; intro j
      fin_cases j
      exact NI359N0
      exact NI359N1
      exact NI359N2
  β := ![I311N2, I313N2, I317N2, I331N2, I337N1, I337N2, I347N1, I347N2, I347N3, I359N2]
  Il := ![[I311N2], [I313N2], [I317N2], [I331N2], [I337N1, I337N2], [I347N1, I347N2, I347N3], [], [], [I359N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
