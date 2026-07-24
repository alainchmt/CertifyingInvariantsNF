
import IdealArithmetic.Examples.NF5_3_2025000000_3.RI5_3_2025000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9174, 3262, -7773, 5694, 19966]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-9174, 3262, -7773, 5694, 19966]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-9174, 3262, -7773, 5694, 19966], ![-24844, 8859, -21064, 15436, 54122], ![-67772, 24360, -57569, 42232, 148042], ![-81888, 30200, -69988, 51519, 180468], ![1090, -596, 1040, -810, -2805]]]
  hmulB := by decide  
  f := ![![![-169, 130, -211, 162, 592]], ![![820, -685, 1060, -800, -2906]], ![![-6388, 5512, -8557, 6436, 23342]], ![![23484, -20416, 31832, -23937, -86796]], ![![-9357, 8110, -12631, 9500, 34451]]]
  g := ![![![-4587, 3262, -7773, 5694, 19966], ![-12422, 8859, -21064, 15436, 54122], ![-33886, 24360, -57569, 42232, 148042], ![-40944, 30200, -69988, 51519, 180468], ![545, -596, 1040, -810, -2805]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3023, -2669, 4140, -3116, -11307]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![3023, -2669, 4140, -3116, -11307]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3023, -2669, 4140, -3116, -11307], ![-23718, 20455, -32001, 24070, 87273], ![176394, -153385, 239241, -179990, -652791], ![-656640, 569351, -888973, 668754, 2425212], ![261242, -226668, 353827, -266181, -965318]]]
  hmulB := by decide  
  f := ![![![1258, -781, 1275, -1008, -3480]], ![![5501, -3372, 5455, -4317, -14904]], ![![37481, -22834, 37049, -29356, -101310]], ![![139511, -85230, 138209, -109458, -377799]], ![![-25762, 15762, -25547, 20227, 69820]]]
  g := ![![![2334, -2669, 4140, -3116, -11307], ![-18121, 20455, -32001, 24070, 87273], ![135264, -153385, 239241, -179990, -652791], ![-502886, 569351, -888973, 668754, 2425212], ![200132, -226668, 353827, -266181, -965318]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 4, -8, 6, 21]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-13, 4, -8, 6, 21]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-13, 4, -8, 6, 21], ![-30, 9, -26, 20, 69], ![-198, 116, -203, 154, 537], ![-468, 252, -426, 335, 1158], ![60, -28, 47, -39, -133]]]
  hmulB := by decide  
  f := ![![![244, -212, 331, -249, -903]], ![![-799, 693, -1082, 814, 2952]], ![![7067, -6132, 9572, -7201, -26115]], ![![-25740, 22332, -34860, 26225, 95106]], ![![10373, -9000, 14049, -10569, -38329]]]
  g := ![![![-15, 4, -8, 6, 21], ![-41, 9, -26, 20, 69], ![-324, 116, -203, 154, 537], ![-726, 252, -426, 335, 1158], ![87, -28, 47, -39, -133]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-9174, 3262, -7773, 5694, 19966]] ![![3023, -2669, 4140, -3116, -11307]]
  ![![837932, -297473, 709705, -519776, -1822673]] where
 M := ![![![837932, -297473, 709705, -519776, -1822673]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![837932, -297473, 709705, -519776, -1822673]] ![![3023, -2669, 4140, -3116, -11307]]
  ![![-76790406, 27306040, -65083665, 47668537, 167167594]] where
 M := ![![![-76790406, 27306040, -65083665, 47668537, 167167594]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-76790406, 27306040, -65083665, 47668537, 167167594]] ![![-13, 4, -8, 6, 21]]
  ![![786840072, -279333712, 666430359, -488082317, -1711534027]] where
 M := ![![![786840072, -279333712, 666430359, -488082317, -1711534027]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![786840072, -279333712, 666430359, -488082317, -1711534027]] ![![-13, 4, -8, 6, 21]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-8071637922, 2865487396, -6836439168, 5006892336, 17557420672]]]
 hmul := by decide  
 g := ![![![![-4035818961, 1432743698, -3418219584, 2503446168, 8778710336]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 29, -38, 29, 107]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-19, 29, -38, 29, 107]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-19, 29, -38, 29, 107], ![394, -308, 500, -375, -1355], ![-2290, 2079, -3193, 2405, 8735], ![9348, -8005, 12557, -9443, -34230], ![-3642, 3160, -4933, 3711, 13458]]]
  hmulB := by decide  
  f := ![![![-81, 43, -68, 55, 189]], ![![-206, 126, -208, 165, 569]], ![![-1658, 1023, -1651, 1305, 4507]], ![![-6124, 3723, -6035, 4783, 16506]], ![![1095, -663, 1079, -856, -2953]]]
  g := ![![![-42, 29, -38, 29, 107], ![583, -308, 500, -375, -1355], ![-3675, 2079, -3193, 2405, 8735], ![14526, -8005, 12557, -9443, -34230], ![-5700, 3160, -4933, 3711, 13458]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![862549, -748400, 1168244, -878860, -3187228]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![862549, -748400, 1168244, -878860, -3187228]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![862549, -748400, 1168244, -878860, -3187228], ![-6505064, 5644189, -8810516, 6628076, 24037036], ![49059080, -42566640, 66446049, -49986796, -181279516], ![-181741248, 157689760, -246151952, 185178013, 671556960], ![72388232, -62808432, 98043260, -73757108, -267483695]]]
  hmulB := by decide  
  f := ![![![951, -1456, 2276, -1628, -5772]], ![![613, -347, 224, -160, -592]], ![![-1998, 1232, -1079, 772, 2804]], ![![2624, -3488, 5200, -3723, -13216]], ![![-1355, 1120, -1296, 928, 3325]]]
  g := ![![![820563, -748400, 1168244, -878860, -3187228], ![-6188419, 5644189, -8810516, 6628076, 24037036], ![46671046, -42566640, 66446049, -49986796, -181279516], ![-172894688, 157689760, -246151952, 185178013, 671556960], ![68864613, -62808432, 98043260, -73757108, -267483695]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-19, 29, -38, 29, 107]] ![![-19, 29, -38, 29, 107]]
  ![![-19795, 17490, -27122, 20414, 74078]] where
 M := ![![![-19795, 17490, -27122, 20414, 74078]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-19795, 17490, -27122, 20414, 74078]] ![![862549, -748400, 1168244, -878860, -3187228]]
  ![![190881518849, -165620411366, 258531610354, -194491124990, -705331405918]] where
 M := ![![![190881518849, -165620411366, 258531610354, -194491124990, -705331405918]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![190881518849, -165620411366, 258531610354, -194491124990, -705331405918]] ![![862549, -748400, 1168244, -878860, -3187228]]
  ![![-1785294674142211611, 1549030204988963842, -2418018830615784842, 1819054938645290534, 6596890101655956198]] where
 M := ![![![-1785294674142211611, 1549030204988963842, -2418018830615784842, 1819054938645290534, 6596890101655956198]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![-1785294674142211611, 1549030204988963842, -2418018830615784842, 1819054938645290534, 6596890101655956198]] ![![862549, -748400, 1168244, -878860, -3187228]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![16697672417257153075697817, -14487915805703045125372278, 22615474586446564118270298, -17013428603368680365908758, -61700015961243458850121878]]]
 hmul := by decide  
 g := ![![![![5565890805752384358565939, -4829305268567681708457426, 7538491528815521372756766, -5671142867789560121969586, -20566671987081152950040626]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3687, -3199, 4994, -3757, -13625]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![3687, -3199, 4994, -3757, -13625]] 
 ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![3687, -3199, 4994, -3757, -13625], ![-27814, 24132, -37670, 28339, 102773], ![209782, -182017, 284125, -213745, -775157], ![-777156, 674307, -1052583, 791849, 2871678], ![309542, -268576, 419243, -315393, -1143788]]]
  hmulB := by decide  
  f := ![![![-3205, 1137, -2712, 1987, 6967]], ![![-2383, 851, -2022, 1482, 5196]], ![![-7350, 2643, -6241, 4579, 16051]], ![![-5892, 2211, -5055, 3731, 13062]], ![![-1817, 623, -1525, 1112, 3903]]]
  g := ![![![5557, -3199, 4994, -3757, -13625], ![-41917, 24132, -37670, 28339, 102773], ![316154, -182017, 284125, -213745, -775157], ![-1171233, 674307, -1052583, 791849, 2871678], ![466502, -268576, 419243, -315393, -1143788]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![3687, -3199, 4994, -3757, -13625]] ![![3687, -3199, 4994, -3757, -13625]]
  ![![-147512395, 127990722, -199792086, 150301882, 545076994]] where
 M := ![![![-147512395, 127990722, -199792086, 150301882, 545076994]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-147512395, 127990722, -199792086, 150301882, 545076994]] ![![3687, -3199, 4994, -3757, -13625]]
  ![![5899617941831, -5118867222399, 7990494501216, -6011180847981, -21799836053793]] where
 M := ![![![5899617941831, -5118867222399, 7990494501216, -6011180847981, -21799836053793]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![5899617941831, -5118867222399, 7990494501216, -6011180847981, -21799836053793]] ![![3687, -3199, 4994, -3757, -13625]]
  ![![-235949606940239175, 204724224689301892, -319572225762683432, 240411459235590532, 871863703543255052]] where
 M := ![![![-235949606940239175, 204724224689301892, -319572225762683432, 240411459235590532, 871863703543255052]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-235949606940239175, 204724224689301892, -319572225762683432, 240411459235590532, 871863703543255052]] ![![3687, -3199, 4994, -3757, -13625]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![9436580057247499425055, -8187750600609515363715, 12780987142081301992890, -9615027594985338371065, -34869359369511678459565]]]
 hmul := by decide  
 g := ![![![![1887316011449499885011, -1637550120121903072743, 2556197428416260398578, -1923005518997067674213, -6973871873902335691913]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1403, 1643, -2337, 1672, 5946]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-1403, 1643, -2337, 1672, 5946]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![6, 4, 5, 2, 1]] where
  M :=![![![-1403, 1643, -2337, 1672, 5946], ![852, -2148, 3811, -2726, -9630], ![4908, -2559, 1514, -1080, -4026], ![-9780, 10441, -14261, 10215, 36366], ![3916, -2868, 2960, -2120, -7633]]]
  hmulB := by decide  
  f := ![![![-533, 209, -471, 346, 1218]], ![![-1044, 222, -737, 532, 1830]], ![![-5796, 3183, -6022, 4470, 15942]], ![![3900, -5537, 7417, -5649, -20802]], ![![-4538, 1397, -3630, 2648, 9233]]]
  g := ![![![-5297, -3163, -4581, -1460, 5946], ![8376, 5196, 7423, 2362, -9630], ![4152, 1935, 3092, 996, -4026], ![-32568, -19289, -28013, -8931, 36366], ![7102, 3952, 5875, 1878, -7633]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [3, 0, 0, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 4, 3, 5], [1, 1, 2, 6], [2, 1, 2, 3], [0, 1]]
 g := ![![[6, 1, 6, 1], []], ![[3, 1, 4, 4, 0, 5], [4, 1, 4, 6, 2, 6]], ![[0, 0, 5, 4, 5, 5], [6, 6, 1, 5, 0, 6]], ![[3, 6, 4, 5, 0, 5], [0, 6, 6, 1, 6, 6]]]
 h' := ![![[3, 4, 3, 5], [0, 0, 0, 1], [0, 1]], ![[1, 1, 2, 6], [1, 0, 3, 1], [3, 4, 3, 5]], ![[2, 1, 2, 3], [4, 6, 6, 3], [1, 1, 2, 6]], ![[0, 1], [1, 1, 5, 2], [2, 1, 2, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 6, 4], []]
 b := ![[], [], [6, 3, 4, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [3, 0, 0, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-871795492479357, 570195196446315, -916742653029465, 718152078858420, 2505028223148120]
  a := ![1566, -1159, 1784, -1386, -4887]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2271709261624011, -1349988242306595, -1920269109824295, -613129195348260, 2505028223148120]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![533, -209, 471, -346, -1218]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![533, -209, 471, -346, -1218]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![533, -209, 471, -346, -1218], ![1044, -222, 737, -532, -1830], ![5796, -3183, 6022, -4470, -15942], ![-3900, 5537, -7417, 5649, 20802], ![3212, -2796, 4360, -3280, -11897]]]
  hmulB := by decide  
  f := ![![![1403, -1643, 2337, -1672, -5946]], ![![680, -632, 791, -566, -2022]], ![![301, -808, 1453, -1040, -3672]], ![![1798, -1961, 2705, -1937, -6894]], ![![-359, 175, -89, 64, 241]]]
  g := ![![![132, -209, 471, -346, -1218], ![163, -222, 737, -532, -1830], ![1900, -3183, 6022, -4470, -15942], ![-3009, 5537, -7417, 5649, 20802], ![1579, -2796, 4360, -3280, -11897]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-1403, 1643, -2337, 1672, 5946]] ![![533, -209, 471, -346, -1218]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1601, -1704, 2330, -1670, -5952]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![1601, -1704, 2330, -1670, -5952]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![5, 10, 2, 9, 1]] where
  M :=![![![1601, -1704, 2330, -1670, -5952], ![-2136, 3285, -5338, 3842, 13644], ![96, -2448, 6139, -4566, -16296], ![-2952, 1400, -4780, 4065, 15276], ![1964, -2672, 5696, -4332, -15665]]]
  hmulB := by decide  
  f := ![![![-39077, 23848, -38674, 30630, 105720]], ![![-298680, 182319, -295622, 234142, 808140]], ![![-2283696, 1394112, -2260375, 1790310, 6179232]], ![![-8582232, 5239288, -8494676, 6728163, 23222148]], ![![-7581879, 4628562, -7504512, 5943903, 20515291]]]
  g := ![![![2851, 5256, 1294, 4718, -5952], ![-6396, -12105, -2966, -10814, 13644], ![7416, 14592, 3521, 12918, -16296], ![-7212, -13760, -3212, -12129, 15276], ![7299, 13998, 3366, 12423, -15665]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [6, 0, 4, 10, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 6, 2], [4, 2, 4, 1], [3, 2, 5, 10], [0, 1]]
 g := ![![[1, 5, 0, 9], [1, 1], []], ![[0, 0, 10, 0, 10], [0, 0, 3, 5, 6], [4]], ![[2, 5, 3, 4, 3, 3], [8, 9, 0, 5, 4, 4], [3, 9, 1]], ![[2, 6, 0, 7, 3, 7], [0, 4, 9, 0, 5, 2], [8, 2, 1]]]
 h' := ![![[5, 6, 2], [5, 5, 7, 8], [0, 0, 1], [0, 1]], ![[4, 2, 4, 1], [5, 1, 8, 7], [1, 5, 7, 6], [5, 6, 2]], ![[3, 2, 5, 10], [1, 1, 1, 5], [9, 6, 7, 2], [4, 2, 4, 1]], ![[0, 1], [9, 4, 6, 2], [5, 0, 7, 3], [3, 2, 5, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 1, 10], []]
 b := ![[], [], [9, 10, 5, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [6, 0, 4, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-194551691302637619, 120555874424863714, -195096604627021319, 154152301251861497, 533290881414368934]
  a := ![1757, -1371, 1997, -1666, -5483]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-260091463488589299, -473850267247165966, -114698033405069017, -422315057407041719, 533290881414368934]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39077, -23848, 38674, -30630, -105720]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![39077, -23848, 38674, -30630, -105720]] 
 ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![39077, -23848, 38674, -30630, -105720], ![298680, -182319, 295622, -234142, -808140], ![2283696, -1394112, 2260375, -1790310, -6179232], ![8582232, -5239288, 8494676, -6728163, -23222148], ![-1588996, 970064, -1572792, 1245724, 4299595]]]
  hmulB := by decide  
  f := ![![![-1601, 1704, -2330, 1670, 5952]], ![![-388, 321, -362, 258, 924]], ![![-882, 1152, -1829, 1326, 4728]], ![![-896, 1112, -1260, 845, 2940]], ![![-1634, 1792, -2636, 1912, 6835]]]
  g := ![![![109515, -23848, 38674, -30630, -105720], ![837160, -182319, 295622, -234142, -808140], ![6401154, -1394112, 2260375, -1790310, -6179232], ![24056192, -5239288, 8494676, -6728163, -23222148], ![-4454022, 970064, -1572792, 1245724, 4299595]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![1601, -1704, 2330, -1670, -5952]] ![![39077, -23848, 38674, -30630, -105720]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [1, 7, 3, 10, 7, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 10, 3, 10, 3], [10, 1, 4, 0, 2], [9, 1, 8, 5, 7], [9, 0, 11, 11, 1], [0, 1]]
 g := ![![[9, 2, 4], [6, 1], []], ![[6, 5, 3, 2, 2, 0, 4, 10], [5, 1], [3, 6, 12, 2, 2, 1, 3, 1]], ![[3, 8, 3, 4, 3, 8, 2, 8], [0, 7, 2, 3], [6, 4, 0, 2, 4, 9, 9, 8]], ![[7, 12, 2, 7, 9, 4, 10, 8], [2, 10, 2, 10], [9, 6, 1, 6, 0, 1, 11, 5]], ![[1, 11, 5, 2, 5, 5, 6, 1], [6, 1, 4, 9], [7, 0, 11, 8, 2, 9, 0, 1]]]
 h' := ![![[4, 10, 3, 10, 3], [7, 9, 1, 2], [0, 0, 0, 1], [0, 1]], ![[10, 1, 4, 0, 2], [11, 6, 4, 5, 8], [9, 11, 7, 12], [4, 10, 3, 10, 3]], ![[9, 1, 8, 5, 7], [10, 12, 10, 4, 2], [6, 7, 1, 11, 4], [10, 1, 4, 0, 2]], ![[9, 0, 11, 11, 1], [10, 0, 3, 3, 4], [5, 5, 3, 6, 6], [9, 1, 8, 5, 7]], ![[0, 1], [4, 12, 8, 12, 12], [7, 3, 2, 9, 3], [9, 0, 11, 11, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 1, 7, 2], [], [], []]
 b := ![[], [6, 7, 0, 1, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [1, 7, 3, 10, 7, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![112279166325308229, -68556086061820500, 111149665569784088, -88033394922330806, -303853316521849172]
  a := ![489, -365, 557, -438, -1526]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8636858948100633, -5273545081678500, 8549974274598776, -6771799609410062, -23373332040142244]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 371293 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25845, -9174, 21889, -16031, -56215]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![25845, -9174, 21889, -16031, -56215]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![11, 12, 12, 1, 0], ![14, 10, 11, 0, 1]] where
  M :=![![![25845, -9174, 21889, -16031, -56215], ![69718, -24753, 59053, -43249, -151661], ![187874, -66630, 159068, -116491, -408487], ![218712, -77714, 185350, -135735, -476028], ![-826, 340, -753, 551, 1950]]]
  hmulB := by decide  
  f := ![![![13, -258, 527, -377, -1327]], ![![1150, -805, 787, -563, -2033]], ![![-3310, 3622, -4990, 3571, 12713]], ![![-1457, 1672, -2361, 1690, 6011]], ![![-1558, 1784, -2515, 1800, 6403]]]
  g := ![![![58188, 43844, 48978, -16031, -56215], ![156983, 118285, 132136, -43249, -151661], ![422829, 318596, 355901, -116491, -408487], ![492717, 371258, 414734, -135735, -476028], ![-2011, -1516, -1695, 551, 1950]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [4, 4, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 1, 4], [9, 15, 13], [0, 1]]
 g := ![![[14, 6, 2], [11, 8], [4, 1], []], ![[13, 13, 12, 9], [13, 4], [2, 4], [4, 16]], ![[4, 6, 0, 13], [15, 15], [14, 1], [12, 16]]]
 h' := ![![[12, 1, 4], [8, 3, 11], [1, 14, 12], [0, 0, 1], [0, 1]], ![[9, 15, 13], [7, 16, 7], [5, 5, 15], [9, 12, 15], [12, 1, 4]], ![[0, 1], [7, 15, 16], [13, 15, 7], [16, 5, 1], [9, 15, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 4], []]
 b := ![[], [3, 3, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [4, 4, 13, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2279987226794, 1414538143818, -2288763163058, 1808095784148, 6256253466946]
  a := ![-3687, 2745, -4199, 3287, 11506]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6456269964098, -4873243878554, -5459100041720, 1808095784148, 6256253466946]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-87, 56, -49, 35, 127]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-87, 56, -49, 35, 127]] 
 ![![17, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-87, 56, -49, 35, 127], ![266, -285, 385, -275, -979], ![-242, 464, -758, 539, 1903], ![-672, 396, -384, 287, 1056], ![14, 140, -271, 189, 658]]]
  hmulB := by decide  
  f := ![![![-3247, 1176, -2763, 2029, 7111]], ![![-542, 203, -465, 343, 1201]], ![![-1666, 672, -1456, 1085, 3791]], ![![-2760, 1284, -2508, 1907, 6636]], ![![-538, 140, -427, 301, 1064]]]
  g := ![![![-35, 56, -49, 35, 127], ![246, -285, 385, -275, -979], ![-462, 464, -758, 539, 1903], ![-288, 396, -384, 287, 1056], ![-154, 140, -271, 189, 658]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -10, 16, -12, -42]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![11, -10, 16, -12, -42]] 
 ![![17, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![11, -10, 16, -12, -42], ![60, -33, 50, -40, -138], ![396, -234, 391, -312, -1074], ![1632, -1018, 1646, -1299, -4488], ![-316, 200, -318, 250, 865]]]
  hmulB := by decide  
  f := ![![![115, -30, 88, -64, -222]], ![![98, -33, 82, -60, -210]], ![![10, 30, -25, 20, 78]], ![![310, -226, 378, -283, -1020]], ![![-78, 76, -114, 86, 313]]]
  g := ![![![11, -10, 16, -12, -42], ![38, -33, 50, -40, -138], ![278, -234, 391, -312, -1074], ![1182, -1018, 1646, -1299, -4488], ![-230, 200, -318, 250, 865]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![25845, -9174, 21889, -16031, -56215]] ![![-87, 56, -49, 35, 127]]
  ![![-115, 30, -88, 64, 222]] where
 M := ![![![-115, 30, -88, 64, 222]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-115, 30, -88, 64, 222]] ![![11, -10, 16, -12, -42]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-153, 79, -138, 109, 373]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-153, 79, -138, 109, 373]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![11, 5, 17, 17, 1]] where
  M :=![![![-153, 79, -138, 109, 373], ![-1378, 866, -1418, 1109, 3863], ![-7358, 4081, -6751, 5409, 18433], ![-37260, 23981, -38689, 30357, 105690], ![7930, -5360, 8585, -6691, -23454]]]
  hmulB := by decide  
  f := ![![![-155, 113, -116, 83, 299]], ![![418, -468, 650, -465, -1655]], ![![-370, 723, -1223, 875, 3095]], ![![-804, 455, -331, 237, 870]], ![![-1033, 1011, -1315, 941, 3357]]]
  g := ![![![-224, -94, -341, -328, 373], ![-2309, -971, -3531, -3398, 3863], ![-11059, -4636, -16848, -16208, 18433], ![-63150, -26551, -96601, -92967, 105690], ![13996, 5890, 21437, 20633, -23454]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [11, 15, 14, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 1, 16, 8], [1, 9, 7, 4], [15, 8, 15, 7], [0, 1]]
 g := ![![[5, 4], [16, 14, 8, 1], [1], []], ![[1, 12, 17, 12, 18, 18], [9, 16, 11, 0, 16, 18], [18, 14, 17], [1, 2, 7]], ![[14, 10, 8, 0, 10, 9], [11, 17, 6, 16, 3, 5], [13, 4, 5], [9, 2, 16]], ![[0, 12, 4, 4], [10, 10, 8, 3, 5, 1], [2, 2, 16], [3, 9, 11]]]
 h' := ![![[2, 1, 16, 8], [14, 12, 17], [8, 4, 5, 18], [0, 0, 1], [0, 1]], ![[1, 9, 7, 4], [14, 2, 0, 8], [3, 0, 8, 8], [12, 5, 1, 6], [2, 1, 16, 8]], ![[15, 8, 15, 7], [13, 6, 7, 11], [18, 6, 2, 5], [16, 13, 10, 9], [1, 9, 7, 4]], ![[0, 1], [0, 18, 14], [1, 9, 4, 7], [2, 1, 7, 4], [15, 8, 15, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 7, 5], []]
 b := ![[], [], [3, 14, 17, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [11, 15, 14, 1, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22052552152230954, 16072509925938572, -25527542507493212, 19672606330307117, 69709744358631802]
  a := ![3745, -2764, 4267, -3300, -11687]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-41518933689325304, -17498747993011602, -63715431400222834, -61336476198233343, 69709744358631802]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![155, -113, 116, -83, -299]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![155, -113, 116, -83, -299]] 
 ![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![155, -113, 116, -83, -299], ![-418, 468, -650, 465, 1655], ![370, -723, 1223, -875, -3095], ![804, -455, 331, -237, -870], ![54, -280, 541, -387, -1364]]]
  hmulB := by decide  
  f := ![![![153, -79, 138, -109, -373]], ![![145, -83, 140, -110, -380]], ![![500, -273, 457, -365, -1245]], ![![2106, -1337, 2167, -1701, -5916]], ![![-361, 253, -401, 312, 1097]]]
  g := ![![![165, -113, 116, -83, -299], ![-815, 468, -650, 465, 1655], ![1430, -723, 1223, -875, -3095], ![559, -455, 331, -237, -870], ![606, -280, 541, -387, -1364]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-153, 79, -138, 109, 373]] ![![155, -113, 116, -83, -299]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-89, 9, 239, -182, -640]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-89, 9, 239, -182, -640]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![18, 8, 8, 12, 1]] where
  M :=![![![-89, 9, 239, -182, -640], ![616, -544, 583, -356, -1172], ![9032, -5909, 9524, -7334, -26812], ![-37980, 32363, -48919, 36849, 133866], ![14136, -11412, 17614, -13346, -48565]]]
  hmulB := by decide  
  f := ![![![1039857, -634821, 1029253, -815216, -2813704]], ![![7952176, -4854714, 7871083, -6234262, -21517448]], ![![60813272, -37125819, 60193124, -47675740, -164551996]], ![![228554868, -139530179, 226224163, -179180007, -618436710]], ![![142138318, -86773846, 140688852, -111432082, -384605913]]]
  g := ![![![497, 223, 233, 326, -640], ![944, 384, 433, 596, -1172], ![21376, 9069, 9740, 13670, -26812], ![-106416, -45155, -48689, -68241, 133866], ![38622, 16396, 17658, 24758, -48565]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [19, 22, 17, 7, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 22, 12, 5], [2, 0, 1, 5], [9, 0, 10, 13], [0, 1]]
 g := ![![[7, 12, 13, 9], [13, 1, 6, 12], [16, 1], []], ![[14, 11, 13, 4, 0, 5], [10, 15, 13, 10], [18, 20, 0, 10, 8, 19], [2, 14, 2]], ![[0, 13, 12, 18, 18, 10], [4, 1, 19, 1, 6, 19], [20, 21, 16, 13, 12, 17], [18, 19, 2]], ![[0, 6, 6, 8, 6, 2], [5, 11, 22, 6, 18, 2], [0, 19, 22, 7, 2, 16], [8, 20, 8]]]
 h' := ![![[5, 22, 12, 5], [6, 19, 18, 20], [18, 20, 5, 9], [0, 0, 1], [0, 1]], ![[2, 0, 1, 5], [16, 9, 0, 1], [20, 14, 18], [10, 2, 17, 6], [5, 22, 12, 5]], ![[9, 0, 10, 13], [19, 9, 10, 5], [17, 22, 14, 17], [7, 2, 1, 10], [2, 0, 1, 5]], ![[0, 1], [0, 9, 18, 20], [13, 13, 9, 20], [21, 19, 4, 7], [9, 0, 10, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [9, 6, 10], []]
 b := ![[], [], [7, 20, 22, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [19, 22, 17, 7, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1680939757819373, 1451567075369836, -2266871099793004, 1706406389087160, 6184672323503488]
  a := ![-1624, 1190, -1850, 1414, 5068]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4913262677429659, -2088078761419916, -2249749986426996, -3152593977954552, 6184672323503488]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1039857, 634821, -1029253, 815216, 2813704]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-1039857, 634821, -1029253, 815216, 2813704]] 
 ![![23, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-1039857, 634821, -1029253, 815216, 2813704], ![-7952176, 4854714, -7871083, 6234262, 21517448], ![-60813272, 37125819, -60193124, 47675740, 164551996], ![-228554868, 139530179, -226224163, 179180007, 618436710], ![42318112, -25834732, 41886570, -33176102, -114506745]]]
  hmulB := by decide  
  f := ![![![89, -9, -239, 182, 640]], ![![39, 17, -202, 150, 524]], ![![-354, 253, -518, 398, 1444]], ![![1690, -1411, 2023, -1523, -5542]], ![![-603, 495, -797, 604, 2195]]]
  g := ![![![-788372, 634821, -1029253, 815216, 2813704], ![-6028976, 4854714, -7871083, 6234262, 21517448], ![-46105841, 37125819, -60193124, 47675740, 164551996], ![-173279847, 139530179, -226224163, 179180007, 618436710], ![32083657, -25834732, 41886570, -33176102, -114506745]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-89, 9, 239, -182, -640]] ![![-1039857, 634821, -1029253, 815216, 2813704]]
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


lemma PB2201I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB2201I0 : PrimesBelowBoundCertificateInterval O 1 23 2201 where
  m := 9
  g := ![5, 5, 5, 2, 2, 1, 3, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB2201I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
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
    · exact ![371293]
    · exact ![4913, 17, 17]
    · exact ![130321, 19]
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
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
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
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I11N1, I17N1, I17N2, I19N1, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N1], [], [I17N1, I17N2], [I19N1], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
