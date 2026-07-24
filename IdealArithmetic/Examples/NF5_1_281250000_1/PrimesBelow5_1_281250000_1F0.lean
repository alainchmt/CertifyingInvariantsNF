
import IdealArithmetic.Examples.NF5_1_281250000_1.RI5_1_281250000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1580818, 836159, 171847, -270352, -170245]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-1580818, 836159, 171847, -270352, -170245]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-1580818, 836159, 171847, -270352, -170245], ![-5107350, 2675307, 565807, -843215, -540704], ![-16221120, 8410250, 1832092, -2578005, -1686430], ![-10118580, 5187926, 1166449, -1540768, -1031202], ![-7357470, 3625610, 907533, -950885, -697553]]]
  hmulB := by decide  
  f := ![![![123776041, -21550165, -11077122, 4746951, 6258641]], ![![93879615, -16344992, -8401607, 3600400, 4746951]], ![![142408530, -24794160, -12744592, 5461475, 7200800]], ![![43204800, -7522294, -3866537, 1657008, 2184590]], ![![-38435415, 6692105, 3439653, -1474130, -1943392]]]
  g := ![![![-790409, 836159, 171847, -270352, -170245], ![-2553675, 2675307, 565807, -843215, -540704], ![-8110560, 8410250, 1832092, -2578005, -1686430], ![-5059290, 5187926, 1166449, -1540768, -1031202], ![-3678735, 3625610, 907533, -950885, -697553]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-368056397, 64080038, 32938770, -14115143, -18610683]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-368056397, 64080038, 32938770, -14115143, -18610683]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-368056397, 64080038, 32938770, -14115143, -18610683], ![-558320490, 97210678, 49964895, -21412980, -28230286], ![-846908580, 147436660, 75797698, -32478385, -42825960], ![-256955760, 44748084, 22991655, -9854222, -12991354], ![228583980, -39804285, -20451918, 8761560, 11558758]]]
  hmulB := by decide  
  f := ![![![-19446616, -1853521, 7029054, 10699969, 2231454]], ![![33471810, -37616483, 4423224, 28729905, 10699969]], ![![320999070, -234027415, -8886578, 129115810, 57459810]], ![![344758860, -223099236, -20982321, 106033042, 51646324]], ![![604472017, -357112673, -50575281, 146567897, 78418864]]]
  g := ![![![-174722857, 64080038, 32938770, -14115143, -18610683], ![-265045102, 97210678, 49964895, -21412980, -28230286], ![-402041310, 147436660, 75797698, -32478385, -42825960], ![-121982203, 44748084, 22991655, -9854222, -12991354], ![108512611, -39804285, -20451918, 8761560, 11558758]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4194347, 730261, 375366, -160858, -212084]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-4194347, 730261, 375366, -160858, -212084]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-4194347, 730261, 375366, -160858, -212084], ![-6362520, 1107753, 569403, -244010, -321716], ![-9651480, 1680380, 863743, -370145, -488020], ![-2928120, 509804, 262047, -112297, -148058], ![2604870, -453525, -233118, 99900, 131713]]]
  hmulB := by decide  
  f := ![![![-1426, 700, 177, -181, -134]], ![![-2723, 1312, 348, -318, -248]], ![![-6143, 2865, 823, -603, -522]], ![![-3443, 1539, 489, -266, -272]], ![![-1073, 290, 228, 142, -15]]]
  g := ![![![-2463516, 730261, 375366, -160858, -212084], ![-3736975, 1107753, 569403, -244010, -321716], ![-5668719, 1680380, 863743, -370145, -488020], ![-1719808, 509804, 262047, -112297, -148058], ![1529950, -453525, -233118, 99900, 131713]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-1580818, 836159, 171847, -270352, -170245]] ![![-368056397, 64080038, 32938770, -14115143, -18610683]]
  ![![-4, -5, 1, 3, -2]] where
 M := ![![![-4, -5, 1, 3, -2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-4, -5, 1, 3, -2]] ![![-368056397, 64080038, 32938770, -14115143, -18610683]]
  ![![2188884218, -381084060, -195903056, 83961301, 110676624]] where
 M := ![![![2188884218, -381084060, -195903056, 83961301, 110676624]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2188884218, -381084060, -195903056, 83961301, 110676624]] ![![-4194347, 730261, 375366, -160858, -212084]]
  ![![-4823081119886806, 839727381157842, 431633506868515, -184970686876121, -243875463780778]] where
 M := ![![![-4823081119886806, 839727381157842, 431633506868515, -184970686876121, -243875463780778]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-4823081119886806, 839727381157842, 431633506868515, -184970686876121, -243875463780778]] ![![-4194347, 730261, 375366, -160858, -212084]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![10627343898235209285302, -1850284380099217299474, -951076210729059834908, 407570814499008366190, 537363639048071486836]]]
 hmul := by decide  
 g := ![![![![5313671949117604642651, -925142190049608649737, -475538105364529917454, 203785407249504183095, 268681819524035743418]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1319, -99181, 40582, 115171, 35448]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-1319, -99181, 40582, 115171, 35448]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 2, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-1319, -99181, 40582, 115171, 35448], ![1063440, -887519, 15990, 557390, 230342], ![6910260, -4695110, -330129, 2383370, 1114780], ![6688680, -4191848, -462348, 1899431, 953348], ![10845090, -6224955, -981144, 2419185, 1342041]]]
  hmulB := by decide  
  f := ![![![-2913074465817, 507183754829, 260700684108, -111719743343, -147297416058]], ![![-4418922481740, 769360935633, 395464011486, -169470740040, -223439486686]], ![![-3205419688799, 558082813413, 286863626567, -122931517591, -162079632046]], ![![-3623831281320, 630930783850, 324308666056, -138978081549, -183236299048]], ![![603047814570, -104994245265, -53968746646, 23127574615, 30492658491]]]
  g := ![![![-13967, -109841, 40582, 115171, 35448], ![349150, -667433, 15990, 557390, 230342], ![2413463, -3153950, -330129, 2383370, 1114780], ![2383676, -2663570, -462348, 1899431, 953348], ![3942078, -3687775, -981144, 2419185, 1342041]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [1, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 2], [0, 1]]
 g := ![![[0, 1]], ![[0, 2]]]
 h' := ![![[0, 2], [0, 1]], ![[0, 1], [0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [0, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [1, 0, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1861, 487, -1097, 905, 1079]
  a := ![0, -1, -3, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![986, -441, -1097, 905, 1079]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, -1, -1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, -1, -1, 0]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 0, -1, -1, 0], ![0, 3, -1, -5, -2], ![-60, 50, -2, -25, -10], ![-60, 38, 5, -22, -10], ![-120, 70, 9, -25, -17]]]
  hmulB := by decide  
  f := ![![![6961, -1212, -623, 267, 352]], ![![3520, -613, -315, 135, 178]], ![![5340, -930, -478, 205, 270]], ![![1620, -282, -145, 62, 82]], ![![-1440, 250, 129, -55, -73]]]
  g := ![![![1, 0, -1, -1, 0], ![0, 3, -1, -5, -2], ![-20, 50, -2, -25, -10], ![-20, 38, 5, -22, -10], ![-40, 70, 9, -25, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-1319, -99181, 40582, 115171, 35448]] ![![-1319, -99181, 40582, 115171, 35448]]
  ![![1329739583041, -805822643190, -103065400946, 345802150782, 179718408022]] where
 M := ![![![1329739583041, -805822643190, -103065400946, 345802150782, 179718408022]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![1329739583041, -805822643190, -103065400946, 345802150782, 179718408022]] ![![3, 0, -1, -1, 0]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-32141195203677, 18150032314386, 3028690288149, -6824598861195, -3870935148354]]]
 hmul := by decide  
 g := ![![![![-10713731734559, 6050010771462, 1009563429383, -2274866287065, -1290311716118]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, 7, 3, -2, -2]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-35, 7, 3, -2, -2]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-35, 7, 3, -2, -2], ![-60, 15, 5, -5, -4], ![-120, 40, 10, -15, -10], ![-60, 26, 5, -10, -6], ![-30, 25, 3, -10, -5]]]
  hmulB := by decide  
  f := ![![![5, -5, 1, 0, 0]], ![![0, 1, -1, 1, 0]], ![![0, 0, 2, -5, 2]], ![![12, -10, -1, 6, -2]], ![![-30, 31, -3, -10, 5]]]
  g := ![![![-7, 7, 3, -2, -2], ![-12, 15, 5, -5, -4], ![-24, 40, 10, -15, -10], ![-12, 26, 5, -10, -6], ![-6, 25, 3, -10, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-35, 7, 3, -2, -2]] ![![-35, 7, 3, -2, -2]]
  ![![625, -122, -56, 30, 34]] where
 M := ![![![625, -122, -56, 30, 34]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![625, -122, -56, 30, 34]] ![![-35, 7, 3, -2, -2]]
  ![![-10655, 1935, 957, -440, -552]] where
 M := ![![![-10655, 1935, 957, -440, -552]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-10655, 1935, 957, -440, -552]] ![![-35, 7, 3, -2, -2]]
  ![![184945, -32520, -16576, 7200, 9400]] where
 M := ![![![184945, -32520, -16576, 7200, 9400]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![184945, -32520, -16576, 7200, 9400]] ![![-35, 7, 3, -2, -2]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-3246755, 565975, 290675, -124650, -164250]]]
 hmul := by decide  
 g := ![![![![-649351, 113195, 58135, -24930, -32850]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -11, 0, 5, -2]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![13, -11, 0, 5, -2]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![1, 3, 3, 1, 0], ![3, 6, 4, 0, 1]] where
  M :=![![![13, -11, 0, 5, -2], ![-60, 63, -6, -20, 10], ![300, -310, 43, 70, -40], ![-240, 260, -48, -37, 28], ![270, -315, 90, -15, -17]]]
  hmulB := by decide  
  f := ![![![-41, 23, 6, -5, -4]], ![![-120, 59, 18, -10, -10]], ![![-300, 130, 49, -10, -20]], ![![-203, 90, 33, -8, -14]], ![![-279, 124, 46, -10, -19]]]
  g := ![![![2, -2, -1, 5, -2], ![-10, 9, 2, -20, 10], ![50, -40, -1, 70, -40], ![-41, 29, -7, -37, 28], ![48, -24, 29, -15, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 3, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 1, 6], [5, 5, 1], [0, 1]]
 g := ![![[3, 2, 1], [1]], ![[5, 6, 0, 6], [1, 4, 2, 6]], ![[2, 0, 5, 4], [2, 5, 2, 1]]]
 h' := ![![[3, 1, 6], [1, 4, 1], [0, 1]], ![[5, 5, 1], [0, 0, 1], [3, 1, 6]], ![[0, 1], [1, 3, 5], [5, 5, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 6], []]
 b := ![[], [4, 5, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 3, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3308394, 4096611, -697564, -1990411, 1031174]
  a := ![3, -64, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-630215, 554400, 164139, -1990411, 1031174]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, 23, 6, -5, -4]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-41, 23, 6, -5, -4]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![3, 6, 1, 0, 0], ![2, 6, 0, 1, 0], ![0, 1, 0, 0, 1]] where
  M :=![![![-41, 23, 6, -5, -4], ![-120, 59, 18, -10, -10], ![-300, 130, 49, -10, -20], ![-120, 40, 24, 9, -4], ![90, -75, 0, 45, 19]]]
  hmulB := by decide  
  f := ![![![13, -11, 0, 5, -2]], ![![-60, 63, -6, -20, 10]], ![![-3, 5, 1, -5, 2]], ![![-82, 88, -12, -21, 12]], ![![30, -36, 12, -5, -1]]]
  g := ![![![-7, 3, 6, -5, -4], ![-22, 3, 18, -10, -10], ![-61, -12, 49, -10, -20], ![-30, -22, 24, 9, -4], ![0, -52, 0, 45, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [3, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 6], [0, 1]]
 g := ![![[4, 1], [2, 1]], ![[6, 6], [4, 6]]]
 h' := ![![[2, 6], [1, 1], [0, 1]], ![[0, 1], [3, 6], [2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [5, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [3, 5, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![969, -509, -148, 353, 158]
  a := ![1, -3, -1, -1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![101, -271, -148, 353, 158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![13, -11, 0, 5, -2]] ![![-41, 23, 6, -5, -4]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [3, 5, 10, 5, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6, 3, 4, 10], [10, 4, 2, 7, 9], [5, 2, 4, 6, 1], [3, 9, 2, 5, 2], [0, 1]]
 g := ![![[0, 1, 0, 9, 5], [1], []], ![[4, 3, 3, 0, 2, 8, 10, 7], [0, 6, 9, 2, 4, 2, 9, 10], [4, 9, 10, 1]], ![[9, 4, 9, 0, 9, 6, 7, 1], [6, 10, 8, 7, 8, 0, 2, 3], [9, 10, 0, 4]], ![[10, 6, 3, 3, 4, 8, 8, 5], [1, 5, 10, 10, 3, 9, 1, 1], [7, 7, 8, 1]], ![[0, 7, 8, 9, 10, 3, 2, 8], [5, 1, 2, 4, 8, 7, 8, 10], [8, 8, 4, 4]]]
 h' := ![![[0, 6, 3, 4, 10], [8, 6, 1, 6, 7], [0, 0, 1], [0, 1]], ![[10, 4, 2, 7, 9], [0, 10, 4, 0, 9], [10, 8, 9, 5, 1], [0, 6, 3, 4, 10]], ![[5, 2, 4, 6, 1], [10, 0, 9, 7, 4], [7, 5, 4, 10, 2], [10, 4, 2, 7, 9]], ![[3, 9, 2, 5, 2], [0, 2, 6, 8, 4], [4, 8, 3, 5, 1], [5, 2, 4, 6, 1]], ![[0, 1], [0, 4, 2, 1, 9], [7, 1, 5, 2, 7], [3, 9, 2, 5, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 2, 0, 7], [], [], []]
 b := ![[], [8, 5, 7, 1, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [3, 5, 10, 5, 4, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13079743468, 40941964547, -24520926452, -3569617601, 26115049279]
  a := ![1, 19, 4, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1189067588, 3721996777, -2229175132, -324510691, 2374095389]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 161051 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, -125, 3, 46, -38]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![127, -125, 3, 46, -38]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![4, 9, 7, 1, 0], ![8, 7, 6, 0, 1]] where
  M :=![![![127, -125, 3, 46, -38], ![-1140, 1077, -79, -365, 92], ![2760, -3440, 712, 525, -730], ![-4380, 4202, -583, -748, 210], ![1770, -3095, 1371, -670, -383]]]
  hmulB := by decide  
  f := ![![![680950399, -118557553, -60940507, 26115228, 34431744]], ![![1032952320, -179843201, -92442325, 39614905, 52230456]], ![![1566913680, -272809080, -140228296, 60092935, 79229810]], ![![1804934392, -314249915, -161529558, 69221302, 91265148]], ![![1665911714, -290045232, -149087958, 63889623, 84235571]]]
  g := ![![![19, -21, -7, 46, -38], ![-32, 286, 148, -365, 92], ![500, -235, 109, 525, -730], ![-236, 728, 261, -748, 210], ![578, 432, 643, -670, -383]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [11, 3, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 11, 10], [9, 1, 3], [0, 1]]
 g := ![![[5, 0, 3], [11, 10], [1]], ![[4, 3, 7, 10], [7, 4], [0, 7, 5, 12]], ![[7, 0, 6, 10], [8, 12], [5, 5, 7, 1]]]
 h' := ![![[10, 11, 10], [0, 1, 4], [2, 10, 6], [0, 1]], ![[9, 1, 3], [2, 2, 1], [12, 12, 2], [10, 11, 10]], ![[0, 1], [7, 10, 8], [11, 4, 5], [9, 1, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 12], []]
 b := ![[], [12, 7, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [11, 3, 7, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2431936, 1538942, 587254, -1537096, 291019]
  a := ![-1, 0, -4, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![106792, 1025821, 738524, -1537096, 291019]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![680950399, -118557553, -60940507, 26115228, 34431744]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![680950399, -118557553, -60940507, 26115228, 34431744]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![11, 4, 1, 0, 0], ![12, 12, 0, 1, 0], ![0, 6, 0, 0, 1]] where
  M :=![![![680950399, -118557553, -60940507, 26115228, 34431744], ![1032952320, -179843201, -92442325, 39614905, 52230456], ![1566913680, -272809080, -140228296, 60092935, 79229810], ![475378860, -82766314, -42543229, 18231324, 24037174], ![-422899230, 73629295, 37846653, -16218670, -21383581]]]
  hmulB := by decide  
  f := ![![![127, -125, 3, 46, -38]], ![![-1140, 1077, -79, -365, 92]], ![![-31, -39, 33, -33, -60]], ![![-1272, 1202, -115, -352, 66]], ![![-390, 259, 69, -220, 13]]]
  g := ![![![79839480, -30366825, -60940507, 26115228, 34431744], ![121110695, -46064269, -92442325, 39614905, 52230456], ![183716132, -69876152, -140228296, 60092935, 79229810], ![55736807, -21199410, -42543229, 18231324, 24037174], ![-49583721, 18859093, 37846653, -16218670, -21383581]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [10, 3, 1] where
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
 g := ![![[12, 4], [1], [10, 1]], ![[0, 9], [1], [7, 12]]]
 h' := ![![[10, 12], [6, 2], [4, 12], [0, 1]], ![[0, 1], [0, 11], [7, 1], [10, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [11, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [10, 3, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19190, 20260, -2928, -4490, 2678]
  a := ![0, 0, 4, -10, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5146, 5368, -2928, -4490, 2678]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![127, -125, 3, 46, -38]] ![![680950399, -118557553, -60940507, 26115228, 34431744]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![50233373, -25406700, -5931938, 7246338, 4995154]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![50233373, -25406700, -5931938, 7246338, 4995154]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![16, 5, 1, 1, 0], ![11, 4, 9, 0, 1]] where
  M :=![![![50233373, -25406700, -5931938, 7246338, 4995154], ![149854620, -74645477, -18160362, 20291850, 14492676], ![434780280, -212462280, -54353627, 54124950, 40583700], ![243502200, -115962444, -31667466, 26813773, 21649980], ![107359560, -42642510, -17397522, 2018760, 6521923]]]
  hmulB := by decide  
  f := ![![![3168037909, -551574432, -283518214, 121497906, 160189442]], ![![4805683260, -836698141, -430076526, 184303350, 242995812]], ![![7289874360, -1269212040, -652394791, 279575490, 368606700]], ![![4954031612, -862526605, -443352715, 189992785, 250496884]], ![![6924266767, -1205557118, -619675423, 265553808, 350120157]]]
  g := ![![![-7097337, -4801118, -3419686, 7246338, 4995154], ![-19660848, -13769143, -9934488, 20291850, 14492676], ![-51625860, -37965990, -27866581, 54124950, 40583700], ![-24921644, -19801837, -14901827, 26813773, 21649980], ![195191, -4636706, -4594917, 2018760, 6521923]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [1, 1, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 15, 2], [16, 1, 15], [0, 1]]
 g := ![![[2, 1, 13], [10, 13], [14, 1], []], ![[16, 15, 8, 15], [0, 8], [11, 1], [14, 4]], ![[2, 13, 4, 2], [8, 9], [16, 4], [1, 4]]]
 h' := ![![[15, 15, 2], [16, 6, 9], [3, 2, 8], [0, 0, 1], [0, 1]], ![[16, 1, 15], [16, 0, 4], [4, 1, 12], [7, 7, 1], [15, 15, 2]], ![[0, 1], [10, 11, 4], [1, 14, 14], [0, 10, 15], [16, 1, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 5], []]
 b := ![[], [13, 5, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [1, 1, 3, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1470402, 1153223, 136653, -688859, 179249]
  a := ![13, -1, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![445859, 228266, -46337, -688859, 179249]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3168037909, 551574432, 283518214, -121497906, -160189442]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-3168037909, 551574432, 283518214, -121497906, -160189442]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![9, 12, 1, 0, 0], ![9, 7, 0, 1, 0], ![15, 16, 0, 0, 1]] where
  M :=![![![-3168037909, 551574432, 283518214, -121497906, -160189442], ![-4805683260, 836698141, 430076526, -184303350, -242995812], ![-7289874360, 1269212040, 652394791, -279575490, -368606700], ![-2211640200, 385058628, 197927310, -84818609, -111830196], ![1967484240, -342548670, -176077386, 75455040, 99484741]]]
  hmulB := by decide  
  f := ![![![-50233373, 25406700, 5931938, -7246338, -4995154]], ![![-149854620, 74645477, 18160362, -20291850, -14492676]], ![![-157949181, 78639312, 19156789, -21343776, -15261894]], ![![-102622641, 51008299, 12481026, -13769045, -9885594]], ![![-191678475, 95180626, 23349552, -25610790, -18431297]]]
  g := ![![![-130787003, 33110134, 283518214, -121497906, -160189442], ![-198394392, 50225663, 430076526, -184303350, -242995812], ![-300949857, 76188834, 652394791, -279575490, -368606700], ![-91303857, 23114371, 197927310, -84818609, -111830196], ![81224367, -20562422, -176077386, 75455040, 99484741]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [2, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 16], [0, 1]]
 g := ![![[5, 9], [13], [15], [1]], ![[0, 8], [13], [15], [1]]]
 h' := ![![[7, 16], [4, 14], [8, 9], [15, 7], [0, 1]], ![[0, 1], [0, 3], [3, 8], [13, 10], [7, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [1, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [2, 10, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10039, 13737, -2999, -2129, 3457]
  a := ![3, 0, 7, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-926, 548, -2999, -2129, 3457]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![50233373, -25406700, -5931938, 7246338, 4995154]] ![![-3168037909, 551574432, 283518214, -121497906, -160189442]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![589, -165, -49, 64, 8]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![589, -165, -49, 64, 8]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![11, 1, 7, 1, 0], ![7, 7, 2, 0, 1]] where
  M :=![![![589, -165, -49, 64, 8], ![240, 389, -101, -165, 128], ![3840, -2960, 224, 775, -330], ![-1980, 2418, -437, -436, 310], ![2730, -3385, 879, 70, -271]]]
  hmulB := by decide  
  f := ![![![5731, -3303, -513, 1294, 714]], ![![21420, -12119, -2009, 4575, 2588]], ![![77640, -43280, -7544, 15835, 9150]], ![![35939, -20086, -3471, 7390, 4254]], ![![21133, -11821, -2037, 4357, 2505]]]
  g := ![![![-9, -15, -27, 64, 8], ![61, -18, 42, -165, 128], ![-125, -75, -239, 775, -330], ![34, 36, 105, -436, 310], ![203, -82, 49, 70, -271]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [15, 13, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 16, 2], [11, 2, 17], [0, 1]]
 g := ![![[3, 12, 4], [2, 14, 9], [4, 1], []], ![[7, 1, 7, 8], [10, 10, 2, 12], [2, 4], [4, 4]], ![[8, 12, 3, 6], [3, 10, 15, 5], [15, 9], [8, 4]]]
 h' := ![![[12, 16, 2], [8, 1, 17], [16, 9, 3], [0, 0, 1], [0, 1]], ![[11, 2, 17], [4, 4, 17], [15, 10, 5], [8, 6, 2], [12, 16, 2]], ![[0, 1], [17, 14, 4], [4, 0, 11], [1, 13, 16], [11, 2, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 12], []]
 b := ![[], [2, 2, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [15, 13, 15, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![478844, -300983, -98162, 261479, -34331]
  a := ![1, 1, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-113532, -16955, -97887, 261479, -34331]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, 14, 7, -3, -4]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-79, 14, 7, -3, -4]] 
 ![![19, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-79, 14, 7, -3, -4], ![-120, 21, 11, -5, -6], ![-180, 30, 16, -5, -10], ![-60, 14, 5, -4, -2], ![60, -20, -3, 5, 1]]]
  hmulB := by decide  
  f := ![![![-61, 26, 9, -3, -4]], ![![-32, 13, 5, -1, -2]], ![![-48, 18, 8, 1, -2]], ![![-45, 16, 8, 1, -2]], ![![-10, 0, 3, 5, 1]]]
  g := ![![![-10, 14, 7, -3, -4], ![-15, 21, 11, -5, -6], ![-23, 30, 16, -5, -10], ![-8, 14, 5, -4, -2], ![9, -20, -3, 5, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27191, 15375, 2554, -5797, -3282]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-27191, 15375, 2554, -5797, -3282]] 
 ![![19, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-27191, 15375, 2554, -5797, -3282], ![-98460, 54859, 9578, -20050, -11594], ![-347820, 191390, 34809, -68050, -40100], ![-240600, 130936, 24668, -45391, -27220], ![-234390, 124255, 25368, -40405, -25341]]]
  hmulB := by decide  
  f := ![![![21271, -4047, -1820, 913, 996]], ![![17246, -3173, -1506, 718, 830]], ![![17437, -3599, -1391, 761, 772]], ![![15097, -2645, -1384, 660, 736]], ![![7213, -1486, -518, 194, 357]]]
  g := ![![![-9332, 15375, 2554, -5797, -3282], ![-34168, 54859, 9578, -20050, -11594], ![-121813, 191390, 34809, -68050, -40100], ![-84935, 130936, 24668, -45391, -27220], ![-84268, 124255, 25368, -40405, -25341]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![589, -165, -49, 64, 8]] ![![-79, 14, 7, -3, -4]]
  ![![-21271, 4047, 1820, -913, -996]] where
 M := ![![![-21271, 4047, 1820, -913, -996]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![-21271, 4047, 1820, -913, -996]] ![![-27191, 15375, 2554, -5797, -3282]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4919, 1866, 849, -209, -452]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-4919, 1866, 849, -209, -452]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![9, 9, 17, 17, 1]] where
  M :=![![![-4919, 1866, 849, -209, -452], ![-13560, 6381, 1657, -275, -418], ![-12540, -3110, 6106, 4105, -550], ![-3300, 242, 199, 5006, 1642], ![30900, -20620, -429, 6655, 5281]]]
  hmulB := by decide  
  f := ![![![62172582383, -10824619882, -5564030357, 2384389767, 3143709796]], ![![94311293880, -16420162517, -8440230115, 3616946175, 4768779534]], ![![143063386020, -24908194470, -12803216342, 5486644765, 7233892350]], ![![43403354100, -7556784546, -3884309941, 1664568358, 2194657906]], ![![197377288869, -34364571061, -17663947434, 7569645168, 9980233935]]]
  g := ![![![-37, 258, 371, 325, -452], ![-426, 441, 381, 297, -418], ![-330, 80, 672, 585, -550], ![-786, -632, -1205, -996, 1642], ![-723, -2963, -3922, -3614, 5281]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [8, 7, 7, 13, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 20, 12, 3], [0, 11, 18, 10], [1, 14, 16, 10], [0, 1]]
 g := ![![[19, 2], [16, 2, 17, 1], [10, 1], []], ![[3, 1, 5, 5, 20, 8], [11, 11, 6, 16, 9, 18], [11, 1, 16, 2, 17, 12], [4, 1, 9]], ![[20, 9, 10, 14, 5, 5], [7, 1, 16, 15, 4, 10], [12, 19, 20, 19, 1, 17], [12, 3, 8]], ![[3, 15, 19, 6, 3, 10], [5, 14, 9, 19, 1, 14], [7, 11, 19, 17], [18, 9, 8]]]
 h' := ![![[9, 20, 12, 3], [10, 16, 5], [12, 14, 15, 1], [0, 0, 1], [0, 1]], ![[0, 11, 18, 10], [8, 8, 0, 15], [16, 19, 12, 11], [3, 2, 3, 21], [9, 20, 12, 3]], ![[1, 14, 16, 10], [13, 4, 2, 9], [19, 9, 8, 22], [19, 7, 21, 2], [0, 11, 18, 10]], ![[0, 1], [1, 18, 16, 22], [15, 4, 11, 12], [18, 14, 21], [1, 14, 16, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 11, 22], []]
 b := ![[], [], [19, 12, 6, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [8, 7, 7, 13, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1335126, -1387752, 181486, 337978, -188342]
  a := ![4, 0, -1, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![131748, 13362, 147100, 153904, -188342]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-62172582383, 10824619882, 5564030357, -2384389767, -3143709796]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-62172582383, 10824619882, 5564030357, -2384389767, -3143709796]] 
 ![![23, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-62172582383, 10824619882, 5564030357, -2384389767, -3143709796], ![-94311293880, 16420162517, 8440230115, -3616946175, -4768779534], ![-143063386020, 24908194470, 12803216342, -5486644765, -7233892350], ![-43403354100, 7556784546, 3884309941, -1664568358, -2194657906], ![38611824420, -6722550460, -3455500077, 1480807705, 1952377817]]]
  hmulB := by decide  
  f := ![![![4919, -1866, -849, 209, 452]], ![![3156, -1251, -515, 121, 254]], ![![4181, -1244, -893, -24, 358]], ![![4207, -1552, -710, -45, 302]], ![![-488, 572, -129, -253, -151]]]
  g := ![![![-9946882273, 10824619882, 5564030357, -2384389767, -3143709796], ![-15088698286, 16420162517, 8440230115, -3616946175, -4768779534], ![-22888459893, 24908194470, 12803216342, -5486644765, -7233892350], ![-6944026401, 7556784546, 3884309941, -1664568358, -2194657906], ![6177437982, -6722550460, -3455500077, 1480807705, 1952377817]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-4919, 1866, 849, -209, -452]] ![![-62172582383, 10824619882, 5564030357, -2384389767, -3143709796]]
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


lemma PB1045I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1045I0 : PrimesBelowBoundCertificateInterval O 1 23 1045 where
  m := 9
  g := ![5, 3, 5, 2, 1, 2, 2, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1045I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
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
    · exact ![9, 9, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![343, 49]
    · exact ![161051]
    · exact ![2197, 169]
    · exact ![4913, 289]
    · exact ![6859, 19, 19]
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
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N0, I7N1, I13N1, I17N1, I19N1, I19N2, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1], [], [I13N1], [I17N1], [I19N1, I19N2], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
