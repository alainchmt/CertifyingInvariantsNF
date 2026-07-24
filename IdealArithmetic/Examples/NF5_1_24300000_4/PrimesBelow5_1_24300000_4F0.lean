
import IdealArithmetic.Examples.NF5_1_24300000_4.RI5_1_24300000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![185, 174, 117, 147, 108]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![185, 174, 117, 147, 108]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![185, 174, 117, 147, 108], ![432, 557, 390, 450, 294], ![1176, 1566, 1145, 1368, 900], ![1584, 2016, 1488, 1820, 1221], ![2226, 2778, 2034, 2484, 1673]]]
  hmulB := by decide  
  f := ![![![-1148, 318, -486, -591, 711]], ![![1422, -757, 870, 225, -591]], ![![-2364, 1926, -1939, 558, 450]], ![![-385, -1110, 735, -1897, 1209]], ![![996, 588, -216, 1719, -1306]]]
  g := ![![![19, 174, 117, 147, 108], ![-9, 557, 390, 450, 294], ![-96, 1566, 1145, 1368, 900], ![-118, 2016, 1488, 1820, 1221], ![-129, 2778, 2034, 2484, 1673]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -2, 2, -1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, -2, 2, -1, 0]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, -2, 2, -1, 0], ![0, 3, -2, 4, -2], ![-8, 0, -1, -8, 8], ![16, -6, 9, 5, -7], ![-14, 10, -9, 0, 6]]]
  hmulB := by decide  
  f := ![![![-22, 6, 7, 2, -5]], ![![-10, -9, -2, 2, 2]], ![![8, -8, -5, 0, 4]], ![![13, 8, 1, -2, -1]], ![![3, 10, 4, -1, -3]]]
  g := ![![![1, -2, 2, -1, 0], ![0, 3, -2, 4, -2], ![-4, 0, -1, -8, 8], ![8, -6, 9, 5, -7], ![-7, 10, -9, 0, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -1, 0, 0, 0]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![3, -1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![3, -1, 0, 0, 0], ![0, 3, -1, 0, 0], ![0, -1, 3, -2, 0], ![0, -1, 0, 3, -2], ![-4, -1, -2, -2, 3]]]
  hmulB := by decide  
  f := ![![![6, 7, 5, 6, 4]], ![![11, 14, 10, 12, 8]], ![![27, 34, 25, 30, 20]], ![![35, 44, 32, 39, 26]], ![![47, 59, 43, 52, 35]]]
  g := ![![![2, -1, 0, 0, 0], ![-1, 3, -1, 0, 0], ![0, -1, 3, -2, 0], ![0, -1, 0, 3, -2], ![-1, -1, -2, -2, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![185, 174, 117, 147, 108]] ![![2, -2, 2, -1, 0]]
  ![![274, 350, 256, 310, 207]] where
 M := ![![![274, 350, 256, 310, 207]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![274, 350, 256, 310, 207]] ![![2, -2, 2, -1, 0]]
  ![![562, 712, 519, 628, 420]] where
 M := ![![![562, 712, 519, 628, 420]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![562, 712, 519, 628, 420]] ![![3, -1, 0, 0, 0]]
  ![![6, 7, 5, 6, 4]] where
 M := ![![![6, 7, 5, 6, 4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![6, 7, 5, 6, 4]] ![![3, -1, 0, 0, 0]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![2, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -25, -18, -22, -15]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-21, -25, -18, -22, -15]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 1, 0, 1, 0], ![1, 2, 0, 0, 1]] where
  M :=![![![-21, -25, -18, -22, -15], ![-60, -76, -55, -66, -44], ![-176, -225, -164, -198, -132], ![-234, -297, -217, -263, -176], ![-322, -407, -297, -360, -241]]]
  hmulB := by decide  
  f := ![![![7, -3, 4, 4, -5]], ![![-20, 10, -13, -2, 8]], ![![13, -10, 10, -2, -3]], ![![-6, 9, -8, 7, -2]], ![![-17, 4, -7, -8, 10]]]
  g := ![![![4, 9, -18, -22, -15], ![13, 26, -55, -66, -44], ![40, 79, -164, -198, -132], ![53, 106, -217, -263, -176], ![72, 145, -297, -360, -241]]]
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
  c := ![-10652, 36828, -1143, 14461, 25261]
  a := ![3, -61, 2, -65, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11590, -9385, -1143, 14461, 25261]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1381, 1698, -951, 3616, -2515]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![1381, 1698, -951, 3616, -2515]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![1381, 1698, -951, 3616, -2515], ![-10060, 1531, -3332, -6932, 7232], ![28928, -13092, 15995, 7800, -13864], ![-22698, 18664, -18744, 5597, 4184], ![13398, -16596, 15182, -11094, 1981]]]
  hmulB := by decide  
  f := ![![![-911, -254, 135, 290, 103]], ![![-470, -297, 74, 352, 262]], ![![166, 304, 349, 548, 386]], ![![566, 916, 562, 497, 258]], ![![-160, 836, 814, 934, 469]]]
  g := ![![![1639, 1698, -951, 3616, -2515], ![-6974, 1531, -3332, -6932, 7232], ![16950, -13092, 15995, 7800, -13864], ![-10302, 18664, -18744, 5597, 4184], ![4088, -16596, 15182, -11094, 1981]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-21, -25, -18, -22, -15]] ![![1381, 1698, -951, 3616, -2515]]
  ![![181, 55, -1, 240, -196]] where
 M := ![![![181, 55, -1, 240, -196]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![181, 55, -1, 240, -196]] ![![1381, 1698, -951, 3616, -2515]]
  ![![-8405795, 8136811, -7845618, 3783140, 572293]] where
 M := ![![![-8405795, 8136811, -7845618, 3783140, 572293]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-8405795, 8136811, -7845618, 3783140, 572293]] ![![1381, 1698, -951, 3616, -2515]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-398624889165, 162009998919, -206831226951, -133170332934, 205720009722]]]
 hmul := by decide  
 g := ![![![![-132874963055, 54003332973, -68943742317, -44390110978, 68573336574]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8495, -10567, -7676, -9312, -6261]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-8495, -10567, -7676, -9312, -6261]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-8495, -10567, -7676, -9312, -6261], ![-25044, -31744, -23089, -27874, -18624], ![-74496, -94631, -68992, -83426, -55748], ![-98974, -125459, -91519, -110803, -74114], ![-135706, -171833, -125299, -151696, -101491]]]
  hmulB := by decide  
  f := ![![![2659, 18621, -13162, 28398, -17089]], ![![-11544, 15058, -13641, 10618, -2312]], ![![47564, -2627, 12350, 39214, -37872]], ![![-41566, 30225, -31407, 4729, 10816]], ![![30063, -17622, 19587, 2498, -11204]]]
  g := ![![![16652, -10567, -7676, -9312, -6261], ![50032, -31744, -23089, -27874, -18624], ![149448, -94631, -68992, -83426, -55748], ![198256, -125459, -91519, -110803, -74114], ![271459, -171833, -125299, -151696, -101491]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-8495, -10567, -7676, -9312, -6261]] ![![-8495, -10567, -7676, -9312, -6261]]
  ![![2679937423, 3395713690, 2475493642, 2995594166, 2003493370]] where
 M := ![![![2679937423, 3395713690, 2475493642, 2995594166, 2003493370]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![2679937423, 3395713690, 2475493642, 2995594166, 2003493370]] ![![-8495, -10567, -7676, -9312, -6261]]
  ![![-860594704670081, -1090461397679707, -794953588642006, -961970983886346, -643376691155773]] where
 M := ![![![-860594704670081, -1090461397679707, -794953588642006, -961970983886346, -643376691155773]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-860594704670081, -1090461397679707, -794953588642006, -961970983886346, -643376691155773]] ![![-8495, -10567, -7676, -9312, -6261]]
  ![![276361323208290338921, 350178028537742059444, 255282104651085275332, 308916118443984876592, 206606470437783995784]] where
 M := ![![![276361323208290338921, 350178028537742059444, 255282104651085275332, 308916118443984876592, 206606470437783995784]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![276361323208290338921, 350178028537742059444, 255282104651085275332, 308916118443984876592, 206606470437783995784]] ![![-8495, -10567, -7676, -9312, -6261]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-88747445239545761344662215, -112452079224080574616218835, -81978311365201387176328120, -99201711683276999286294880, -66347187111741346516131205]]]
 hmul := by decide  
 g := ![![![![-17749489047909152268932443, -22490415844816114923243767, -16395662273040277435265624, -19840342336655399857258976, -13269437422348269303226241]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [3, 6, 2, 0, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4, 1, 3, 4], [2, 2, 0, 0, 2], [4, 4, 6, 0, 2], [3, 3, 0, 4, 6], [0, 1]]
 g := ![![[1, 6, 1], []], ![[3, 1, 4, 6, 6, 1, 2, 2], [3, 6, 6, 0, 3, 6, 3, 1]], ![[4, 1, 6, 2, 1, 6, 3, 1], [0, 5, 2, 6, 0, 1, 6, 1]], ![[5, 4, 3, 6, 3, 5, 6, 1], [3, 4, 5, 0, 1, 3, 6, 1]], ![[1, 5, 0, 1, 0, 5, 3, 3], [4, 2, 2, 5, 3, 2, 6, 6]]]
 h' := ![![[4, 4, 1, 3, 4], [0, 0, 0, 1], [0, 1]], ![[2, 2, 0, 0, 2], [6, 2, 5, 4, 5], [4, 4, 1, 3, 4]], ![[4, 4, 6, 0, 2], [1, 2, 2, 3, 5], [2, 2, 0, 0, 2]], ![[3, 3, 0, 4, 6], [6, 1, 1, 0, 2], [4, 4, 6, 0, 2]], ![[0, 1], [1, 2, 6, 6, 2], [3, 3, 0, 4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 6, 6, 6], [], [], []]
 b := ![[], [5, 3, 6, 6, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [3, 6, 2, 0, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1980646437, -2508987236, -1829478371, -2213569134, -1480312239]
  a := ![1, -6, -1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-282949491, -358426748, -261354053, -316224162, -211473177]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 16807 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, 1, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![1, -1, 1, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![1, 10, 1, 0, 0], ![6, 6, 0, 1, 0], ![8, 1, 0, 0, 1]] where
  M :=![![![1, -1, 1, 0, 0], ![0, 2, -1, 2, 0], ![0, 1, 2, -2, 4], ![8, 1, 5, 5, -2], ![-4, 7, -1, 2, 5]]]
  hmulB := by decide  
  f := ![![![-5, 9, 5, 0, -4]], ![![-16, -4, 1, 2, 0]], ![![-15, -4, 1, 2, 0]], ![![-10, 3, 3, 1, -2]], ![![-4, 7, 4, 0, -3]]]
  g := ![![![0, -1, 1, 0, 0], ![-1, 0, -1, 2, 0], ![-2, -1, 2, -2, 4], ![-1, -7, 5, 5, -2], ![-5, 0, -1, 2, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [3, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 10], [0, 1]]
 g := ![![[9, 4], [4, 3], [1]], ![[0, 7], [0, 8], [1]]]
 h' := ![![[6, 10], [10, 2], [8, 6], [0, 1]], ![[0, 1], [0, 9], [0, 5], [6, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [3, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [3, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8871, 10388, 8349, 9188, 6553]
  a := ![1, 26, 4, 18, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9730, -12253, 8349, 9188, 6553]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 14, 10, 12, 8]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 14, 10, 12, 8]] 
 ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![11, 14, 10, 12, 8], ![32, 41, 30, 36, 24], ![96, 122, 89, 108, 72], ![128, 162, 118, 143, 96], ![176, 222, 162, 196, 131]]]
  hmulB := by decide  
  f := ![![![1, -10, -6, -4, 8]], ![![3, -1, 0, 0, 0]], ![![-2, -6, -7, -4, 8]], ![![0, -2, 2, -1, 0]], ![![-1, -4, -4, 0, 3]]]
  g := ![![![-13, 14, 10, 12, 8], ![-39, 41, 30, 36, 24], ![-116, 122, 89, 108, 72], ![-154, 162, 118, 143, 96], ![-211, 222, 162, 196, 131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10905, -7869, 8195, -1156, -2886]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![10905, -7869, 8195, -1156, -2886]] 
 ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![10905, -7869, 8195, -1156, -2886], ![-11544, 15058, -13641, 10618, -2312], ![-9248, -16879, 10434, -31906, 21236], ![48244, -12271, 19617, 26361, -30750], ![-55728, 24207, -30065, -16442, 27517]]]
  hmulB := by decide  
  f := ![![![-39573, -50035, -36337, -43836, -29298]], ![![-25044, -31744, -23089, -27874, -18624]], ![![-53466, -67725, -49310, -59602, -39848]], ![![-71188, -90079, -65573, -79271, -53014]], ![![-72476, -91745, -66827, -80826, -54059]]]
  g := ![![![1273, -7869, 8195, -1156, -2886], ![-5966, 15058, -13641, 10618, -2312], ![15088, -16879, 10434, -31906, 21236], ![-9842, -12271, 19617, 26361, -30750], ![4482, 24207, -30065, -16442, 27517]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2

def I11N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-297, 872, 452, -28, -338]] i)))

def SI11N3: IdealEqSpanCertificate' Table ![![-297, 872, 452, -28, -338]] 
 ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-297, 872, 452, -28, -338], ![-1352, -211, 196, 228, -56], ![-224, -984, -323, 280, 456], ![1588, 200, -134, 19, 308], ![1292, 996, 310, 60, 47]]]
  hmulB := by decide  
  f := ![![![-14811, -512, -2864, -14068, 12854]], ![![-4751, -2043, 468, -7136, 5622]], ![![-18310, 5944, -8395, -8208, 10644]], ![![889, -6264, 4818, -7945, 4250]], ![![-11620, 4068, -5546, -4796, 6519]]]
  g := ![![![-575, 872, 452, -28, -338], ![-117, -211, 196, 228, -56], ![374, -984, -323, 280, 456], ![-139, 200, -134, 19, 308], ![-736, 996, 310, 60, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N3 : Nat.card (O ⧸ I11N3) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N3)

lemma isPrimeI11N3 : Ideal.IsPrime I11N3 := prime_ideal_of_norm_prime hp11.out _ NI11N3
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![1, -1, 1, 0, 0]] ![![11, 14, 10, 12, 8]]
  ![![75, 95, 69, 84, 56]] where
 M := ![![![75, 95, 69, 84, 56]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![75, 95, 69, 84, 56]] ![![10905, -7869, 8195, -1156, -2886]]
  ![![14811, 512, 2864, 14068, -12854]] where
 M := ![![![14811, 512, 2864, 14068, -12854]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N2 : IdealMulLeCertificate' Table 
  ![![14811, 512, 2864, 14068, -12854]] ![![-297, 872, 452, -28, -338]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N2, I11N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
    exact isPrimeI11N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1 ⊙ MulI11N2)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, -41, -14, 4, 9]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-27, -41, -14, 4, 9]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![12, 4, 1, 0, 0], ![2, 5, 0, 1, 0], ![9, 11, 0, 0, 1]] where
  M :=![![![-27, -41, -14, 4, 9], ![36, -28, -23, -10, 8], ![32, 11, -12, -30, -20], ![-58, -1, -3, -27, -34], ![-86, -47, -23, -32, -31]]]
  hmulB := by decide  
  f := ![![![-121, 51, -64, -38, 61]], ![![244, -162, 173, -6, -76]], ![![-60, 23, -30, -22, 32]], ![![64, -65, 62, -33, -2]], ![![149, -102, 108, -8, -44]]]
  g := ![![![4, -8, -14, 4, 9], ![20, 2, -23, -10, 8], ![32, 33, -12, -30, -20], ![26, 40, -3, -27, -34], ![41, 42, -23, -32, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [11, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 12], [0, 1]]
 g := ![![[2, 4], [12], [4, 1]], ![[5, 9], [12], [8, 12]]]
 h' := ![![[4, 12], [10, 11], [8, 5], [0, 1]], ![[0, 1], [2, 2], [2, 8], [4, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [11, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [11, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1213, 3600, 648, 3258, 920]
  a := ![-1, -6, -4, 5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1643, -1954, 648, 3258, 920]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![135, 283, 164, 116, 41]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![135, 283, 164, 116, 41]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![7, 3, 1, 0, 0], ![9, 6, 0, 1, 0], ![5, 9, 0, 0, 1]] where
  M :=![![![135, 283, 164, 116, 41], ![164, 456, 365, 410, 232], ![928, 1171, 920, 1194, 820], ![1558, 1703, 1223, 1535, 1078], ![2074, 2469, 1747, 2096, 1419]]]
  hmulB := by decide  
  f := ![![![2701, -2009, 2074, -370, -667]], ![![-2668, 3738, -3343, 2814, -740]], ![![611, -522, 519, -178, -97]], ![![1607, 66, 303, 1541, -1403]], ![![-1905, 2310, -2122, 1508, -242]]]
  g := ![![![-174, -98, 164, 116, 41], ![-557, -399, 365, 410, 232], ![-1566, -1241, 920, 1194, 820], ![-2016, -1606, 1223, 1535, 1078], ![-2778, -2163, 1747, 2096, 1419]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [1, 10, 1] where
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
 g := ![![[10, 1], [12], [3, 1]], ![[0, 12], [12], [6, 12]]]
 h' := ![![[3, 12], [10, 1], [10, 8], [0, 1]], ![[0, 1], [0, 12], [8, 5], [3, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [11, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [1, 10, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3223, 3156, -2884, 1112, 536]
  a := ![0, -2, 4, -18, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![329, 24, -2884, 1112, 536]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![124739, -93130, 96042, -17578, -30524]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![124739, -93130, 96042, -17578, -30524]] 
 ![![13, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![124739, -93130, 96042, -17578, -30524], ![-122096, 172679, -154178, 131036, -35156], ![-140624, -180394, 102367, -378668, 262072], ![585192, -163766, 248964, 298921, -361090], ![-661132, 299654, -365884, -177644, 316499]]]
  hmulB := by decide  
  f := ![![![-1537, 13698, 11658, 11654, 5016]], ![![834, 8383, 7206, 7944, 4108]], ![![6817, 10888, 8337, 9926, 6288]], ![![9371, 12616, 8978, 10391, 6726]], ![![11081, 23048, 17486, 19414, 11299]]]
  g := ![![![48203, -93130, 96042, -17578, -30524], ![-44660, 172679, -154178, 131036, -35156], ![-63169, -180394, 102367, -378668, 262072], ![234585, -163766, 248964, 298921, -361090], ![-261481, 299654, -365884, -177644, 316499]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-27, -41, -14, 4, 9]] ![![135, 283, 164, 116, 41]]
  ![![1537, -13698, -11658, -11654, -5016]] where
 M := ![![![1537, -13698, -11658, -11654, -5016]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![1537, -13698, -11658, -11654, -5016]] ![![124739, -93130, 96042, -17578, -30524]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -5, 1, -2, 2]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-3, -5, 1, -2, 2]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![1, 11, 9, 1, 0], ![8, 0, 1, 0, 1]] where
  M :=![![![-3, -5, 1, -2, 2], ![8, -2, -1, 6, -4], ![-16, 9, -10, -10, 12], ![20, -11, 17, -1, -8], ![-20, 15, -13, 6, 1]]]
  hmulB := by decide  
  f := ![![![-3, -1, -1, -2, -2]], ![![-8, -8, -5, -6, -4]], ![![-16, -23, -16, -18, -12]], ![![-15, -19, -13, -15, -10]], ![![-4, -4, -3, -4, -3]]]
  g := ![![![-1, 1, 1, -2, 2], ![2, -4, -3, 6, -4], ![-6, 7, 4, -10, 12], ![5, 0, 2, -1, -8], ![-2, -3, -4, 6, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [3, 5, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 0, 7], [11, 16, 10], [0, 1]]
 g := ![![[8, 10, 9], [12, 2], [4, 1], []], ![[3, 6, 16, 5], [15, 4], [14, 1], [9, 15]], ![[13, 12, 0, 6], [8, 13], [], [6, 15]]]
 h' := ![![[10, 0, 7], [6, 10, 14], [5, 11, 11], [0, 0, 1], [0, 1]], ![[11, 16, 10], [6, 15, 5], [0, 13, 15], [5, 12, 16], [10, 0, 7]], ![[0, 1], [11, 9, 15], [1, 10, 8], [1, 5], [11, 16, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 7], []]
 b := ![[], [16, 9, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [3, 5, 13, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-326918, -243160, -315360, -235780, -200700]
  a := ![13, -6, -3, 2, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![89086, 138260, 118080, -235780, -200700]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -28, 16, -58, 40]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-21, -28, 16, -58, 40]] 
 ![![17, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-21, -28, 16, -58, 40], ![160, -23, 52, 112, -116], ![-464, 208, -255, -128, 224], ![368, -300, 302, -87, -70], ![-220, 268, -246, 176, -29]]]
  hmulB := by decide  
  f := ![![![163, 172, 84, 62, 36]], ![![66, 81, 44, 36, 20]], ![![173, 196, 109, 98, 60]], ![![81, 88, 58, 67, 46]], ![![123, 136, 86, 94, 63]]]
  g := ![![![-7, -28, 16, -58, 40], ![-14, -23, 52, 112, -116], ![81, 208, -255, -128, 224], ![-103, -300, 302, -87, -70], ![87, 268, -246, 176, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![321, 381, 273, 332, 226]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![321, 381, 273, 332, 226]] 
 ![![17, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![321, 381, 273, 332, 226], ![904, 1152, 833, 998, 664], ![2656, 3399, 2480, 2994, 1996], ![3540, 4487, 3279, 3977, 2662], ![4872, 6153, 4489, 5442, 3645]]]
  hmulB := by decide  
  f := ![![![2377, -1543, 1659, -12, -766]], ![![1218, -716, 795, 98, -452]], ![![274, -439, 384, -366, 120]], ![![790, -263, 367, 345, -454]], ![![-358, 55, -119, -246, 257]]]
  g := ![![![-303, 381, 273, 332, 226], ![-918, 1152, 833, 998, 664], ![-2722, 3399, 2480, 2994, 1996], ![-3598, 4487, 3279, 3977, 2662], ![-4930, 6153, 4489, 5442, 3645]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-3, -5, 1, -2, 2]] ![![-21, -28, 16, -58, 40]]
  ![![-2377, 1543, -1659, 12, 766]] where
 M := ![![![-2377, 1543, -1659, 12, 766]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-2377, 1543, -1659, 12, 766]] ![![321, 381, 273, 332, 226]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [15, 16, 2, 17, 13, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 18, 8, 10, 1], [0, 18, 8, 2, 1], [15, 8, 16, 14, 1], [16, 12, 6, 12, 16], [0, 1]]
 g := ![![[8, 16, 11, 6, 17], [13, 10, 0, 6, 1], [], []], ![[1, 4, 10, 15, 13, 8, 3, 1], [15, 6, 8, 10, 13, 6, 18, 16], [8, 7, 18, 16], [9, 8, 7, 1]], ![[18, 4, 8, 8, 7, 10, 11, 5], [12, 4, 4, 17, 1, 14, 3, 5], [15, 16, 14, 7], [8, 6, 10, 1]], ![[13, 11, 7, 8, 15, 17, 15, 11], [16, 2, 0, 17, 18, 8, 17, 5], [16, 10, 2, 16], [18, 16, 15, 1]], ![[2, 18, 10, 16, 10, 15, 14, 4], [17, 8, 15, 9, 17, 11, 5, 11], [16, 16], [12, 18, 1, 9]]]
 h' := ![![[13, 18, 8, 10, 1], [14, 3, 4, 11, 6], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[0, 18, 8, 2, 1], [11, 6, 3, 3, 1], [10, 16, 1, 6, 15], [15, 14, 15, 5, 15], [13, 18, 8, 10, 1]], ![[15, 8, 16, 14, 1], [10, 13, 15, 10, 9], [1, 8, 0, 18, 9], [13, 10, 5, 3, 8], [0, 18, 8, 2, 1]], ![[16, 12, 6, 12, 16], [3, 2, 5, 16, 12], [18, 16, 17, 12, 10], [12, 16, 8, 7, 15], [15, 8, 16, 14, 1]], ![[0, 1], [16, 14, 11, 17, 10], [7, 17, 1, 2, 3], [0, 17, 9, 4], [16, 12, 6, 12, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 16, 3, 18], [], [], []]
 b := ![[], [12, 0, 11, 0, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [15, 16, 2, 17, 13, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![69360906, 205388138, 60573881, 162786870, 89996350]
  a := ![-1, 0, 2, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3650574, 10809902, 3188099, 8567730, 4736650]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1757, 86, 382, 186, -264]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-1757, 86, 382, 186, -264]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![11, 14, 14, 1, 0], ![7, 1, 18, 0, 1]] where
  M :=![![![-1757, 86, 382, 186, -264], ![-1056, -1453, -442, 236, 372], ![1488, -890, -709, -140, 472], ![1472, 1282, 248, -355, -326], ![-124, 1246, 536, -196, -541]]]
  hmulB := by decide  
  f := ![![![-947, 822, -814, 294, 140]], ![![560, -1327, 1102, -1348, 588]], ![![2352, 902, -151, 3380, -2696]], ![![1073, 226, 68, 1283, -1082]], ![![1833, 763, -162, 2718, -2149]]]
  g := ![![![-85, -98, 110, 186, -264], ![-272, -223, -454, 236, 372], ![-12, 26, -315, -140, 472], ![333, 286, 482, -355, -326], ![253, 197, 566, -196, -541]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [5, 9, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 18, 17], [15, 4, 6], [0, 1]]
 g := ![![[7, 16, 18], [0, 7, 12], [0, 3, 1], []], ![[9, 15, 4, 14], [6, 1, 10, 7], [14, 1, 16, 19], [7, 13]], ![[6, 7, 9, 3], [12, 17, 2, 6], [16, 8, 1, 12], [18, 13]]]
 h' := ![![[11, 18, 17], [0, 11, 15], [0, 8, 14], [0, 0, 1], [0, 1]], ![[15, 4, 6], [8, 9, 17], [4, 9, 8], [17, 15, 4], [11, 18, 17]], ![[0, 1], [5, 3, 14], [9, 6, 1], [20, 8, 18], [15, 4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 10], []]
 b := ![[], [7, 0, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [5, 9, 20, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2345539, 2484734, 2106872, 2338960, 1478788]
  a := ![3, 10, 7, -1, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1466719, -1379978, -2489424, 2338960, 1478788]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![947, -822, 814, -294, -140]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![947, -822, 814, -294, -140]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![16, 18, 1, 0, 0], ![17, 19, 0, 1, 0], ![9, 22, 0, 0, 1]] where
  M :=![![![947, -822, 814, -294, -140], ![-560, 1327, -1102, 1348, -588], ![-2352, -902, 151, -3380, 2696], ![5672, -2106, 2796, 2173, -3086], ![-5892, 3114, -3588, -964, 2467]]]
  hmulB := by decide  
  f := ![![![1757, -86, -382, -186, 264]], ![![1056, 1453, 442, -236, -372]], ![![1984, 1116, 111, -308, -128]], ![![2107, 1081, 72, -317, -98]], ![![1703, 1302, 250, -290, -229]]]
  g := ![![![-253, -296, 814, -294, -140], ![-24, 369, -1102, 1348, -588], ![1236, 56, 151, -3380, 2696], ![-2097, -1123, 2796, 2173, -3086], ![1987, 1380, -3588, -964, 2467]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [16, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 22], [0, 1]]
 g := ![![[18, 13], [7, 16], [13, 6], [1]], ![[0, 10], [22, 7], [10, 17], [1]]]
 h' := ![![[11, 22], [3, 6], [22, 4], [7, 11], [0, 1]], ![[0, 1], [0, 17], [20, 19], [13, 12], [11, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [1, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [16, 12, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![523, 1106, 345, 946, 446]
  a := ![1, 4, 2, -2, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1091, -1430, 345, 946, 446]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-1757, 86, 382, 186, -264]] ![![947, -822, 814, -294, -140]]
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


lemma PB307I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB307I0 : PrimesBelowBoundCertificateInterval O 1 23 307 where
  m := 9
  g := ![5, 4, 5, 1, 4, 3, 3, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB307I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1, I11N2, I11N3]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1, I17N2]
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
    · exact ![9, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![16807]
    · exact ![121, 11, 11, 11]
    · exact ![169, 169, 13]
    · exact ![4913, 17, 17]
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
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
      exact NI11N3
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
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I11N0, I11N1, I11N2, I11N3, I13N0, I13N1, I13N2, I17N1, I17N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [I11N0, I11N1, I11N2, I11N3], [I13N0, I13N1, I13N2], [I17N1, I17N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
