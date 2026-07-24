
import IdealArithmetic.Examples.NF5_1_15000000_1.RI5_1_15000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -3, -4, -3, 5]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![25, -3, -4, -3, 5]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![25, -3, -4, -3, 5], ![-45, 6, 7, 5, -9], ![81, -11, -12, -9, 15], ![-63, 10, 9, 7, -12], ![21, -3, -3, -3, 4]]]
  hmulB := by decide  
  f := ![![![-7, -4, 1, 2, 2]], ![![-9, -6, 1, 3, 3]], ![![-27, -17, 2, 7, 9]], ![![-8, -5, 1, 2, 1]], ![![-12, -9, 0, 3, 4]]]
  g := ![![![14, -3, -4, -3, 5], ![-25, 6, 7, 5, -9], ![45, -11, -12, -9, 15], ![-35, 10, 9, 7, -12], ![12, -3, -3, -3, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 14, 4, 0, -11]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-17, 14, 4, 0, -11]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-17, 14, 4, 0, -11], ![99, 20, -11, -17, 0], ![0, 88, 15, -10, -51], ![90, -7, -11, -9, 18], ![6, 33, 9, 0, -14]]]
  hmulB := by decide  
  f := ![![![41, -15, 3, 25, -11]], ![![70, 31, -32, -23, 32]], ![![-317, -104, 121, 62, -112]], ![![396, 64, -108, -1, 81]], ![![-71, 18, 0, -34, 12]]]
  g := ![![![-12, 14, 4, 0, -11], ![45, 20, -11, -17, 0], ![-26, 88, 15, -10, -51], ![45, -7, -11, -9, 18], ![-11, 33, 9, 0, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 22, -9, -16, -15]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![41, 22, -9, -16, -15]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![41, 22, -9, -16, -15], ![135, 77, -25, -49, -48], ![432, 254, -68, -146, -147], ![81, 55, -4, -20, -24], ![270, 171, -27, -78, -85]]]
  hmulB := by decide  
  f := ![![![-23, -10, 10, 5, -9]], ![![29, 2, -6, 4, 3]], ![![-79, 2, 11, -22, 0]], ![![2, -29, 19, 36, -27]], ![![54, 18, -21, -12, 20]]]
  g := ![![![22, 22, -9, -16, -15], ![66, 77, -25, -49, -48], ![196, 254, -68, -146, -147], ![25, 55, -4, -20, -24], ![102, 171, -27, -78, -85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![25, -3, -4, -3, 5]] ![![-17, 14, 4, 0, -11]]
  ![![-962, 124, 151, 118, -195]] where
 M := ![![![-962, 124, 151, 118, -195]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-962, 124, 151, 118, -195]] ![![-17, 14, 4, 0, -11]]
  ![![38080, -4961, -6000, -4680, 7735]] where
 M := ![![![38080, -4961, -6000, -4680, 7735]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![38080, -4961, -6000, -4680, 7735]] ![![41, 22, -9, -16, -15]]
  ![![8915, -2952, -820, 79, 3773]] where
 M := ![![![8915, -2952, -820, 79, 3773]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![8915, -2952, -820, 79, 3773]] ![![41, 22, -9, -16, -15]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![637864, 410074, -52862, -174146, -194090]]]
 hmul := by decide  
 g := ![![![![318932, 205037, -26431, -87073, -97045]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36206, 4674, 5696, 4453, -7331]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-36206, 4674, 5696, 4453, -7331]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![1, 0, 2, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-36206, 4674, 5696, 4453, -7331], ![65979, -8517, -10380, -8115, 13359], ![-120231, 15522, 18915, 14787, -24345], ![98397, -12702, -15480, -12102, 19923], ![-34248, 4422, 5388, 4212, -6935]]]
  hmulB := by decide  
  f := ![![![-6, -8, 4, 7, -3]], ![![27, 7, -16, -7, 21]], ![![-189, -52, 45, 13, -21]], ![![-83, -36, 22, 17, -10]], ![![-6, 2, -4, -6, 7]]]
  g := ![![![-13553, 1558, -1070, 4453, -7331], ![24698, -2839, 1950, -8115, 13359], ![-45006, 5174, -3553, 14787, -24345], ![36833, -4234, 2908, -12102, 19923], ![-12820, 1474, -1012, 4212, -6935]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [2, 1, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2, 2], [1, 0, 1], [0, 1]]
 g := ![![[1]], ![[0, 0, 1, 2]], ![[2, 0, 2, 1]]]
 h' := ![![[1, 2, 2], [0, 1]], ![[1, 0, 1], [1, 2, 2]], ![[0, 1], [1, 0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 2], []]
 b := ![[], [0, 0, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [2, 1, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10535354, 6476694, -964157, -2932729, -3716605]
  a := ![0, -8, -7, -7, -37]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4489361, 2158898, 1633767, -2932729, -3716605]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 27 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18, 7, 3, 1, -7]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-18, 7, 3, 1, -7]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-18, 7, 3, 1, -7], ![63, 6, -9, -11, 3], ![-27, 45, 8, -5, -33], ![72, -4, -10, -9, 12], ![3, 21, 3, -3, -12]]]
  hmulB := by decide  
  f := ![![![-30, 3, 3, -9, 1]], ![![-3, -10, 7, 11, -9]], ![![81, 31, -34, -21, 33]], ![![-114, -26, 36, 9, -30]], ![![41, -3, -5, 11, 0]]]
  g := ![![![-6, 7, 3, 1, -7], ![21, 6, -9, -11, 3], ![-9, 45, 8, -5, -33], ![24, -4, -10, -9, 12], ![1, 21, 3, -3, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-36206, 4674, 5696, 4453, -7331]] ![![-18, 7, 3, 1, -7]]
  ![![1091001, -140841, -171639, -134184, 220904]] where
 M := ![![![1091001, -140841, -171639, -134184, 220904]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![1091001, -140841, -171639, -134184, 220904]] ![![-18, 7, 3, 1, -7]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-32875284, 4243926, 5172012, 4043391, -6656499]]]
 hmul := by decide  
 g := ![![![![-10958428, 1414642, 1724004, 1347797, -2218833]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 3, -1, -2, -2]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 3, -1, -2, -2]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![5, 3, -1, -2, -2], ![18, 10, -3, -6, -6], ![54, 33, -8, -18, -18], ![9, 6, 0, -2, -3], ![33, 21, -3, -9, -10]]]
  hmulB := by decide  
  f := ![![![-11, 3, 1, 2, -2]], ![![-3, 1, 0, 0, 0]], ![![-13, 0, 3, 4, -4]], ![![6, 3, -3, -2, 3]], ![![-10, 0, 2, 1, -2]]]
  g := ![![![1, 3, -1, -2, -2], ![3, 10, -3, -6, -6], ![7, 33, -8, -18, -18], ![0, 6, 0, -2, -3], ![2, 21, -3, -9, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 3, -1, -2, -2]] ![![5, 3, -1, -2, -2]]
  ![![-59, -42, 0, 12, 16]] where
 M := ![![![-59, -42, 0, 12, 16]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-59, -42, 0, 12, 16]] ![![5, 3, -1, -2, -2]]
  ![![-415, -189, 137, 202, 174]] where
 M := ![![![-415, -189, 137, 202, 174]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-415, -189, 137, 202, 174]] ![![5, 3, -1, -2, -2]]
  ![![9481, 6252, -636, -2472, -2848]] where
 M := ![![![9481, 6252, -636, -2472, -2848]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![9481, 6252, -636, -2472, -2848]] ![![5, 3, -1, -2, -2]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![9365, -4665, -14605, -14450, -9130]]]
 hmul := by decide  
 g := ![![![![1873, -933, -2921, -2890, -1826]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1837, -237, -289, -226, 372]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![1837, -237, -289, -226, 372]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![2, 4, 4, 1, 0], ![0, 2, 6, 0, 1]] where
  M :=![![![1837, -237, -289, -226, 372], ![-3348, 432, 527, 412, -678], ![6102, -787, -960, -750, 1236], ![-4995, 644, 786, 614, -1011], ![1737, -225, -273, -213, 352]]]
  hmulB := by decide  
  f := ![![![7, 5, -1, -2, 0]], ![![0, 6, 5, 0, -6]], ![![54, 23, -2, 2, 0]], ![![29, 18, 2, 0, -3]], ![![45, 21, 1, 3, -2]]]
  g := ![![![327, -11, -231, -226, 372], ![-596, 20, 421, 412, -678], ![1086, -37, -768, -750, 1236], ![-889, 30, 628, 614, -1011], ![309, -11, -219, -213, 352]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [5, 2, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 6, 4], [1, 0, 3], [0, 1]]
 g := ![![[5, 6, 2], [1]], ![[1, 4, 0, 4], [6, 6, 5, 1]], ![[5, 4, 6, 6], [2, 6, 3, 6]]]
 h' := ![![[3, 6, 4], [2, 5, 4], [0, 1]], ![[1, 0, 3], [4, 1, 6], [3, 6, 4]], ![[0, 1], [5, 1, 4], [1, 0, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 3], []]
 b := ![[], [3, 6, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [5, 2, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3798583139, 2341028352, -407621672, -1127023894, -1315466882]
  a := ![3, -61, -63, -66, -235]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![864661561, 1354293956, 1713325028, -1127023894, -1315466882]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16, 10, -2, -5, -5]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![16, 10, -2, -5, -5]] 
 ![![7, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![16, 10, -2, -5, -5], ![45, 29, -4, -13, -15], ![135, 86, -11, -35, -39], ![9, 10, 2, -2, -3], ![60, 42, 0, -12, -17]]]
  hmulB := by decide  
  f := ![![![-956, 124, 150, 117, -193]], ![![-25, 3, 4, 3, -5]], ![![-861, 112, 135, 106, -174]], ![![369, -48, -58, -46, 75]], ![![-266, 34, 42, 33, -54]]]
  g := ![![![1, 10, -2, -5, -5], ![2, 29, -4, -13, -15], ![5, 86, -11, -35, -39], ![-2, 10, 2, -2, -3], ![-1, 42, 0, -12, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, -1, -1, 1]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![2, 1, -1, -1, 1]] 
 ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![2, 1, -1, -1, 1], ![-9, -2, 3, 1, -3], ![27, 3, -6, 1, 3], ![-18, 2, 2, -5, 0], ![-3, -3, 3, 3, -4]]]
  hmulB := by decide  
  f := ![![![2, -7, -1, 1, 5]], ![![-5, -7, 0, 2, 4]], ![![-3, -10, -1, 2, 6]], ![![-4, -4, 0, 1, 2]], ![![-1, -7, -1, 1, 4]]]
  g := ![![![0, 1, -1, -1, 1], ![0, -2, 3, 1, -3], ![2, 3, -6, 1, 3], ![-2, 2, 2, -5, 0], ![1, -3, 3, 3, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![1837, -237, -289, -226, 372]] ![![16, 10, -2, -5, -5]]
  ![![-2, 7, 1, -1, -5]] where
 M := ![![![-2, 7, 1, -1, -5]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-2, 7, 1, -1, -5]] ![![2, 1, -1, -1, 1]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3121, -403, -491, -384, 632]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![3121, -403, -491, -384, 632]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![3, 8, 1, 0, 0], ![9, 3, 0, 1, 0], ![4, 7, 0, 0, 1]] where
  M :=![![![3121, -403, -491, -384, 632], ![-5688, 734, 895, 700, -1152], ![10368, -1337, -1632, -1276, 2100], ![-8487, 1094, 1336, 1044, -1719], ![2955, -381, -465, -363, 598]]]
  hmulB := by decide  
  f := ![![![-25, -21, -3, 4, 8]], ![![-72, -52, -7, 4, 12]], ![![-69, -54, -9, 4, 12]], ![![-36, -29, -6, 2, 9]], ![![-53, -41, -8, 1, 8]]]
  g := ![![![502, 23, -491, -384, 632], ![-915, -42, 895, 700, -1152], ![1668, 77, -1632, -1276, 2100], ![-1365, -63, 1336, 1044, -1719], ![475, 22, -465, -363, 598]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [2, 5, 1] where
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
 g := ![![[8, 3], [5, 3], [1]], ![[4, 8], [1, 8], [1]]]
 h' := ![![[6, 10], [1, 6], [9, 6], [0, 1]], ![[0, 1], [4, 5], [1, 5], [6, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [1, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [2, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-318757, -198672, 81990, 147169, 99259]
  a := ![1, 26, 22, 17, 121]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-207844, -180992, 81990, 147169, 99259]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-194, -102, 48, 81, 75]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-194, -102, 48, 81, 75]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![2, 7, 1, 0, 0], ![1, 7, 0, 1, 0], ![4, 2, 0, 0, 1]] where
  M :=![![![-194, -102, 48, 81, 75], ![-675, -371, 138, 255, 243], ![-2187, -1266, 379, 771, 765], ![-459, -300, 30, 118, 135], ![-1440, -900, 162, 432, 463]]]
  hmulB := by decide  
  f := ![![![338, 60, -96, -9, 75]], ![![-675, 17, 102, -141, -27]], ![![-346, -23, 73, -36, -42]], ![![-308, 79, 0, -146, 51]], ![![-116, 2, 18, -24, -5]]]
  g := ![![![-61, -105, 48, 81, 75], ![-198, -328, 138, 255, 243], ![-616, -986, 379, 771, 765], ![-107, -146, 30, 118, 135], ![-368, -544, 162, 432, 463]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [8, 4, 1] where
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
 g := ![![[6, 4], [0, 5], [1]], ![[1, 7], [2, 6], [1]]]
 h' := ![![[7, 10], [0, 2], [3, 7], [0, 1]], ![[0, 1], [3, 9], [8, 4], [7, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [3, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [8, 4, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16195, -21295, 5994, 16822, 7215]
  a := ![-1, -6, 1, 10, -51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6715, -17767, 5994, 16822, 7215]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![112, -33, 3, 59, -23]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![112, -33, 3, 59, -23]] 
 ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![112, -33, 3, 59, -23], ![207, 184, -155, -175, 177], ![-1593, -479, 580, 261, -525], ![1926, 334, -540, -31, 414], ![-489, 111, 9, -219, 70]]]
  hmulB := by decide  
  f := ![![![-6544, 823, 1031, 813, -1307]], ![![-3095, 379, 488, 388, -610]], ![![-5565, 685, 876, 695, -1101]], ![![-776, 88, 122, 99, -148]], ![![-6527, 809, 1027, 813, -1296]]]
  g := ![![![29, -33, 3, 59, -23], ![-111, 184, -155, -175, 177], ![226, -479, 580, 261, -525], ![-108, 334, -540, -31, 414], ![-104, 111, 9, -219, 70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![3121, -403, -491, -384, 632]] ![![-194, -102, 48, 81, 75]]
  ![![6544, -823, -1031, -813, 1307]] where
 M := ![![![6544, -823, -1031, -813, 1307]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![6544, -823, -1031, -813, 1307]] ![![112, -33, 3, 59, -23]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13651, -4970, 5534, 3238, -5268]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-13651, -4970, 5534, 3238, -5268]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![9, 10, 10, 4, 1]] where
  M :=![![![-13651, -4970, 5534, 3238, -5268], ![47412, 7687, -12944, -144, 9714], ![-87426, 5326, 11085, -22346, -432], ![32832, -23346, 9830, 33143, -18972], ![49662, 19404, -21000, -13314, 20351]]]
  hmulB := by decide  
  f := ![![![389, 334, -42, -142, -192]], ![![1728, 923, -184, -460, -426]], ![![3834, 2822, -263, -1094, -1380]], ![![756, 286, -10, -89, -24]], ![![4923, 3308, -376, -1352, -1573]]]
  g := ![![![2597, 3670, 4478, 1870, -5268], ![-3078, -6881, -8468, -3000, 9714], ![-6426, 742, 1185, -1586, -432], ![15660, 12798, 15350, 8387, -18972], ![-10269, -14162, -17270, -7286, 20351]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [7, 4, 6, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 9, 12, 7], [7, 1, 2, 10], [3, 2, 12, 9], [0, 1]]
 g := ![![[4, 7, 0, 3], [6, 8, 1], []], ![[9, 2, 1, 5, 5, 2], [4], [10, 8, 12, 3, 10, 5]], ![[8, 2, 9, 3, 8, 3], [11, 0, 12], [10, 5, 1, 1, 7, 12]], ![[7, 1, 0, 10, 5, 12], [8, 4, 3], [5, 2, 12, 5, 12, 1]]]
 h' := ![![[11, 9, 12, 7], [10, 11, 3, 9], [0, 0, 0, 1], [0, 1]], ![[7, 1, 2, 10], [11, 10, 3, 2], [0, 12, 2], [11, 9, 12, 7]], ![[3, 2, 12, 9], [1, 8, 3, 8], [0, 7, 7, 8], [7, 1, 2, 10]], ![[0, 1], [8, 10, 4, 7], [5, 7, 4, 4], [3, 2, 12, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 4, 9], []]
 b := ![[], [], [5, 7, 1, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [7, 4, 6, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4737798439, 1141797112, -1541726328, -477702768, 1320560232]
  a := ![0, -2, -14, -36, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-549787973, -927985016, -1134409896, -443072592, 1320560232]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![389, 334, -42, -142, -192]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![389, 334, -42, -142, -192]] 
 ![![13, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![389, 334, -42, -142, -192], ![1728, 923, -184, -460, -426], ![3834, 2822, -263, -1094, -1380], ![756, 286, -10, -89, -24], ![1854, 1404, 0, -402, -565]]]
  hmulB := by decide  
  f := ![![![-13651, -4970, 5534, 3238, -5268]], ![![2597, 209, -570, 238, 342]], ![![-19326, -4178, 5961, 1270, -4896]], ![![-4825, -4472, 3736, 4293, -4296]], ![![1720, 728, -764, -526, 755]]]
  g := ![![![149, 334, -42, -142, -192], ![545, 923, -184, -460, -426], ![1122, 2822, -263, -1094, -1380], ![97, 286, -10, -89, -24], ![338, 1404, 0, -402, -565]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-13651, -4970, 5534, 3238, -5268]] ![![389, 334, -42, -142, -192]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [2, 5, 1, 13, 15, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 10, 12, 5, 8], [0, 9, 2, 3, 8], [4, 7, 1, 1, 5], [0, 7, 2, 8, 13], [0, 1]]
 g := ![![[1, 5, 6, 8, 9], [6, 8, 2, 1], [], []], ![[1, 1, 9, 10, 12, 6, 13, 8], [0, 8, 14, 13], [12, 0, 15, 1], [4, 5, 4, 13]], ![[15, 1, 16, 11, 7, 16, 9, 13], [13, 11, 4, 13], [16, 16, 8, 8], [3, 3, 6, 13]], ![[0, 5, 8, 0, 7, 9, 7, 10], [15, 4, 2, 8], [9, 6, 16, 9], [1, 10, 9, 8]], ![[0, 3, 12, 3, 6, 7, 9, 15], [13, 14, 2, 8], [9, 10, 10, 9], [13, 14, 2, 16]]]
 h' := ![![[15, 10, 12, 5, 8], [5, 5, 1, 4, 3], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[0, 9, 2, 3, 8], [13, 8, 10, 8, 1], [9, 7, 12, 12, 8], [13, 15, 15, 15, 1], [15, 10, 12, 5, 8]], ![[4, 7, 1, 1, 5], [7, 13, 5, 15, 5], [4, 4, 6, 5, 8], [11, 13, 0, 6, 5], [0, 9, 2, 3, 8]], ![[0, 7, 2, 8, 13], [0, 7, 10, 13, 11], [8, 12, 10, 2, 5], [14, 14, 5, 6, 14], [4, 7, 1, 1, 5]], ![[0, 1], [16, 1, 8, 11, 14], [12, 11, 6, 15, 12], [8, 9, 13, 7, 14], [0, 7, 2, 8, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 10, 11, 10], [], [], []]
 b := ![[], [4, 1, 3, 12, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [2, 5, 1, 13, 15, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![89907773503, -18489557442, 15054062445, 75271722817, 32715524421]
  a := ![13, -6, -1, 5, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5288692559, -1087621026, 885533085, 4427748401, 1924442613]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26, 6, -10, -3, 11]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![26, 6, -10, -3, 11]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![11, 4, 6, 17, 1]] where
  M :=![![![26, 6, -10, -3, 11], ![-99, -17, 22, -1, -9], ![81, -50, 1, 63, -3], ![-9, 52, -36, -64, 51], ![-132, -48, 42, 24, -31]]]
  hmulB := by decide  
  f := ![![![38, -4, -6, -5, 7]], ![![-63, 11, 10, 7, -15]], ![![135, -8, -21, -19, 21]], ![![-99, 14, 16, 12, -21]], ![![-35, 10, 6, 3, -11]]]
  g := ![![![-5, -2, -4, -10, 11], ![0, 1, 4, 8, -9], ![6, -2, 1, 6, -3], ![-30, -8, -18, -49, 51], ![11, 4, 12, 29, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [5, 6, 18, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 1, 8, 2], [2, 9, 13, 1], [11, 8, 17, 16], [0, 1]]
 g := ![![[3, 5], [18, 15, 7, 4], [1], []], ![[12, 15, 13, 18, 4, 2], [3, 9, 12, 0, 13, 18], [18, 7, 9], [5, 5, 4]], ![[16, 3, 5, 0, 17, 1], [10, 6, 10, 7, 6, 5], [13, 2, 6], [7, 5, 1]], ![[0, 15, 12, 6], [16, 8, 7, 12, 10, 1], [2, 1, 4], [15, 13, 9]]]
 h' := ![![[4, 1, 8, 2], [5, 13, 10], [14, 13, 1, 17], [0, 0, 1], [0, 1]], ![[2, 9, 13, 1], [5, 18, 0, 18], [10, 0, 13, 16], [10, 10, 1, 3], [4, 1, 8, 2]], ![[11, 8, 17, 16], [6, 16, 3, 1], [3, 10, 8, 10], [7, 7, 10, 14], [2, 9, 13, 1]], ![[0, 1], [0, 10, 6], [16, 15, 16, 14], [8, 2, 7, 2], [11, 8, 17, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [11, 2, 17], []]
 b := ![[], [], [11, 13, 14, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [5, 6, 18, 2, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4793083, 654792, -1229108, 96798, 844050]
  a := ![-1, 0, -2, -5, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-236393, -143232, -331232, -750108, 844050]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38, -4, -6, -5, 7]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![38, -4, -6, -5, 7]] 
 ![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![38, -4, -6, -5, 7], ![-63, 11, 10, 7, -15], ![135, -8, -21, -19, 21], ![-99, 14, 16, 12, -21], ![42, 0, -6, -6, 5]]]
  hmulB := by decide  
  f := ![![![26, 6, -10, -3, 11]], ![![3, 1, -2, -1, 3]], ![![7, -2, -1, 3, 1]], ![![5, 4, -4, -4, 5]], ![![4, 0, -2, 0, 3]]]
  g := ![![![2, -4, -6, -5, 7], ![-3, 11, 10, 7, -15], ![7, -8, -21, -19, 21], ![-5, 14, 16, 12, -21], ![2, 0, -6, -6, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![26, 6, -10, -3, 11]] ![![38, -4, -6, -5, 7]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-75551, 9754, 11886, 9292, -15298]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-75551, 9754, 11886, 9292, -15298]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![7, 14, 22, 1, 0], ![14, 7, 17, 0, 1]] where
  M :=![![![-75551, 9754, 11886, 9292, -15298], ![137682, -17771, -21660, -16934, 27876], ![-250884, 32394, 39471, 30856, -50802], ![205326, -26506, -32302, -25253, 41574], ![-71466, 9228, 11244, 8790, -14471]]]
  hmulB := by decide  
  f := ![![![47, -2, -6, 12, 2]], ![![-18, 35, -20, -42, 36]], ![![-324, -146, 145, 112, -126]], ![![-287, -114, 118, 83, -92]], ![![-226, -99, 99, 76, -81]]]
  g := ![![![3199, -576, 2936, 9292, -15298], ![-5828, 1051, -5348, -16934, 27876], ![10624, -1912, 9751, 30856, -50802], ![-8693, 1566, -7978, -25253, 41574], ![3026, -545, 2777, 8790, -14471]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [17, 8, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 10, 17], [9, 12, 6], [0, 1]]
 g := ![![[10, 2, 9], [12, 9, 13], [15, 0, 1], []], ![[17, 1, 22, 10], [15, 10, 5, 21], [19, 3, 18, 10], [18, 13]], ![[14, 17, 10, 3], [16, 3, 1, 18], [15, 14, 15, 2], [6, 13]]]
 h' := ![![[14, 10, 17], [3, 8, 3], [21, 18, 6], [0, 0, 1], [0, 1]], ![[9, 12, 6], [15, 9, 11], [4, 15, 10], [5, 7, 12], [14, 10, 17]], ![[0, 1], [12, 6, 9], [11, 13, 7], [2, 16, 10], [9, 12, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 1], []]
 b := ![[], [8, 11, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [17, 8, 0, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-34756573, -18602987, 3049389, 7032879, 10764600]
  a := ![3, 10, 6, -2, 63]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10203962, -8365891, -14550963, 7032879, 10764600]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, 2, 6, -12, -2]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-47, 2, 6, -12, -2]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![17, 6, 1, 0, 0], ![12, 4, 0, 1, 0], ![14, 16, 0, 0, 1]] where
  M :=![![![-47, 2, 6, -12, -2], ![18, -35, 20, 42, -36], ![324, 146, -145, -112, 126], ![-450, -114, 154, 51, -138], ![222, 12, -36, 30, 1]]]
  hmulB := by decide  
  f := ![![![75551, -9754, -11886, -9292, 15298]], ![![-137682, 17771, 21660, 16934, -27876]], ![![30833, -3982, -4851, -3792, 6244]], ![![6546, -846, -1030, -805, 1326]], ![![-46684, 6024, 7344, 5742, -9451]]]
  g := ![![![1, 2, 6, -12, -2], ![-14, 11, 20, 42, -36], ![103, -24, -145, -112, 126], ![-76, 42, 154, 51, -138], ![20, 4, -36, 30, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [20, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 22], [0, 1]]
 g := ![![[13, 3], [3, 1], [6, 3], [1]], ![[15, 20], [19, 22], [8, 20], [1]]]
 h' := ![![[16, 22], [9, 7], [18, 22], [3, 16], [0, 1]], ![[0, 1], [6, 16], [2, 1], [6, 7], [16, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [21, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [20, 7, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7481, -8302, 2528, 6445, 3267]
  a := ![1, 4, 0, -5, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7545, -4414, 2528, 6445, 3267]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-75551, 9754, 11886, 9292, -15298]] ![![-47, 2, 6, -12, -2]]
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


lemma PB242I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB242I0 : PrimesBelowBoundCertificateInterval O 1 23 242 where
  m := 9
  g := ![5, 3, 5, 3, 3, 2, 1, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB242I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
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
    · exact ![27, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![343, 7, 7]
    · exact ![121, 121, 11]
    · exact ![28561, 13]
    · exact ![1419857]
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
      exact NI11N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I7N2, I11N0, I11N1, I11N2, I13N1, I19N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1, I7N2], [I11N0, I11N1, I11N2], [I13N1], [], [I19N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
