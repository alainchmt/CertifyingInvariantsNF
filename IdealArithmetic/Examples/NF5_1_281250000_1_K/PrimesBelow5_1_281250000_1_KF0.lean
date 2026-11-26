
import IdealArithmetic.Examples.NF5_1_281250000_1_K.RI5_1_281250000_1_K
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


def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![1, 0, 1, 0, 0]] i)))

def P3P0 : CertificateIrreducibleZModOfList' 3 1 2 1 [0, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[2, 0, 1]]]
 h' := ![![[0, 1], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P3P1 : CertificateIrreducibleZModOfList' 3 2 2 1 [1, 0, 1] where
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

def A3 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 3 3 where
 D := ![[0, 1], [1, 0, 1], [1, 0, 1]]; D' := ![[0, 1], [1, 0, 1], [1, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![1, 1, 1]
 n := ![1, 2, 2]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P3P0
  | 1 => exact P3P1
  | 2 => exact P3P1

def C30 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3.D 0) 3 where
  n := 1
  w := ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C31 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A3.D 1) 3 where
  n := 2
  w := ![![3, 0, 0, 0, 0], ![1, 0, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K3 : KummerData 3 ![I3N0, I3N1, I3N1] ![3, 9, 9] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A3
  C := by
    intro i
    match i with
    | 0 => exact C30
    | 1 => exact C31
    | 2 => exact C31
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 3 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide

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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![3, 6, 1, 0, 0]] i)))

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![5, 1, 1, 5, 0]] i)))

def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [3, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6], [0, 1]]
 g := ![![[2, 4], [1, 1]], ![[6, 3], [2, 6]]]
 h' := ![![[1, 6], [4, 5], [0, 1]], ![[0, 1], [2, 2], [1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [5, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P7P1 : CertificateIrreducibleZModOfList' 7 3 2 2 [5, 1, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4, 2], [2, 2, 5], [0, 1]]
 g := ![![[2, 1, 1], [1]], ![[1, 5, 5, 4], [3, 5, 5, 1]], ![[6, 2, 0, 6], [6, 4, 4, 6]]]
 h' := ![![[4, 4, 2], [2, 6, 6], [0, 1]], ![[2, 2, 5], [0, 3, 3], [4, 4, 2]], ![[0, 1], [6, 5, 5], [2, 2, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 5], []]
 b := ![[], [1, 4, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A7 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 7 2 where
 D := ![[3, 6, 1], [5, 1, 1, 1]]; D' := ![[3, 6, 1], [5, 1, 1, 1]]
 heqm := by decide
 hProd := by decide
 s := ![2, 2]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P7P0
  | 1 => exact P7P1

def C70 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A7.D 0) 7 where
  n := 2
  w := ![![7, 0, 0, 0, 0], ![3, 6, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C71 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A7.D 1) 7 where
  n := 3
  w := ![![7, 0, 0, 0, 0], ![5, 1, 1, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K7 : KummerData 7 ![I7N0, I7N1] ![49, 343] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A7
  C := by
    intro i
    match i with
    | 0 => exact C70
    | 1 => exact C71
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 7 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![308, -242, 0, 165, 0]] i)))

def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [8, 8, 0, 8, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 1, 1, 6, 7], [1, 0, 7, 4, 1], [9, 2, 1, 0, 6], [9, 7, 2, 1, 8], [0, 1]]
 g := ![![[1, 0, 9], [1], []], ![[0, 1, 0, 1, 6, 10, 3, 10], [9, 7, 9, 10, 9, 3, 2, 7], [3, 10, 7, 5]], ![[9, 6, 4, 5, 5, 7, 5, 4], [4, 3, 4, 10, 9, 0, 4, 1], [3, 0, 8, 1]], ![[9, 1, 8, 2, 9, 0, 9, 8], [9, 7, 0, 0, 3, 8, 7, 7], [2, 10, 0, 3]], ![[10, 4, 7, 6, 4, 10, 2, 8], [0, 6, 7, 2, 5, 0, 1, 2], [10, 5, 5, 9]]]
 h' := ![![[3, 1, 1, 6, 7], [3, 3, 0, 3], [0, 0, 1], [0, 1]], ![[1, 0, 7, 4, 1], [9, 7, 9, 1, 6], [7, 1, 3, 6, 1], [3, 1, 1, 6, 7]], ![[9, 2, 1, 0, 6], [2, 3, 0, 0, 2], [10, 9, 5, 0, 10], [1, 0, 7, 4, 1]], ![[9, 7, 2, 1, 8], [3, 8, 2, 5, 4], [10, 6, 8, 8, 5], [9, 2, 1, 0, 6]], ![[0, 1], [9, 1, 0, 2, 10], [1, 6, 5, 8, 6], [9, 7, 2, 1, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 5, 6, 4], [], [], []]
 b := ![[], [2, 3, 3, 3, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A11 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 11 1 where
 D := ![[8, 8, 0, 8, 0, 1]]; D' := ![[8, 8, 0, 8, 0, 1]]
 heqm := by decide
 hProd := by decide
 s := ![3]
 n := ![5]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P11P0

def C110 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A11.D 0) 11 where
  n := 5
  w := ![![11, 0, 0, 0, 0], ![308, -242, 0, 165, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K11 : KummerData 11 ![I11N0] ![161051] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A11
  C := by
    intro i
    match i with
    | 0 => exact C110
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 11 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![11, 4, 1, 0, 0]] i)))

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![7, 6, 9, 5, 0]] i)))

def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [11, 4, 1] where
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
 g := ![![[11, 4], [12], [9, 1]], ![[8, 9], [12], [5, 12]]]
 h' := ![![[9, 12], [10, 2], [5, 5], [0, 1]], ![[0, 1], [2, 11], [11, 8], [9, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [2, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P13P1 : CertificateIrreducibleZModOfList' 13 3 2 3 [7, 6, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 9, 12], [9, 3, 1], [0, 1]]
 g := ![![[10], [3, 3], [1]], ![[7, 10, 9, 3], [2, 12], [7, 9, 10, 12]], ![[2, 10, 0, 10], [11, 3], [10, 9, 0, 1]]]
 h' := ![![[8, 9, 12], [2, 6], [6, 7, 4], [0, 1]], ![[9, 3, 1], [11, 2, 7], [8, 11, 5], [8, 9, 12]], ![[0, 1], [4, 5, 6], [9, 8, 4], [9, 3, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 10], []]
 b := ![[], [10, 12, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A13 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 13 2 where
 D := ![[11, 4, 1], [7, 6, 9, 1]]; D' := ![[11, 4, 1], [7, 6, 9, 1]]
 heqm := by decide
 hProd := by decide
 s := ![3, 3]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P13P0
  | 1 => exact P13P1

def C130 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A13.D 0) 13 where
  n := 2
  w := ![![13, 0, 0, 0, 0], ![11, 4, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C131 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A13.D 1) 13 where
  n := 3
  w := ![![13, 0, 0, 0, 0], ![7, 6, 9, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K13 : KummerData 13 ![I13N0, I13N1] ![169, 2197] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A13
  C := by
    intro i
    match i with
    | 0 => exact C130
    | 1 => exact C131
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 13 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![9, 12, 1, 0, 0]] i)))

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![12, 8, 5, 5, 0]] i)))

def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [9, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 16], [0, 1]]
 g := ![![[7, 2], [1], [8], [1]], ![[0, 15], [1], [8], [1]]]
 h' := ![![[5, 16], [4, 6], [9, 1], [8, 5], [0, 1]], ![[0, 1], [0, 11], [14, 16], [16, 12], [5, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [15, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P17P1 : CertificateIrreducibleZModOfList' 17 3 2 4 [12, 8, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 2, 9], [9, 14, 8], [0, 1]]
 g := ![![[4, 7, 4], [], [12, 1], []], ![[14, 3, 5, 15], [10, 9], [5, 9], [5, 13]], ![[10, 8, 2, 1], [12, 9], [2, 4], [6, 13]]]
 h' := ![![[3, 2, 9], [13, 11, 2], [9, 11], [0, 0, 1], [0, 1]], ![[9, 14, 8], [12, 11, 8], [8, 5, 14], [0, 3, 14], [3, 2, 9]], ![[0, 1], [11, 12, 7], [6, 1, 3], [9, 14, 2], [9, 14, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 13], []]
 b := ![[], [14, 11, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A17 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 17 2 where
 D := ![[9, 12, 1], [12, 8, 5, 1]]; D' := ![[9, 12, 1], [12, 8, 5, 1]]
 heqm := by decide
 hProd := by decide
 s := ![4, 4]
 n := ![2, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P17P0
  | 1 => exact P17P1

def C170 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A17.D 0) 17 where
  n := 2
  w := ![![17, 0, 0, 0, 0], ![9, 12, 1, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C171 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A17.D 1) 17 where
  n := 3
  w := ![![17, 0, 0, 0, 0], ![12, 8, 5, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K17 : KummerData 17 ![I17N0, I17N1] ![289, 4913] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A17
  C := by
    intro i
    match i with
    | 0 => exact C170
    | 1 => exact C171
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 17 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![8, 1, 0, 0, 0]] i)))

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![14, 1, 0, 0, 0]] i)))

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![17, 5, 16, 5, 0]] i)))

def P19P0 : CertificateIrreducibleZModOfList' 19 1 2 4 [8, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [7], [], [11, 1]]]
 h' := ![![[0, 1], [1], [11], [7], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P19P1 : CertificateIrreducibleZModOfList' 19 1 2 4 [14, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [4], [], [5, 1]]]
 h' := ![![[0, 1], [1], [17], [6], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P19P2 : CertificateIrreducibleZModOfList' 19 3 2 4 [17, 5, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 11, 1], [0, 7, 18], [0, 1]]
 g := ![![[11, 11, 17], [7, 1, 16], [3, 1], []], ![[15, 13, 8, 11], [11, 8, 0, 16], [14, 11], [6, 1]], ![[0, 11, 6, 2], [17, 3], [2, 7], [8, 1]]]
 h' := ![![[3, 11, 1], [14, 3, 6], [6, 6, 4], [0, 0, 1], [0, 1]], ![[0, 7, 18], [16, 14, 7], [13, 9, 15], [2, 0, 7], [3, 11, 1]], ![[0, 1], [15, 2, 6], [13, 4], [16, 0, 11], [0, 7, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 3], []]
 b := ![[], [12, 12, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A19 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 19 3 where
 D := ![[8, 1], [14, 1], [17, 5, 16, 1]]; D' := ![[8, 1], [14, 1], [17, 5, 16, 1]]
 heqm := by decide
 hProd := by decide
 s := ![4, 4, 4]
 n := ![1, 1, 3]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P19P0
  | 1 => exact P19P1
  | 2 => exact P19P2

def C190 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A19.D 0) 19 where
  n := 1
  w := ![![19, 0, 0, 0, 0], ![8, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C191 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A19.D 1) 19 where
  n := 1
  w := ![![19, 0, 0, 0, 0], ![14, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C192 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A19.D 2) 19 where
  n := 3
  w := ![![19, 0, 0, 0, 0], ![17, 5, 16, 5, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K19 : KummerData 19 ![I19N0, I19N1, I19N2] ![19, 19, 6859] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A19
  C := by
    intro i
    match i with
    | 0 => exact C190
    | 1 => exact C191
    | 2 => exact C192
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 19 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![12, 1, 0, 0, 0]] i)))

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![21, 21, 9, 55, 10]] i)))

def P23P0 : CertificateIrreducibleZModOfList' 23 1 2 4 [12, 1] where
 m := 0
 P := ![]
 exp := ![]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1]]
 g := ![![[], [2], [13], [11, 1]]]
 h' := ![![[0, 1], [22], [5], [6], [0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[]]
 b := ![[]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def P23P1 : CertificateIrreducibleZModOfList' 23 4 2 4 [21, 21, 4, 11, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 14, 8, 7], [2, 11, 14, 5], [10, 20, 1, 11], [0, 1]]
 g := ![![[0, 6, 21, 13], [14, 20, 2, 4], [12, 1], []], ![[1, 16, 16, 10, 17, 22], [0, 18, 2, 22, 20, 21], [9, 12, 0, 14, 18, 22], [0, 10, 3]], ![[3, 17, 9, 14, 6, 21], [5, 5, 20, 3, 19, 7], [8, 13, 16, 3, 5, 11], [12, 3, 2]], ![[12, 16, 17, 16, 11, 14], [10, 15, 19, 4, 16, 21], [0, 13, 16, 5, 20, 19], [4, 2, 6]]]
 h' := ![![[0, 14, 8, 7], [5, 0, 17, 17], [1, 3, 0, 2], [0, 0, 1], [0, 1]], ![[2, 11, 14, 5], [0, 18, 18, 6], [18, 19, 11, 7], [0, 20, 15, 6], [0, 14, 8, 7]], ![[10, 20, 1, 11], [5, 14, 7, 8], [20, 3, 7, 12], [5, 5, 1, 4], [2, 11, 14, 5]], ![[0, 1], [4, 14, 4, 15], [7, 21, 5, 2], [16, 21, 6, 13], [10, 20, 1, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 9, 12], []]
 b := ![[], [], [13, 14, 19, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def A23 : FactorsPolyZMod [-300, 250, 0, -25, 0, 1] 23 2 where
 D := ![[12, 1], [21, 21, 4, 11, 1]]; D' := ![[12, 1], [21, 21, 4, 11, 1]]
 heqm := by decide
 hProd := by decide
 s := ![4, 4]
 n := ![1, 4]; t := 2
 hn := by intro i; fin_cases i <;> exact ⟨by decide⟩
 hirr := by
  intro i
  match i with
  | 0 => exact P23P0
  | 1 => exact P23P1

def C230 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A23.D 0) 23 where
  n := 1
  w := ![![23, 0, 0, 0, 0], ![12, 1, 0, 0, 0]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def C231 : PrimeIdealKummer Table ![0, 1, 0, 0, 0] ![1, 0, 0, 0, 0] (A23.D 1) 23 where
  n := 4
  w := ![![23, 0, 0, 0, 0], ![21, 21, 9, 55, 10]]
  hpmem := by decide
  hlen := by decide
  hpol := by decide

def K23 : KummerData 23 ![I23N0, I23N1] ![23, 279841] where
  a := ![0, 1, 0, 0, 0]
  z := ![1, 0, 0, 0, 0]
  heq := timesTableT_eq_Table
  A := A23
  C := by
    intro i
    match i with
    | 0 => exact C230
    | 1 => exact C231
  hmin := minpoly_hroot
  hcond := conductor_hroot_coprime 23 (by decide)
  hBz := B_one_repr
  hieq := by
    intro i
    fin_cases i <;> rfl
  hN := by decide


lemma PB1045I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)
  decide

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
    · exact ![I3N0, I3N1, I3N1]
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
    · convert (containsPrimesAbove_of_KummerData K3) <;> rfl
    · exact PBC5
    · convert (containsPrimesAbove_of_KummerData K7) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K11) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K13) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K17) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K19) <;> rfl
    · convert (containsPrimesAbove_of_KummerData K23) <;> rfl
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![3, 9, 9]
    · exact ![5, 5, 5, 5, 5]
    · exact ![49, 343]
    · exact ![161051]
    · exact ![169, 2197]
    · exact ![289, 4913]
    · exact ![19, 19, 6859]
    · exact ![23, 279841]
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
    · exact (card_quot_of_KummerData K3)
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · exact (card_quot_of_KummerData K7)
    · exact (card_quot_of_KummerData K11)
    · exact (card_quot_of_KummerData K13)
    · exact (card_quot_of_KummerData K17)
    · exact (card_quot_of_KummerData K19)
    · exact (card_quot_of_KummerData K23)
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N0, I7N1, I13N0, I17N0, I19N0, I19N1, I23N0]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1], [], [I13N0], [I17N0], [I19N0, I19N1], [I23N0]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
