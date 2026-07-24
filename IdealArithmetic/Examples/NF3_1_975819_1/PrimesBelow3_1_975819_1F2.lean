
import IdealArithmetic.Examples.NF3_1_975819_1.RI3_1_975819_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [69, 59, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 42, 6], [25, 40, 77], [0, 1]]
 g := ![![[71, 49, 31], [76, 61, 77], [72, 70], [63, 25], [55, 23, 1], []], ![[68, 58, 81, 45], [74, 78, 6, 39], [65, 40], [77, 81], [36, 71, 16, 55], [4, 36]], ![[75, 63, 37, 78], [8, 30, 42, 29], [23, 51], [73, 30], [49, 34, 36, 40], [16, 36]]]
 h' := ![![[81, 42, 6], [68, 0, 60], [12, 52, 49], [0, 38, 30], [23, 65, 5], [0, 0, 1], [0, 1]], ![[25, 40, 77], [16, 24, 76], [26, 29, 31], [64, 31, 17], [27, 76, 9], [60, 17, 40], [81, 42, 6]], ![[0, 1], [46, 59, 30], [2, 2, 3], [26, 14, 36], [0, 25, 69], [19, 66, 42], [25, 40, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 43], []]
 b := ![[], [28, 61, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [69, 59, 60, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-964045, 300626, -105410]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11615, 3622, -1270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4989009315, -1719269842, -546232628]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![4989009315, -1719269842, -546232628]] 
 ![![89, 0, 0], ![0, 89, 0], ![37, 80, 1]] where
  M :=![![![4989009315, -1719269842, -546232628], ![165123397572, -19752602861, -8050116582], ![420414187496, -30453937762, -15141025963]]]
  hmulB := by decide  
  f := ![![![605808127979291131, -105579492791451790, 34278724645082824]], ![![-9935343509361612324, 1731519403554617687, -562176188602341774]], ![![-8265257266909236705, 1440458834617961008, -467676917637586759]]]
  g := ![![![283141759, 471677982, -546232628], ![5201996754, 7014120491, -8050116582], ![11018338743, 13267731902, -15141025963]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [37, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 88], [0, 1]]
 g := ![![[], [], [34], [0, 88], [], [1]], ![[], [], [34], [0, 1], [], [1]]]
 h' := ![![[0, 88], [55], [77], [0, 37], [0, 34], [52], [0, 1]], ![[0, 1], [55], [77], [0, 52], [0, 55], [52], [0, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [0, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [37, 0, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9174, -7788, 5612]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2230, -5132, 5612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![605808127979291131, -105579492791451790, 34278724645082824]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![605808127979291131, -105579492791451790, 34278724645082824]] 
 ![![89, 0, 0], ![46, 1, 0], ![3, 0, 1]] where
  M :=![![![605808127979291131, -105579492791451790, 34278724645082824], ![-9935343509361612324, 1731519403554617687, -562176188602341774], ![36804683258773147328, -6414274770087169018, 2082536606574055881]]]
  hmulB := by decide  
  f := ![![![4989009315, -1719269842, -546232628]], ![![4433908158, -1110550737, -372773230]], ![![4891923769, -400131992, -188536223]]]
  g := ![![![60220546319672191, -105579492791451790, 34278724645082824], ![-987625927045696636, 1731519403554617687, -562176188602341774], ![3658581043405177017, -6414274770087169018, 2082536606574055881]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![4989009315, -1719269842, -546232628]] ![![605808127979291131, -105579492791451790, 34278724645082824]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![18, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![18, 1, 0]] 
 ![![97, 0, 0], ![18, 1, 0], ![44, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![18, 1, 0], ![-2, 20, 5], ![-296, 39, 17]]]
  hmulB := by decide  
  f := ![![![-3149, 31862, 7965], ![-194, -154521, 0]], ![![-590, 5900, 1475], ![1, -28615, 0]], ![![-1426, 14453, 3613], ![-101, -70092, 0]]]
  g := ![![![1, 0, 0], ![-18, 97, 0], ![-44, 0, 97]], ![![0, 1, 0], ![-6, 20, 5], ![-18, 39, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![35, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![35, 1, 0]] 
 ![![97, 0, 0], ![35, 1, 0], ![51, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![35, 1, 0], ![-2, 37, 5], ![-296, 39, 34]]]
  hmulB := by decide  
  f := ![![![7023, -137689, -18605], ![1164, 360937, 0]], ![![2509, -49659, -6710], ![486, 130174, 0]], ![![3699, -72393, -9782], ![594, 189771, 0]]]
  g := ![![![1, 0, 0], ![-35, 97, 0], ![-51, 0, 97]], ![![0, 1, 0], ![-16, 37, 5], ![-35, 39, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22698884875771343, 3955933638773195, -1284381619312970]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![-22698884875771343, 3955933638773195, -1284381619312970]] 
 ![![97, 0, 0], ![43, 1, 0], ![20, 0, 1]] where
  M :=![![![-22698884875771343, 3955933638773195, -1284381619312970], ![372265092039092730, -64877900751430783, 21064049813178945], ![-1379026179405566860, 240334980406123595, -78030083287063338]]]
  hmulB := by decide  
  f := ![![![-6322226379, 224902240, 164776235]], ![![-3310095921, 105408738, 82939310]], ![![-1714658150, 22981695, 34427273]]]
  g := ![![![-1722849473781024, 3955933638773195, -1284381619312970], ![28254987918423067, -64877900751430783, 21064049813178945], ![-104668336815748605, 240334980406123595, -78030083287063338]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![18, 1, 0]] ![![97, 0, 0], ![35, 1, 0]]
  ![![6322226379, -224902240, -164776235]] where
 M := ![![![9409, 0, 0], ![3395, 97, 0]], ![![1746, 97, 0], ![628, 55, 5]]]
 hmul := by decide  
 g := ![![![![2201791832949820271, -383725562960999915, 124585017073358090]], ![![422195878612904275, -73579776605631042, 23889306862775005]]], ![![![36314835724791444, -6328904746486727, 2054819334454515]], ![![6963407596516882, -1213574080943210, 394013748855875]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![6322226379, -224902240, -164776235]] ![![-22698884875771343, 3955933638773195, -1284381619312970]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [65, 99, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 7, 83], [69, 93, 18], [0, 1]]
 g := ![![[25, 48, 82], [6, 31], [72, 29, 13], [73, 76], [100, 65], [1]], ![[66, 38, 76, 53], [48, 56], [34, 75, 1, 50], [80, 30], [45, 20], [61, 42, 82, 26]], ![[57, 25, 35, 26], [78, 37], [27, 17, 57, 91], [42, 68], [22, 78], [78, 61, 57, 75]]]
 h' := ![![[92, 7, 83], [59, 76, 53], [67, 63, 43], [84, 67, 66], [48, 58, 51], [36, 2, 60], [0, 1]], ![[69, 93, 18], [54, 77, 26], [89, 89, 37], [75, 72, 84], [86, 12, 63], [53, 2, 90], [92, 7, 83]], ![[0, 1], [100, 49, 22], [25, 50, 21], [82, 63, 52], [40, 31, 88], [37, 97, 52], [69, 93, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 53], []]
 b := ![[], [94, 66, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [65, 99, 41, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26410484849, 18579167655, -9914498855]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-261489949, 183952155, -98163355]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-47, -14, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-47, -14, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![56, 89, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-47, -14, 1], ![-268, -36, -71], ![4306, -613, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -89, 103]], ![![-1, -1, 1], ![36, 61, -71], ![38, -12, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [18, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 102], [0, 1]]
 g := ![![[48, 63], [5, 13], [59, 49], [2], [30], [63, 1]], ![[0, 40], [0, 90], [56, 54], [2], [30], [23, 102]]]
 h' := ![![[63, 102], [13, 75], [71, 61], [25, 96], [79, 65], [102, 37], [0, 1]], ![[0, 1], [0, 28], [0, 42], [99, 7], [54, 38], [64, 66], [63, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [69, 91]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [18, 40, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2241, -6972, 5133]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2769, -4503, 5133]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-32, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-32, 1, 0]] 
 ![![103, 0, 0], ![71, 1, 0], ![96, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-32, 1, 0], ![-2, -30, 5], ![-296, 39, -33]]]
  hmulB := by decide  
  f := ![![![6785, 106570, -17760], ![-1030, 365856, 0]], ![![4673, 73447, -12240], ![-720, 252144, 0]], ![![6336, 99327, -16553], ![-921, 340992, 0]]]
  g := ![![![1, 0, 0], ![-71, 103, 0], ![-96, 0, 103]], ![![-1, 1, 0], ![16, -30, 5], ![1, 39, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-47, -14, 1]] ![![103, 0, 0], ![-32, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-3296, 103, 0]], ![![-4841, -1442, 103], ![1236, 412, -103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-32, 1, 0]]], ![![![-47, -14, 1]], ![![12, 4, -1]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1231247219317964020856225, -24679367175807074990785, -26928572011655120030116]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![1231247219317964020856225, -24679367175807074990785, -26928572011655120030116]] 
 ![![107, 0, 0], ![0, 107, 0], ![58, 82, 1]] where
  M :=![![![1231247219317964020856225, -24679367175807074990785, -26928572011655120030116], ![8020216049801529678895906, 131674176511800189700131, -96468263867380254923809], ![2942664018150764752393568, 841719004924417117377157, 178783706027566294642370]]]
  hmulB := by decide  
  f := ![![![-978881947048083836065470860663166131655506369, 170598337491401830115131912680218491945326166, -55388535038029145138756476616948265731600423]], ![![16053809696273823300841653253256249672663072876, -2797838138548416836246709623363711511297270534, 908380222495038295714416040018040725458231253]], ![![11216515809271485840660380013862229391196418624, -1954800530623890189969772987406613237417404835, 634669360059128956624330633641822661890441951]]]
  g := ![![![26103779401812719463579, 20406201287662736144661, -26928572011655120030116], ![127246498636538172565204, 75159549660158701807967, -96468263867380254923809], ![-69409261041570844269756, -129145279339588963021469, 178783706027566294642370]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [18, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 106], [0, 1]]
 g := ![![[86, 61], [27, 85], [87], [0, 13], [13], [57, 1]], ![[32, 46], [57, 22], [87], [99, 94], [13], [7, 106]]]
 h' := ![![[57, 106], [49, 32], [39, 37], [0, 80], [97, 21], [44, 21], [0, 1]], ![[0, 1], [54, 75], [8, 70], [66, 27], [10, 86], [64, 86], [57, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [8, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [18, 50, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4726, -649, 745]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-448, -577, 745]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![370115725060972757883845, -35186306990391408579199, -15590601806727889079316]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![370115725060972757883845, -35186306990391408579199, -15590601806727889079316]] 
 ![![107, 0, 0], ![19, 1, 0], ![91, 0, 1]] where
  M :=![![![370115725060972757883845, -35186306990391408579199, -15590601806727889079316], ![4685190748772237984635934, -308290359382197733367877, -160340933145229153816679], ![7889469376465938908593712, -327695651574496366274589, -218322040217751396709596]]]
  hmulB := by decide  
  f := ![![![-14763553678696576618681121794759537307321977761, 2572973912376164333993116104499008673912992480, -835373062792975864974377176419201314039127989]], ![![-358720010591275031687027122330333058237025025, 62517280675484258515641182424026108386213764, -20297622134511625229656155635986731618124686]], ![![-20938449523338272946614893017147056778681163407, 3649127138467577068900825835560351548124398109, -1184770082401425974432875215048354374956642400]]]
  g := ![![![22966358152249041374826, -35186306990391408579199, -15590601806727889079316], ![234894696198596709494798, -308290359382197733367877, -160340933145229153816679], ![317598059964455579143777, -327695651574496366274589, -218322040217751396709596]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![1231247219317964020856225, -24679367175807074990785, -26928572011655120030116]] ![![370115725060972757883845, -35186306990391408579199, -15590601806727889079316]]
  ![![107, 0, 0]] where
 M := ![![![127624270291619401747742770094799164694717086343, -26890255712702812809770313950325263701509128006, -9359671577889510564634179112520118890926845949]]]
 hmul := by decide  
 g := ![![![![1192750189641302820072362337334571632660907349, -251310801053297315979161812619862277584197458, -87473566148500098734898870210468400849783607]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-29, 32, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-29, 32, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![80, 32, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-29, 32, 1], ![-360, 74, 159], ![-9310, 1181, -21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-80, -32, 109]], ![![-1, 0, 1], ![-120, -46, 159], ![-70, 17, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [11, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [103, 108], [0, 1]]
 g := ![![[60, 64], [93], [33, 31], [32, 87], [80], [103, 1]], ![[3, 45], [93], [65, 78], [55, 22], [80], [97, 108]]]
 h' := ![![[103, 108], [55, 8], [73, 86], [84, 85], [97, 95], [66, 25], [0, 1]], ![[0, 1], [7, 101], [102, 23], [10, 24], [72, 14], [25, 84], [103, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [28, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [11, 6, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-99616, 11122, 4837]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4464, -1318, 4837]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-50, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-50, 1, 0]] 
 ![![109, 0, 0], ![59, 1, 0], ![21, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-50, 1, 0], ![-2, -48, 5], ![-296, 39, -51]]]
  hmulB := by decide  
  f := ![![![10391, 273380, -28475], ![-2180, 620755, 0]], ![![5615, 147947, -15410], ![-1198, 335938, 0]], ![![2029, 52669, -5486], ![-361, 119595, 0]]]
  g := ![![![1, 0, 0], ![-59, 109, 0], ![-21, 0, 109]], ![![-1, 1, 0], ![25, -48, 5], ![-14, 39, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-29, 32, 1]] ![![109, 0, 0], ![-50, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-5450, 109, 0]], ![![-3161, 3488, 109], ![1090, -1526, 109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-50, 1, 0]]], ![![![-29, 32, 1]], ![![10, -14, 1]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [33, 4, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 36, 1], [109, 76, 112], [0, 1]]
 g := ![![[77, 66, 13], [111, 63], [12, 61], [45, 36], [25, 75, 91], [1]], ![[43, 45, 66, 31], [7, 32], [6, 44], [93, 56], [65, 54, 51, 7], [46, 37, 49, 1]], ![[3, 50, 23, 85], [19, 52], [111, 106], [28, 49], [68, 6, 82, 62], [77, 83, 61, 112]]]
 h' := ![![[58, 36, 1], [107, 25, 37], [43, 27, 96], [10, 14, 20], [79, 96, 6], [80, 109, 54], [0, 1]], ![[109, 76, 112], [90, 56, 12], [78, 16, 91], [84, 60, 65], [92, 91, 100], [25, 81, 32], [58, 36, 1]], ![[0, 1], [25, 32, 64], [55, 70, 39], [92, 39, 28], [98, 39, 7], [107, 36, 27], [109, 76, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 100], []]
 b := ![[], [47, 59, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [33, 4, 59, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10844497, 2161690, -698905]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-95969, 19130, -6185]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73805718346865075619288612529514873, -12862769494629718442354350632801904, 4176183480541234084524449259898347]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![73805718346865075619288612529514873, -12862769494629718442354350632801904, 4176183480541234084524449259898347]] 
 ![![127, 0, 0], ![13, 1, 0], ![113, 0, 1]] where
  M :=![![![73805718346865075619288612529514873, -12862769494629718442354350632801904, 4176183480541234084524449259898347], ![-1210424771250945852134528279664306904, 210951335098713768031033432399946598, -68490030953689826296296202423907867], ![4483921494258076580629848567412895798, -781452303486821702914957775092463505, 253715827063144157442620933558250657]]]
  hmulB := by decide  
  f := ![![![-9806448733081478949, 886163678551524693, 400632897649705262]], ![![-1951523610956496325, 150477869712833832, 72743410744520367]], ![![-10279768710789025023, 849247834624421266, 398458432510014972]]]
  g := ![![![-1818007964756756190404469256791918, -12862769494629718442354350632801904, 4176183480541234084524449259898347], ![29815601340415161692468566716834459, 210951335098713768031033432399946598, -68490030953689826296296202423907867], ![-110449504083059299783400518491869314, -781452303486821702914957775092463505, 253715827063144157442620933558250657]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![51, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![51, 1, 0]] 
 ![![127, 0, 0], ![51, 1, 0], ![94, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![51, 1, 0], ![-2, 53, 5], ![-296, 39, 50]]]
  hmulB := by decide  
  f := ![![![-1198, 33126, 3125], ![-127, -79375, 0]], ![![-500, 13250, 1250], ![1, -31750, 0]], ![![-910, 24518, 2313], ![-36, -58750, 0]]]
  g := ![![![1, 0, 0], ![-51, 127, 0], ![-94, 0, 127]], ![![0, 1, 0], ![-25, 53, 5], ![-55, 39, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![62, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![62, 1, 0]] 
 ![![127, 0, 0], ![62, 1, 0], ![95, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![62, 1, 0], ![-2, 64, 5], ![-296, 39, 61]]]
  hmulB := by decide  
  f := ![![![7869, -279566, -21840], ![1778, 554736, 0]], ![![3830, -136455, -10660], ![890, 270764, 0]], ![![5897, -209124, -16337], ![1308, 414960, 0]]]
  g := ![![![1, 0, 0], ![-62, 127, 0], ![-95, 0, 127]], ![![0, 1, 0], ![-35, 64, 5], ![-67, 39, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![73805718346865075619288612529514873, -12862769494629718442354350632801904, 4176183480541234084524449259898347]] ![![127, 0, 0], ![51, 1, 0]]
  ![![127, 0, 0], ![-71, 64, 1]] where
 M := ![![![9373326230051864603649653791248388871, -1633571725817974242179002530365841808, 530375302028736728734605056007090069], ![2553666864439173004449190959340951619, -445049909127401872529038449872950506, 144495326553913112014450709830907830]]]
 hmul := by decide  
 g := ![![![![56779298837504017354401968719830975, 2484988936343629852754736744941328, 4415992206025192651635528750175585], ![-30455708136462738023107095265209226, 0, 0]], ![![15468939250460865954805951688815544, 677009820152558595378032175906474, 1203091911384992123900946600072733], ![-8297346191980887720969508378329261, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-71, 64, 1]] ![![127, 0, 0], ![62, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![7874, 127, 0]], ![![-9017, 8128, 127], ![-4826, 4064, 381]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![62, 1, 0]]], ![![![-71, 64, 1]], ![![-38, 32, 3]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39250801, 1784473, 1127786]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-39250801, 1784473, 1127786]] 
 ![![131, 0, 0], ![81, 1, 0], ![96, 0, 1]] where
  M :=![![![-39250801, 1784473, 1127786], ![-337393602, 8301799, 7794579], ![-345502676, -5967215, 4076166]]]
  hmulB := by decide  
  f := ![![![-80351439550119, 14003549706508, -4546563084853]], ![![-39623595647757, 6905551341838, -2242040444700]], ![![-96147573509038, 16756480435601, -5440363120585]]]
  g := ![![![-2229470, 1784473, 1127786], ![-13420755, 8301799, 7794579], ![-1934887, -5967215, 4076166]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-359575300432029177185269729, 62666339533241266183902121, -20346017399594549806077682]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-359575300432029177185269729, 62666339533241266183902121, -20346017399594549806077682]] 
 ![![131, 0, 0], ![99, 1, 0], ![122, 0, 1]] where
  M :=![![![-359575300432029177185269729, 62666339533241266183902121, -20346017399594549806077682], ![5897088471213504210231189630, -1027737299949734087254495085, 333677715065800880725588287], ![-21845291320573731859019612300, 3807170407569244218179387413, -1236082335949052435612279130]]]
  hmulB := by decide  
  f := ![![![-548902525044519, 61957399981936, 25760245136243]], ![![-473971735417551, 51247667430874, 21635809337874]], ![![-619330830061168, 62971030327965, 27193128145381]]]
  g := ![![![-31155181614292972924046584, 62666339533241266183902121, -20346017399594549806077682], ![510949617772591384732094901, -1027737299949734087254495085, 333677715065800880725588287], ![-1892771883085072613084587117, 3807170407569244218179387413, -1236082335949052435612279130]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-39250801, 1784473, 1127786]] ![![-39250801, 1784473, 1127786]]
  ![![548902525044519, -61957399981936, -25760245136243]] where
 M := ![![![548902525044519, -61957399981936, -25760245136243]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI131N1 : IdealMulLeCertificate' Table 
  ![![548902525044519, -61957399981936, -25760245136243]] ![![-359575300432029177185269729, 62666339533241266183902121, -20346017399594549806077682]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![8, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![8, 1, 0]] 
 ![![137, 0, 0], ![8, 1, 0], ![11, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![8, 1, 0], ![-2, 10, 5], ![-296, 39, 7]]]
  hmulB := by decide  
  f := ![![![9585, -48002, -24000], ![274, 657600, 0]], ![![552, -2801, -1400], ![138, 38360, 0]], ![![763, -3855, -1927], ![135, 52800, 0]]]
  g := ![![![1, 0, 0], ![-8, 137, 0], ![-11, 0, 137]], ![![0, 1, 0], ![-1, 10, 5], ![-5, 39, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22831, -386, -480]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![22831, -386, -480]] 
 ![![137, 0, 0], ![130, 1, 0], ![20, 0, 1]] where
  M :=![![![22831, -386, -480], ![142852, 3339, -1450], ![36496, 17106, 4017]]]
  hmulB := by decide  
  f := ![![![38216463, -6660318, 2162420]], ![![31688938, -5522709, 1793070]], ![![22526244, -3925846, 1274613]]]
  g := ![![![603, -386, -480], ![-1914, 3339, -1450], ![-16552, 17106, 4017]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-2, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-2, 1, 0]] 
 ![![137, 0, 0], ![135, 1, 0], ![27, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-2, 1, 0], ![-2, 0, 5], ![-296, 39, -3]]]
  hmulB := by decide  
  f := ![![![-18491, -2, 46240], ![274, -1266976, 0]], ![![-18219, -2, 45560], ![275, -1248344, 0]], ![![-3643, -1, 9113], ![137, -249696, 0]]]
  g := ![![![1, 0, 0], ![-135, 137, 0], ![-27, 0, 137]], ![![-1, 1, 0], ![-1, 0, 5], ![-40, 39, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![8, 1, 0]] ![![22831, -386, -480]]
  ![![137, 0, 0], ![-39, 28, 1]] where
 M := ![![![3127847, -52882, -65760]], ![![325500, 251, -5290]]]
 hmul := by decide  
 g := ![![![![21193, 790, -438], ![-5754, 0, 0]]], ![![![2235, 103, -35], ![-495, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-39, 28, 1]] ![![137, 0, 0], ![-2, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-274, 137, 0]], ![![-5343, 3836, 137], ![-274, 0, 137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-2, 1, 0]]], ![![![-39, 28, 1]], ![![-2, 0, 1]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB280I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB280I2 : PrimesBelowBoundCertificateInterval O 79 137 280 where
  m := 11
  g := ![1, 2, 3, 1, 2, 2, 2, 1, 3, 3, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB280I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![97, 97, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![127, 127, 127]
    · exact ![131, 131, 131]
    · exact ![137, 137, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I89N1, I97N0, I97N1, I97N2, I103N1, I107N1, I109N1, I127N0, I127N1, I127N2, I131N0, I131N1, I137N0, I137N1, I137N2]
  Il := ![[], [I89N1], [I97N0, I97N1, I97N2], [], [I103N1], [I107N1], [I109N1], [], [I127N0, I127N1, I127N2], [I131N0, I131N0, I131N1], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
