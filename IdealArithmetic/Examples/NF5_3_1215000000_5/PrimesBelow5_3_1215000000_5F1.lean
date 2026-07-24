
import IdealArithmetic.Examples.NF5_3_1215000000_5.RI5_3_1215000000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1364, 552, -120, -23, -225]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-1364, 552, -120, -23, -225]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![4, 15, 7, 1, 0], ![13, 8, 10, 0, 1]] where
  M :=![![![-1364, 552, -120, -23, -225], ![1488, -883, 276, 72, 476], ![-3288, 796, -19, 32, -120], ![-480, -764, 452, 161, 730], ![249, 236, -148, -53, -230]]]
  hmulB := by decide  
  f := ![![![12356, 4400, -3344, -1227, -5131]], ![![38148, 13585, -10324, -3788, -15840]], ![![117768, 41940, -31871, -11696, -48904]], ![![55474, 19755, -15013, -5509, -23036]], ![![54577, 19436, -14770, -5420, -22663]]]
  g := ![![![57, 93, 79, -23, -225], ![-172, -199, -172, 72, 476], ![-64, 44, 33, 32, -120], ![-366, -311, -275, 161, 730], ![119, 99, 87, -53, -230]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [4, 28, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 20, 14], [4, 8, 15], [0, 1]]
 g := ![![[15, 12, 13], [5, 22], [13, 12, 4], [1]], ![[25, 1, 22, 12], [22, 23], [9, 22, 26, 14], [2, 26, 22, 18]], ![[24, 15, 5, 15], [28, 25], [28, 19, 5, 19], [25, 21, 28, 11]]]
 h' := ![![[27, 20, 14], [16, 8, 10], [6, 10, 14], [25, 1, 2], [0, 1]], ![[4, 8, 15], [8, 25, 18], [3, 11, 20], [13, 22, 1], [27, 20, 14]], ![[0, 1], [13, 25, 1], [26, 8, 24], [22, 6, 26], [4, 8, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6], []]
 b := ![[], [26, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [4, 28, 27, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1242456562, 1198858908, 139545354, 263133138, 1986110128]
  a := ![33, -74, -69, -37, -209]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-883776126, -642655834, -743568548, 263133138, 1986110128]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12356, 4400, -3344, -1227, -5131]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![12356, 4400, -3344, -1227, -5131]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![8, 15, 1, 0, 0], ![27, 8, 0, 1, 0], ![28, 27, 0, 0, 1]] where
  M :=![![![12356, 4400, -3344, -1227, -5131], ![38148, 13585, -10324, -3788, -15840], ![117768, 41940, -31871, -11696, -48904], ![162726, 57940, -44044, -16161, -67592], ![-60759, -21636, 16444, 6035, 25236]]]
  hmulB := by decide  
  f := ![![![-1364, 552, -120, -23, -225]], ![![1488, -883, 276, 72, 476]], ![![280, -277, 109, 32, 180]], ![![-876, 244, -20, 4, -53]], ![![77, -281, 136, 43, 218]]]
  g := ![![![7445, 6997, -3344, -1227, -5131], ![22984, 21601, -10324, -3788, -15840], ![70960, 66689, -31871, -11696, -48904], ![98069, 92168, -44044, -16161, -67592], ![-36616, -34412, 16444, 6035, 25236]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [20, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 28], [0, 1]]
 g := ![![[2, 16], [1], [2, 22], [18, 1]], ![[0, 13], [1], [21, 7], [7, 28]]]
 h' := ![![[18, 28], [14, 25], [18, 1], [17, 14], [0, 1]], ![[0, 1], [0, 4], [7, 28], [8, 15], [18, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [16, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [20, 11, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2356987, -2333239, -282677, -479919, -3864789]
  a := ![-45, 35, 95, -17, 286]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4175046, 3796399, -282677, -479919, -3864789]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-1364, 552, -120, -23, -225]] ![![12356, 4400, -3344, -1227, -5131]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [30, 30, 27, 14, 7, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 16, 26, 22, 17], [21, 6, 30, 25, 13], [0, 19, 13, 19, 20], [13, 20, 24, 27, 12], [0, 1]]
 g := ![![[21, 18, 14, 13, 14], [16, 2, 11, 7, 20], [4, 24, 1], []], ![[8, 19, 12, 0, 6, 22, 25, 22], [2, 11, 7, 0, 7, 11, 8, 21], [13, 27, 17, 0, 10, 1, 24, 15], [5, 5, 8, 18, 2, 10, 28, 15]], ![[0, 19, 27, 20, 25, 16, 25, 21], [7, 15, 14, 25, 28, 17, 7, 17], [30, 26, 17, 24, 14, 29, 17, 29], [26, 27, 1, 18, 20, 10, 24, 27]], ![[13, 29, 14, 2, 28, 8, 18, 10], [21, 2, 29, 20, 18, 20, 16, 7], [20, 23, 30, 18, 16, 17, 21, 10], [18, 21, 1, 11, 1, 25, 1, 2]], ![[20, 27, 7, 24, 7, 21, 25, 17], [19, 30, 10, 27, 22, 29], [23, 13, 2, 24, 19, 4, 6, 15], [27, 26, 7, 0, 12, 6, 2, 23]]]
 h' := ![![[21, 16, 26, 22, 17], [16, 3, 22, 15, 13], [4, 28, 10, 10, 12], [0, 0, 0, 1], [0, 1]], ![[21, 6, 30, 25, 13], [15, 13, 20, 2, 26], [16, 19, 7, 23, 18], [28, 5, 29, 3, 14], [21, 16, 26, 22, 17]], ![[0, 19, 13, 19, 20], [0, 26, 8, 1, 29], [14, 25, 4, 19, 7], [18, 24, 23, 27, 10], [21, 6, 30, 25, 13]], ![[13, 20, 24, 27, 12], [21, 28, 29, 6, 27], [20, 30, 21, 4, 25], [18, 8, 1, 7, 4], [0, 19, 13, 19, 20]], ![[0, 1], [15, 23, 14, 7, 29], [18, 22, 20, 6], [23, 25, 9, 24, 3], [13, 20, 24, 27, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 19, 23], [], [], []]
 b := ![[], [8, 12, 5, 26], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [30, 30, 27, 14, 7, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1724883582466, 364287650368, -580777550328, 250613710688, 126151770729]
  a := ![4, -12, -8, -8, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![55641405886, 11751214528, -18734759688, 8084313248, 4069411959]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 28629151 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀

instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-567011, -201911, 153457, 56308, 235458]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-567011, -201911, 153457, 56308, 235458]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![29, 11, 1, 0, 0], ![7, 10, 0, 1, 0], ![17, 14, 0, 0, 1]] where
  M :=![![![-567011, -201911, 153457, 56308, 235458], ![-1750596, -623382, 473785, 173846, 726956], ![-5404812, -1924637, 1462770, 536734, 2244412], ![-7468140, -2659383, 2021193, 741637, 3101232], ![2788554, 992996, -754700, -276922, -1157979]]]
  hmulB := by decide  
  f := ![![![-14267, 6437, -1597, -352, -2898]], ![![19500, -8848, 2213, 490, 4012]], ![![-6115, 2740, -674, -148, -1226]], ![![2803, -1280, 322, 73, 586]], ![![767, -363, 97, 22, 175]]]
  g := ![![![-254438, -155390, 153457, 56308, 235458], ![-785555, -479753, 473785, 173846, 726956], ![-2425332, -1481195, 1462770, 536734, 2244412], ![-3351220, -2046652, 2021193, 741637, 3101232], ![1251323, 764206, -754700, -276922, -1157979]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [17, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 36], [0, 1]]
 g := ![![[33, 10], [34], [6, 33], [36], [1]], ![[10, 27], [34], [30, 4], [36], [1]]]
 h' := ![![[31, 36], [21, 26], [9, 21], [10, 25], [20, 31], [0, 1]], ![[0, 1], [13, 11], [31, 16], [8, 12], [19, 6], [31, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [21, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [17, 6, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1321536, 151894, 724273, 7956, 1147020]
  a := ![-53, 134, 111, 72, 336]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1131905, -647377, 724273, 7956, 1147020]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-680, 306, -76, -17, -139]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-680, 306, -76, -17, -139]] 
 ![![37, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-680, 306, -76, -17, -139], ![936, -421, 102, 24, 188], ![-1272, 598, -133, -28, -216], ![264, -242, 80, -13, 22], ![-69, 44, -28, 1, -38]]]
  hmulB := by decide  
  f := ![![![-429632, -152954, 116304, 42675, 178439]], ![![-47468, -16899, 12850, 4715, 19715]], ![![-528744, -188238, 143135, 52520, 219604]], ![![-153030, -54478, 41428, 15201, 63560]], ![![-291225, -103680, 78836, 28927, 120954]]]
  g := ![![![160, 306, -76, -17, -139], ![-215, -421, 102, 24, 188], ![254, 598, -133, -28, -216], ![-82, -242, 80, -13, 22], ![55, 44, -28, 1, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5192, -1714, 1506, 551, 2263]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-5192, -1714, 1506, 551, 2263]] 
 ![![37, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![-5192, -1714, 1506, 551, 2263], ![-16884, -5575, 4898, 1792, 7360], ![-54912, -18130, 15929, 5828, 23936], ![-80850, -26694, 23454, 8581, 35244], ![28143, 9292, -8164, -2987, -12268]]]
  hmulB := by decide  
  f := ![![![-248, -62, 54, 19, 77]], ![![-96, -27, 22, 8, 32]], ![![-80, -22, 21, 8, 36]], ![![-140, -44, 36, 8, 41]], ![![-197, -48, 40, 15, 56]]]
  g := ![![![-1931, -1714, 1506, 551, 2263], ![-6280, -5575, 4898, 1792, 7360], ![-20424, -18130, 15929, 5828, 23936], ![-30073, -26694, 23454, 8581, 35244], ![10468, 9292, -8164, -2987, -12268]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2

def I37N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -7, 1, 0, 2]] i)))

def SI37N3: IdealEqSpanCertificate' Table ![![23, -7, 1, 0, 2]] 
 ![![37, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![23, -7, 1, 0, 2], ![-12, 16, -7, -2, -12], ![84, 3, -8, -2, -4], ![24, 25, -7, -9, -20], ![-18, -12, 4, 2, 3]]]
  hmulB := by decide  
  f := ![![![4343, 1437, -1257, -460, -1890]], ![![1907, 631, -552, -202, -830]], ![![3116, 1031, -902, -330, -1356]], ![![4049, 1340, -1172, -429, -1762]], ![![774, 256, -224, -82, -337]]]
  g := ![![![2, -7, 1, 0, 2], ![2, 16, -7, -2, -12], ![7, 3, -8, -2, -4], ![6, 25, -7, -9, -20], ![0, -12, 4, 2, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N3 : Nat.card (O ⧸ I37N3) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N3)

lemma isPrimeI37N3 : Ideal.IsPrime I37N3 := prime_ideal_of_norm_prime hp37.out _ NI37N3
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-567011, -201911, 153457, 56308, 235458]] ![![-680, 306, -76, -17, -139]]
  ![![190, 67, -51, -19, -79]] where
 M := ![![![190, 67, -51, -19, -79]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![190, 67, -51, -19, -79]] ![![-5192, -1714, 1506, 551, 2263]]
  ![![-4343, -1437, 1257, 460, 1890]] where
 M := ![![![-4343, -1437, 1257, 460, 1890]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N2 : IdealMulLeCertificate' Table 
  ![![-4343, -1437, 1257, 460, 1890]] ![![23, -7, 1, 0, 2]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2, I37N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
    exact isPrimeI37N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1 ⊙ MulI37N2)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![44, 12, 14, 5, 57]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![44, 12, 14, 5, 57]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![38, 11, 0, 1, 0], ![37, 5, 6, 0, 1]] where
  M :=![![![44, 12, 14, 5, 57], ![-372, -105, 72, -56, -152], ![1248, -420, -777, 112, -1216], ![3498, 3448, 426, 803, 5852], ![-1863, -612, 500, -301, -600]]]
  hmulB := by decide  
  f := ![![![12604, 4308, -3546, -1299, -5377]], ![![40056, 13679, -11280, -4132, -17100]], ![![127392, 43460, -35905, -13152, -54416]], ![![26884, 9181, -7570, -2773, -11476]], ![![33305, 11371, -9380, -3436, -14219]]]
  g := ![![![-55, -8, -8, 5, 57], ![180, 31, 24, -56, -152], ![1024, 108, 159, 112, -1216], ![-5940, -845, -846, 803, 5852], ![775, 139, 100, -301, -600]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [16, 10, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 26, 38], [21, 14, 3], [0, 1]]
 g := ![![[14, 37, 20], [1, 4], [34, 8], [35, 2, 1], []], ![[35, 26, 7, 17], [10, 37], [36, 37], [19, 21, 21, 27], [26, 9]], ![[36, 11, 32, 28], [10, 10], [25, 10], [18, 3, 6, 19], [20, 9]]]
 h' := ![![[22, 26, 38], [15, 37, 26], [21, 29, 2], [14, 28, 34], [0, 0, 1], [0, 1]], ![[21, 14, 3], [14, 30, 7], [16, 20, 23], [31, 17, 23], [27, 2, 14], [22, 26, 38]], ![[0, 1], [2, 15, 8], [11, 33, 16], [1, 37, 25], [39, 39, 26], [21, 14, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 15], []]
 b := ![[], [25, 4, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [16, 10, 39, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![843475829, 7189042192, 3900747126, 808442623, 14420889067]
  a := ![59, -126, -123, -55, -374]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13742688764, -1800201756, -2015233836, 808442623, 14420889067]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12604, 4308, -3546, -1299, -5377]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![12604, 4308, -3546, -1299, -5377]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![35, 0, 1, 0, 0], ![0, 18, 0, 1, 0], ![24, 18, 0, 0, 1]] where
  M :=![![![12604, 4308, -3546, -1299, -5377], ![40056, 13679, -11280, -4132, -17100], ![127392, 43460, -35905, -13152, -54416], ![182676, 62248, -51542, -18879, -78090], ![-65475, -22340, 18452, 6759, 27966]]]
  hmulB := by decide  
  f := ![![![44, 12, 14, 5, 57]], ![![-372, -105, 72, -56, -152]], ![![68, 0, -7, 7, 19]], ![![-78, 38, 42, -5, 76]], ![![-183, -54, 52, -29, -48]]]
  g := ![![![6482, 3036, -3546, -1299, -5377], ![20616, 9655, -11280, -4132, -17100], ![65611, 30724, -35905, -13152, -54416], ![94166, 44090, -51542, -18879, -78090], ![-33719, -15790, 18452, 6759, 27966]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [6, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 40], [0, 1]]
 g := ![![[39, 33], [40], [2], [26, 21], [1]], ![[25, 8], [40], [2], [32, 20], [1]]]
 h' := ![![[12, 40], [4, 22], [11, 9], [8, 17], [35, 12], [0, 1]], ![[0, 1], [22, 19], [37, 32], [7, 24], [15, 29], [12, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [37, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [6, 29, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1466688, -646462, 293596, -249712, -804802]
  a := ![-42, 82, 88, 24, 266]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![184700, 447190, 293596, -249712, -804802]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![44, 12, 14, 5, 57]] ![![12604, 4308, -3546, -1299, -5377]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20564, -974, 8926, -2751, 5135]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-20564, -974, 8926, -2751, 5135]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![9, 8, 42, 12, 1]] where
  M :=![![![-20564, -974, 8926, -2751, 5135], ![-14304, -67941, -33986, -8924, -135348], ![865632, 377090, -175029, 149180, 472976], ![-1859316, 402990, 1100618, -196003, 1483166], ![-181371, -402764, -156764, -64625, -766618]]]
  hmulB := by decide  
  f := ![![![664180, -288462, 68582, 14531, 125803]], ![![-842004, 418453, -114090, -27256, -202640]], ![![1379376, -499862, 91381, 13564, 180112]], ![![-160026, 254094, -111502, -34411, -181300]], ![![1285389, -401498, 52068, 1872, 115241]]]
  g := ![![![-1553, -978, -4808, -1497, 5135], ![27996, 23601, 131410, 37564, -135348], ![-78864, -79226, -466047, -128524, 472976], ![-353670, -266566, -1423078, -418465, 1483166], ![156237, 133260, 745144, 212437, -766618]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [18, 2, 16, 25, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 16, 15, 24], [36, 32, 13, 1], [21, 37, 15, 18], [0, 1]]
 g := ![![[38, 41, 41, 14], [25, 21, 40, 35], [29, 4, 6], [18, 1], []], ![[5, 18, 6, 12, 13, 24], [19, 39, 31, 30, 28, 23], [5, 9, 21], [18, 21, 15, 13, 22, 17], [11, 37, 17]], ![[11, 20, 35, 31, 36, 38], [34, 9, 24, 32, 13, 24], [42, 42, 31], [3, 41, 6, 27, 16, 1], [20, 1, 1]], ![[2, 20, 33, 12], [39, 32, 32, 9, 14, 2], [9, 22, 41], [36, 11, 28, 1, 24, 8], [0, 8, 23]]]
 h' := ![![[4, 16, 15, 24], [23, 8, 17, 33], [7, 32, 24, 11], [20, 32, 11, 7], [0, 0, 1], [0, 1]], ![[36, 32, 13, 1], [15, 1, 25, 1], [10, 7, 15, 32], [33, 19, 15, 35], [33, 42, 35, 29], [4, 16, 15, 24]], ![[21, 37, 15, 18], [14, 2, 13, 9], [31, 19, 0, 14], [20, 29, 0, 17], [33, 10, 29, 42], [36, 32, 13, 1]], ![[0, 1], [33, 32, 31], [11, 28, 4, 29], [1, 6, 17, 27], [11, 34, 21, 15], [21, 37, 15, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [27, 31, 29], []]
 b := ![[], [], [14, 2, 8, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [18, 2, 16, 25, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![68005265832584, -21617602816466, -44334245134584, 6742558058144, -67678087288864]
  a := ![-65, 150, 140, 80, 416]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![15746698870520, 12088537104522, 65073149325528, 19043711756384, -67678087288864]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-664180, 288462, -68582, -14531, -125803]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-664180, 288462, -68582, -14531, -125803]] 
 ![![43, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![-664180, 288462, -68582, -14531, -125803], ![842004, -418453, 114090, 27256, 202640], ![-1379376, 499862, -91381, -13564, -180112], ![160026, -254094, 111502, 34411, 181300], ![-16659, 70804, -34428, -11009, -55152]]]
  hmulB := by decide  
  f := ![![![20564, 974, -8926, 2751, -5135]], ![![11332, 2101, -3984, 1679, 401]], ![![-5784, -8090, -2157, -1550, -14582]], ![![47544, -9168, -27464, 5134, -35567]], ![![22869, 10250, -4450, 3998, 13171]]]
  g := ![![![-4750, 288462, -68582, -14531, -125803], ![-25687, -418453, 114090, 27256, 202640], ![-69496, 499862, -91381, -13564, -180112], ![-109797, -254094, 111502, 34411, 181300], ![38086, 70804, -34428, -11009, -55152]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-20564, -974, 8926, -2751, 5135]] ![![-664180, 288462, -68582, -14531, -125803]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![653050, -295103, 73337, 16209, 133081]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![653050, -295103, 73337, 16209, 133081]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![23, 33, 1, 0, 0], ![20, 8, 0, 1, 0], ![39, 28, 0, 0, 1]] where
  M :=![![![653050, -295103, 73337, 16209, 133081], ![-895740, 404780, -100595, -22234, -182544], ![1228668, -555201, 137972, 30494, 250372], ![-394728, 178397, -44339, -9801, -80458], ![98127, -44352, 11024, 2437, 20004]]]
  hmulB := by decide  
  f := ![![![-130, -33, 45, 23, 93]], ![![-696, -158, 243, 42, 316]], ![![-598, -152, 200, 43, 261]], ![![-154, -31, 59, 37, 152]], ![![-519, -113, 185, 40, 267]]]
  g := ![![![-139320, -139812, 73337, 16209, 133081], ![191103, 191777, -100595, -22234, -182544], ![-262108, -263035, 137972, 30494, 250372], ![84233, 84528, -44339, -9801, -80458], ![-20943, -21016, 11024, 2437, 20004]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [36, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 46], [0, 1]]
 g := ![![[38, 17], [22, 42], [21, 24], [0, 25], [1]], ![[0, 30], [0, 5], [42, 23], [16, 22], [1]]]
 h' := ![![[42, 46], [7, 39], [43, 18], [0, 20], [11, 42], [0, 1]], ![[0, 1], [0, 8], [0, 29], [41, 27], [36, 5], [42, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [19, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [36, 5, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-134488, -55486, 29210, -22420, -65722]
  a := ![-13, 24, 27, 8, 82]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![46920, 21280, 29210, -22420, -65722]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21207883, 9593972, -2387008, -528140, -4330376]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-21207883, 9593972, -2387008, -528140, -4330376]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![16, 33, 1, 0, 0], ![18, 28, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![-21207883, 9593972, -2387008, -528140, -4330376], ![29151096, -13139207, 3256292, 717896, 5912936], ![-39784992, 18088292, -4524455, -1005912, -8197568], ![13034892, -5728412, 1380528, 296429, 2523908], ![-3261132, 1417312, -337232, -71508, -618479]]]
  hmulB := by decide  
  f := ![![![-5981, -7756, -1872, -1612, -14040]], ![![93912, 27351, -27100, 14664, 22984]], ![![59096, 20085, -15339, 9488, 20280]], ![![26670, -6736, -16368, 2589, -23620]], ![![5646, -4328, -5200, 236, -11023]]]
  g := ![![![4433331, 2194748, -2387008, -528140, -4330376], ![-6047128, -2993573, 3256292, 717896, 5912936], ![8404480, 4160869, -4524455, -1005912, -8197568], ![-2561562, -1267784, 1380528, 296429, 2523908], ![625486, 309536, -337232, -71508, -618479]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [7, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 46], [0, 1]]
 g := ![![[14, 27], [13, 27], [16, 21], [39, 16], [1]], ![[0, 20], [46, 20], [26, 26], [22, 31], [1]]]
 h' := ![![[43, 46], [3, 36], [29, 11], [9, 16], [40, 43], [0, 1]], ![[0, 1], [0, 11], [32, 36], [39, 31], [9, 4], [43, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [16, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [7, 4, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4721081, -753640, 1758156, -491232, 555637]
  a := ![-87, 190, 184, 89, 552]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1007365, -957836, 1758156, -491232, 555637]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-355, 1975, -1089, -352, -1704]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-355, 1975, -1089, -352, -1704]] 
 ![![47, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![-355, 1975, -1089, -352, -1704], ![12336, 796, -2249, -882, -3152], ![24204, 11229, -9788, -3486, -14604], ![48102, 13359, -14177, -5201, -20846], ![-15402, -4308, 4636, 1698, 6803]]]
  hmulB := by decide  
  f := ![![![-1625, 9713, 6555, 796, 20604]], ![![-3700, 4358, 4315, -22, 10288]], ![![14379, 2274, -5291, 2070, -360]], ![![16345, 32420, 11812, 5435, 61126]], ![![-17518, 868, 8620, -2146, 7943]]]
  g := ![![![696, 1975, -1089, -352, -1704], ![3395, 796, -2249, -882, -3152], ![10194, 11229, -9788, -3486, -14604], ![16548, 13359, -14177, -5201, -20846], ![-5428, -4308, 4636, 1698, 6803]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![653050, -295103, 73337, 16209, 133081]] ![![-21207883, 9593972, -2387008, -528140, -4330376]]
  ![![-25592807977606, 11565069356489, -2874089262251, -635237197119, -5215460022651]] where
 M := ![![![-25592807977606, 11565069356489, -2874089262251, -635237197119, -5215460022651]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-25592807977606, 11565069356489, -2874089262251, -635237197119, -5215460022651]] ![![-355, 1975, -1089, -352, -1704]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![131960021523227794, -59631080812555298, 14819197682327988, 3275369947655521, 26891625845148821]]]
 hmul := by decide  
 g := ![![![![2807660032409102, -1268746400267134, 315302078347404, 69688722290543, 572162252024443]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 5 2 5 [24, 13, 14, 26, 37, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 26, 24, 29, 19], [46, 44, 28, 21, 26], [49, 13, 4, 41, 7], [45, 22, 50, 15, 1], [0, 1]]
 g := ![![[14, 52, 19, 5, 42], [45, 48, 19, 52], [51, 43, 28, 39, 6], [16, 1], []], ![[15, 49, 52, 39, 23, 43, 29, 51], [51, 24, 49, 46], [12, 49, 42, 30, 42, 9, 28, 2], [30, 33, 0, 15], [20, 31, 44, 15, 15, 38, 12, 22]], ![[26, 6, 22, 30, 49, 41, 8, 34], [38, 41, 46, 10], [49, 47, 28, 25, 10, 32, 3, 14], [7, 52, 0, 43], [1, 15, 41, 52, 8, 20, 27, 33]], ![[14, 28, 11, 26, 37, 23, 1, 13], [17, 17, 24, 4], [27, 48, 20, 6, 4, 3, 42, 49], [20, 33, 0, 40], [34, 22, 44, 28, 40, 6, 14, 25]], ![[32, 40, 29, 19, 25, 44, 5, 47], [17, 20, 10, 24], [8, 14, 10, 44, 29, 25, 46, 47], [41, 30, 6, 9], [26, 28, 44, 50, 26, 26, 8, 1]]]
 h' := ![![[35, 26, 24, 29, 19], [5, 8, 47, 25, 28], [48, 11, 6, 48, 23], [40, 33, 28, 47, 18], [0, 0, 0, 1], [0, 1]], ![[46, 44, 28, 21, 26], [1, 10, 46, 18, 48], [18, 45, 43, 42, 24], [47, 44, 43, 19, 9], [48, 47, 31, 18, 11], [35, 26, 24, 29, 19]], ![[49, 13, 4, 41, 7], [48, 33, 3, 39, 41], [18, 14, 49, 37, 40], [7, 39, 45, 22, 5], [4, 0, 3, 7, 19], [46, 44, 28, 21, 26]], ![[45, 22, 50, 15, 1], [17, 13, 30, 33, 32], [52, 50, 2, 43, 2], [14, 51, 42, 19, 31], [21, 25, 3, 4, 26], [49, 13, 4, 41, 7]], ![[0, 1], [40, 42, 33, 44, 10], [17, 39, 6, 42, 17], [22, 45, 1, 52, 43], [30, 34, 16, 23, 50], [45, 22, 50, 15, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 52, 25, 46], [], [], []]
 b := ![[], [48, 51, 22, 5, 45], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 5
  hpos := by decide
  P := [24, 13, 14, 26, 37, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3510919890604361, 25119843785834156, 16632920656989377, 2148655233517232, 53048139966355788]
  a := ![-35, 76, 73, 34, 222]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-66243771520837, 473959316713852, 313828691641309, 40540664783344, 1000908301251996]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 418195493 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7793, 3527, -877, -194, -1590]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-7793, 3527, -877, -194, -1590]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![18, 35, 42, 14, 1]] where
  M :=![![![-7793, 3527, -877, -194, -1590], ![10704, -4832, 1199, 262, 2168], ![-14580, 6637, -1688, -366, -3052], ![4902, -1993, 523, 135, 1118], ![-1260, 500, -108, -36, -247]]]
  hmulB := by decide  
  f := ![![![749, 253, -213, -78, -322]], ![![2400, 810, -683, -250, -1032]], ![![7692, 2595, -2190, -802, -3308]], ![![11130, 3749, -3173, -1163, -4798]], ![![9702, 3272, -2763, -1012, -4175]]]
  g := ![![![353, 1003, 1117, 374, -1590], ![-480, -1368, -1523, -510, 2168], ![684, 1923, 2144, 718, -3052], ![-258, -697, -787, -263, 1118], ![54, 155, 174, 58, -247]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [12, 5, 22, 51, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 53, 16, 44], [9, 3, 8, 43], [19, 2, 35, 31], [0, 1]]
 g := ![![[41, 43, 26, 17], [23, 44, 45, 22], [44, 15, 17], [37, 42, 8, 1], []], ![[46, 14, 24, 34, 11, 56], [25, 25, 33, 58, 0, 55], [25, 26, 17], [5, 13, 41, 18, 9, 30], [4, 26, 28, 57, 25, 47]], ![[43, 16, 32, 43, 15, 23], [49, 2, 35, 56, 5, 30], [34, 19, 36], [16, 31, 18, 14, 54, 14], [53, 57, 39, 16, 44, 34]], ![[0, 54, 29, 9, 31, 18], [51, 10, 0, 31, 10, 52], [14, 34, 36], [37, 23, 57, 16, 16, 14], [44, 57, 15, 50, 42, 55]]]
 h' := ![![[39, 53, 16, 44], [19, 52, 42, 31], [20, 15, 55, 9], [28, 19, 1, 28], [0, 0, 0, 1], [0, 1]], ![[9, 3, 8, 43], [38, 28, 25, 22], [15, 38, 6, 55], [43, 46, 42, 31], [35, 20, 25, 23], [39, 53, 16, 44]], ![[19, 2, 35, 31], [19, 7, 17, 28], [30, 6, 46, 25], [5, 5, 47, 53], [34, 16, 32, 53], [9, 3, 8, 43]], ![[0, 1], [0, 31, 34, 37], [12, 0, 11, 29], [48, 48, 28, 6], [18, 23, 2, 41], [19, 2, 35, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [19, 9, 27], []]
 b := ![[], [], [1, 10, 34, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [12, 5, 22, 51, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1124121296053, -333840835076, -718835192558, 113553129418, -1071159158381]
  a := ![-23, 53, 49, 28, 147]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![345847222829, 629775079801, 750336431516, 256097988928, -1071159158381]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-749, -253, 213, 78, 322]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-749, -253, 213, 78, 322]] 
 ![![59, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![-749, -253, 213, 78, 322], ![-2400, -810, 683, 250, 1032], ![-7692, -2595, 2190, 802, 3308], ![-11130, -3749, 3173, 1163, 4798], ![3948, 1332, -1124, -412, -1699]]]
  hmulB := by decide  
  f := ![![![7793, -3527, 877, 194, 1590]], ![![479, -217, 54, 12, 98]], ![![4738, -2145, 534, 118, 968]], ![![49, -26, 6, 1, 8]], ![![5701, -2579, 641, 142, 1163]]]
  g := ![![![-350, -253, 213, 78, 322], ![-1122, -810, 683, 250, 1032], ![-3597, -2595, 2190, 802, 3308], ![-5216, -3749, 3173, 1163, 4798], ![1847, 1332, -1124, -412, -1699]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-7793, 3527, -877, -194, -1590]] ![![-749, -253, 213, 78, 322]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [60, 5, 17, 38, 41, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 45, 0, 29, 43], [37, 28, 43, 40, 54], [19, 8, 48, 33, 13], [30, 40, 31, 20, 12], [0, 1]]
 g := ![![[56, 8, 12, 34, 3], [1, 11, 0, 39], [36, 38, 47, 57, 9], [57, 20, 1], []], ![[15, 42, 8, 59, 4, 6, 38, 24], [6, 7, 27, 47], [39, 27, 22, 39, 13, 30, 22, 24], [1, 46, 34, 19, 15, 36, 58, 17], [42, 37, 38, 21, 28, 55, 59, 24]], ![[1, 55, 7, 47, 55, 28, 27, 2], [31, 59, 34, 58], [7, 57, 25, 0, 39, 52, 39, 35], [50, 42, 29, 22, 32, 34, 31, 18], [26, 35, 12, 10, 46, 10, 57, 23]], ![[3, 55, 38, 53, 3, 32, 35, 48], [41, 44, 30, 57], [43, 47, 3, 49, 23, 35, 11, 47], [28, 46, 58, 10, 39, 57, 60, 57], [8, 2, 27, 51, 51, 43, 37, 1]], ![[24, 18, 15, 57, 7, 20, 8, 39], [29, 52, 4, 19], [24, 31, 2, 34, 18, 54, 16, 60], [11, 52, 39, 38, 12, 15, 27, 16], [18, 28, 45, 0, 50, 5, 12, 20]]]
 h' := ![![[56, 45, 0, 29, 43], [16, 23, 14, 55, 53], [36, 57, 23, 22, 10], [57, 40, 30, 51, 58], [0, 0, 0, 1], [0, 1]], ![[37, 28, 43, 40, 54], [52, 51, 16, 47, 18], [30, 48, 43, 47, 13], [21, 56, 33, 20, 43], [39, 30, 57, 16, 57], [56, 45, 0, 29, 43]], ![[19, 8, 48, 33, 13], [44, 15, 54, 11, 33], [47, 20, 6, 57, 34], [10, 31, 33, 4, 42], [49, 38, 49, 60, 38], [37, 28, 43, 40, 54]], ![[30, 40, 31, 20, 12], [42, 4, 19, 2, 11], [1, 52, 16, 33, 22], [1, 12, 55, 8, 14], [35, 25, 3, 0, 42], [19, 8, 48, 33, 13]], ![[0, 1], [29, 29, 19, 7, 7], [0, 6, 34, 24, 43], [29, 44, 32, 39, 26], [56, 29, 13, 45, 46], [30, 40, 31, 20, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 0, 32, 60], [], [], []]
 b := ![[], [49, 51, 33, 6, 44], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [60, 5, 17, 38, 41, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-39396800084221582086, -42132827983277796860, -6955878582766300898, -9390120277782294294, -73089583762714352454]
  a := ![157, -346, -331, -173, -992]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-645849181708550526, -690702098086521260, -114030796438791818, -153936397996431054, -1198189897749415614]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 844596301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀



lemma PB1705I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1705I1 : PrimesBelowBoundCertificateInterval O 23 61 1705 where
  m := 9
  g := ![2, 1, 4, 2, 2, 3, 1, 2, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1705I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0]
    · exact ![I37N0, I37N1, I37N2, I37N3]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![24389, 841]
    · exact ![28629151]
    · exact ![1369, 37, 37, 37]
    · exact ![68921, 1681]
    · exact ![3418801, 43]
    · exact ![2209, 2209, 47]
    · exact ![418195493]
    · exact ![12117361, 59]
    · exact ![844596301]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
      exact NI37N3
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I29N1, I37N0, I37N1, I37N2, I37N3, I41N1, I43N1, I47N2, I59N1]
  Il := ![[I29N1], [], [I37N0, I37N1, I37N2, I37N3], [I41N1], [I43N1], [I47N2], [], [I59N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
