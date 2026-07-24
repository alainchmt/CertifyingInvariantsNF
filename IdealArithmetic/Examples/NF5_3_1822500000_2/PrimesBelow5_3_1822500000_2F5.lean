
import IdealArithmetic.Examples.NF5_3_1822500000_2.RI5_3_1822500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1063, -504, -503, -341, -1350]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-1063, -504, -503, -341, -1350]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![42, 107, 1, 0, 0], ![83, 135, 0, 1, 0], ![65, 103, 0, 0, 1]] where
  M :=![![![-1063, -504, -503, -341, -1350], ![7848, 2903, 5653, 4047, 13622], ![-35544, -17622, -14972, -9949, -41674], ![283848, 100746, 214603, 154362, 511758], ![-81504, -27858, -64164, -46328, -151735]]]
  hmulB := by decide  
  f := ![![![56399, 6168, 6703, 11607, 37358]], ![![-60888, -1255, -5755, -10675, -33994]], ![![-20598, 571, -1673, -3268, -10328]], ![![-17765, 1899, -1059, -2338, -7266]], ![![-13295, 1319, -820, -1784, -5555]]]
  g := ![![![684, 1198, -503, -341, -1350], ![-7291, -12821, 5653, 4047, 13622], ![20743, 36281, -14972, -9949, -41674], ![-275406, -484481, 214603, 154362, 511758], ![82017, 144325, -64164, -46328, -151735]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [49, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [193, 198], [0, 1]]
 g := ![![[191, 65], [141, 123], [67, 177], [58], [52], [169], [193, 1]], ![[0, 134], [0, 76], [0, 22], [58], [52], [169], [187, 198]]]
 h' := ![![[193, 198], [56, 142], [100, 83], [2, 133], [156, 43], [147, 98], [95, 186], [0, 1]], ![[0, 1], [0, 57], [0, 116], [0, 66], [97, 156], [156, 101], [173, 13], [193, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [107, 102]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [49, 6, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![776269, 162696, 856201, 634255, 1906033]
  a := ![-180, -61, -183, -126, -395]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1063917, -1876365, 856201, 634255, 1906033]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-996901, -401335, -195858, -301493, -990216]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-996901, -401335, -195858, -301493, -990216]] 
 ![![199, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![107, 0, 0, 1, 0], ![47, 0, 0, 0, 1]] where
  M :=![![![-996901, -401335, -195858, -301493, -990216], ![2057688, 679211, 364644, 572948, 1874906], ![-3745488, -1065714, -618423, -986452, -3219516], ![6243840, 1555308, 972158, 1571233, 5116384], ![-164832, 66663, 2948, -5837, -13045]]]
  hmulB := by decide  
  f := ![![![29453, 2191, 26236, 21587, 70774]], ![![4751, -42, 4628, 3879, 12516]], ![![9288, 2094, 7673, 5908, 19408]], ![![-7175, -11629, 7102, 7384, 16550]], ![![12973, 4226, 7406, 5676, 21015]]]
  g := ![![![489211, -401335, -195858, -301493, -990216], ![-910807, 679211, 364644, 572948, 1874906], ![1544702, -1065714, -618423, -986452, -3219516], ![-2428273, 1555308, 972158, 1571233, 5116384], ![-7359, 66663, 2948, -5837, -13045]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25165, 104820, -34166, -55470, -168516]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![25165, 104820, -34166, -55470, -168516]] 
 ![![199, 0, 0, 0, 0], ![121, 1, 0, 0, 0], ![85, 0, 1, 0, 0], ![63, 0, 0, 1, 0], ![124, 0, 0, 0, 1]] where
  M :=![![![25165, 104820, -34166, -55470, -168516], ![50544, 210529, -68622, -111410, -338460], ![101520, 422844, -137821, -223762, -679780], ![203856, 849252, -276842, -449441, -1365396], ![-127968, -533064, 173760, 282100, 857013]]]
  hmulB := by decide  
  f := ![![![-4253, 324, -8790, -6550, -18116]], ![![-2771, 205, -5652, -4216, -11664]], ![![-3047, 192, -5859, -4392, -12168]], ![![-9813, 480, -17220, -13011, -36128]], ![![268, 72, -496, -308, -803]]]
  g := ![![![73551, 104820, -34166, -55470, -168516], ![147725, 210529, -68622, -111410, -338460], ![296693, 422844, -137821, -223762, -679780], ![595979, 849252, -276842, -449441, -1365396], ![-374064, -533064, 173760, 282100, 857013]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2

def I199N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![791, -35, 1349, 1022, 2840]] i)))

def SI199N3: IdealEqSpanCertificate' Table ![![791, -35, 1349, 1022, 2840]] 
 ![![199, 0, 0, 0, 0], ![133, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![59, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![791, -35, 1349, 1022, 2840], ![5424, -241, 9251, 7009, 19476], ![37224, -1644, 63468, 48085, 133622], ![255192, -11334, 435255, 329766, 916330], ![-88056, 3909, -150184, -113785, -316179]]]
  hmulB := by decide  
  f := ![![![8009, 1031, 1469, 2398, 7706]], ![![5291, 670, 976, 1593, 5118]], ![![962, 110, 178, 291, 934]], ![![2269, 265, 434, 708, 2272]], ![![1358, 191, 242, 395, 1271]]]
  g := ![![![-910, -35, 1349, 1022, 2840], ![-6240, -241, 9251, 7009, 19476], ![-42817, -1644, 63468, 48085, 133622], ![-293590, -11334, 435255, 329766, 916330], ![101304, 3909, -150184, -113785, -316179]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N3 : Nat.card (O ⧸ I199N3) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N3)

lemma isPrimeI199N3 : Ideal.IsPrime I199N3 := prime_ideal_of_norm_prime hp199.out _ NI199N3
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-1063, -504, -503, -341, -1350]] ![![-996901, -401335, -195858, -301493, -990216]]
  ![![-14765, -4175, -2431, -3880, -12662]] where
 M := ![![![-14765, -4175, -2431, -3880, -12662]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![-14765, -4175, -2431, -3880, -12662]] ![![25165, 104820, -34166, -55470, -168516]]
  ![![-8009, -1031, -1469, -2398, -7706]] where
 M := ![![![-8009, -1031, -1469, -2398, -7706]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI199N2 : IdealMulLeCertificate' Table 
  ![![-8009, -1031, -1469, -2398, -7706]] ![![791, -35, 1349, 1022, 2840]]
  ![![199, 0, 0, 0, 0]] where
 M := ![![![-199, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1, I199N2, I199N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
    exact isPrimeI199N2
    exact isPrimeI199N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0 ⊙ MulI199N1 ⊙ MulI199N2)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0, 0, 0]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![0, 0, 0, 211, 0], ![0, 0, 0, 0, 211]] where
  M :=![![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![0, 0, 0, 211, 0], ![0, 0, 0, 0, 211]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 5 2 7 [14, 9, 98, 18, 56, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 206, 20, 42, 185], [126, 73, 173, 136, 133], [149, 154, 75, 113, 31], [82, 199, 154, 131, 73], [0, 1]]
 g := ![![[135, 70, 210, 168, 170], [109, 98, 186, 102, 1], [8, 193, 30, 44], [18, 109, 97, 87], [101, 88, 57, 68, 99], [155, 1], []], ![[67, 144, 194, 39, 109, 74, 98, 93], [64, 133, 20, 109, 162, 38, 63, 178], [18, 2, 16, 139], [140, 170, 184, 170], [190, 5, 104, 139, 146, 12, 116, 5], [38, 196, 92, 84], [27, 102, 10, 54, 38, 45, 84, 148]], ![[144, 24, 116, 170, 99, 147, 167, 18], [125, 119, 181, 130, 69, 1, 115, 149], [209, 42, 149, 62], [21, 152, 53, 150], [2, 57, 49, 159, 198, 156, 34, 118], [162, 96, 101, 44], [47, 68, 185, 159, 21, 128, 163, 198]], ![[62, 171, 62, 32, 121, 32, 210, 86], [73, 8, 34, 185, 201, 114, 9, 129], [2, 133, 97, 34], [25, 207, 47, 4], [78, 181, 77, 71, 38, 80, 140, 3], [189, 40, 203, 71], [133, 11, 4, 140, 184, 47, 76, 40]], ![[47, 126, 154, 39, 196, 56, 163, 47], [60, 173, 152, 179, 165, 137, 166, 204], [40, 88, 134, 105], [209, 193, 148, 64], [148, 197, 12, 26, 41, 148, 94, 36], [80, 24, 158, 204], [183, 121, 72, 25, 52, 92, 76, 144]]]
 h' := ![![[9, 206, 20, 42, 185], [162, 203, 43, 54, 35], [119, 34, 57, 132, 210], [130, 53, 34, 151, 39], [63, 193, 186, 98, 147], [151, 68, 204, 66, 164], [0, 0, 0, 1], [0, 1]], ![[126, 73, 173, 136, 133], [1, 185, 21, 5, 44], [35, 38, 130, 84, 171], [169, 148, 165, 52, 75], [190, 161, 18, 6, 35], [78, 129, 119, 155, 24], [140, 68, 143, 105, 57], [9, 206, 20, 42, 185]], ![[149, 154, 75, 113, 31], [204, 43, 28, 205, 207], [204, 7, 84, 37, 113], [133, 22, 80, 28, 189], [65, 117, 140, 17, 19], [30, 199, 50, 138, 67], [71, 88, 38, 41, 39], [126, 73, 173, 136, 133]], ![[82, 199, 154, 131, 73], [122, 9, 74, 163, 175], [6, 176, 94, 14, 195], [33, 191, 85, 56, 178], [52, 182, 144, 15, 2], [6, 118, 139, 83, 98], [139, 67, 105, 56, 156], [149, 154, 75, 113, 31]], ![[0, 1], [82, 193, 45, 206, 172], [110, 167, 57, 155, 155], [44, 8, 58, 135, 152], [207, 191, 145, 75, 8], [171, 119, 121, 191, 69], [206, 199, 136, 8, 170], [82, 199, 154, 131, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 193, 61, 88], [], [], []]
 b := ![[], [130, 163, 66, 178, 117], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 5
  hpos := by decide
  P := [14, 9, 98, 18, 56, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![965296790989771556, 82714435865784444, 1347799690830897192, 1012026208380826116, 2903910313205153544]
  a := ![309, 41, 314, 215, 678]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4574866308008396, 392011544387604, 6387676259862072, 4796332741141356, 13762608119455704]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 418227202051 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def PBC211 : ContainsPrimesAboveP 211 ![I211N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![211, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 211 (by decide) 𝕀

instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-511, -185, -91, -142, -466]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![-511, -185, -91, -142, -466]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![155, 75, 1, 0, 0], ![194, 105, 0, 1, 0], ![106, 149, 0, 0, 1]] where
  M :=![![![-511, -185, -91, -142, -466], ![960, 275, 167, 265, 864], ![-1656, -456, -252, -407, -1330], ![2616, 546, 423, 678, 2194], ![0, 75, -4, -7, -15]]]
  hmulB := by decide  
  f := ![![![647, 269, 389, 274, 980]], ![![-3792, -1597, -2269, -1591, -5708]], ![![-725, -308, -432, -302, -1086]], ![![-1814, -767, -1084, -759, -2726]], ![![-2062, -870, -1233, -864, -3101]]]
  g := ![![![406, 408, -91, -142, -466], ![-753, -757, 167, 265, 864], ![1154, 1163, -252, -407, -1330], ![-1915, -1925, 423, 678, 2194], ![16, 15, -4, -7, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [218, 210, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 222], [0, 1]]
 g := ![![[181, 89], [221, 196], [66, 36], [194, 47], [144, 72], [171], [13, 1]], ![[0, 134], [93, 27], [88, 187], [136, 176], [188, 151], [171], [26, 222]]]
 h' := ![![[13, 222], [213, 138], [107, 209], [78, 6], [51, 173], [174, 90], [65, 174], [0, 1]], ![[0, 1], [0, 85], [148, 14], [156, 217], [70, 50], [6, 133], [97, 49], [13, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [210]]
 b := ![[], [98, 105]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [218, 210, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![333, -860, 916, 633, 1799]
  a := ![-5, -4, -5, -4, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2041, -1812, 916, 633, 1799]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-193, -2, -18, -34, -108]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-193, -2, -18, -34, -108]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![221, 81, 1, 0, 0], ![162, 127, 0, 1, 0], ![11, 25, 0, 0, 1]] where
  M :=![![![-193, -2, -18, -34, -108], ![144, -37, 0, 10, 28], ![48, 132, 49, 52, 180], ![-576, -324, -212, -231, -784], ![240, 54, 58, 68, 227]]]
  hmulB := by decide  
  f := ![![![-31, 14, -62, -50, -140]], ![![-240, 29, -416, -322, -900]], ![![-125, 25, -225, -176, -492]], ![![-210, 29, -368, -285, -796]], ![![-11, 3, -20, -16, -45]]]
  g := ![![![47, 38, -18, -34, -108], ![-8, -9, 0, 10, 28], ![-95, -67, 49, 52, 180], ![414, 295, -212, -231, -784], ![-117, -85, 58, 68, 227]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P1 : CertificateIrreducibleZModOfList' 223 2 2 7 [142, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [127, 222], [0, 1]]
 g := ![![[164, 152], [51, 7], [20, 47], [222, 55], [188, 86], [78], [127, 1]], ![[67, 71], [48, 216], [191, 176], [71, 168], [183, 137], [78], [31, 222]]]
 h' := ![![[127, 222], [117, 44], [59, 197], [142, 173], [64, 151], [23, 106], [29, 154], [0, 1]], ![[0, 1], [130, 179], [102, 26], [36, 50], [63, 72], [105, 117], [186, 69], [127, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [184, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N1 : CertifiedPrimeIdeal' SI223N1 223 where
  n := 2
  hpos := by decide
  P := [142, 96, 1]
  hirr := P223P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2539127, 612924, 2618711, 1929712, 5888454]
  a := ![319, 126, 324, 221, 700]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4276154, -2707567, 2618711, 1929712, 5888454]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N1 B_one_repr
lemma NI223N1 : Nat.card (O ⧸ I223N1) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, -17, 1, 2, -8]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![-25, -17, 1, 2, -8]] 
 ![![223, 0, 0, 0, 0], ![67, 1, 0, 0, 0], ![194, 0, 1, 0, 0], ![159, 0, 0, 1, 0], ![92, 0, 0, 0, 1]] where
  M :=![![![-25, -17, 1, 2, -8], ![336, 95, 313, 229, 716], ![-696, -612, 344, 307, 382], ![12936, 3234, 13013, 9582, 29406], ![-3912, -885, -4158, -3073, -9311]]]
  hmulB := by decide  
  f := ![![![-37567, -16699, -7815, -11906, -39174]], ![![-10915, -4886, -2280, -3471, -11422]], ![![-33386, -14738, -6918, -10547, -34698]], ![![-25575, -11589, -5380, -8180, -26924]], ![![-15548, -6881, -3226, -4917, -16177]]]
  g := ![![![6, -17, 1, 2, -8], ![-758, 95, 313, 229, 716], ![-495, -612, 344, 307, 382], ![-31198, 3234, 13013, 9582, 29406], ![9898, -885, -4158, -3073, -9311]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![-511, -185, -91, -142, -466]] ![![-193, -2, -18, -34, -108]]
  ![![37567, 16699, 7815, 11906, 39174]] where
 M := ![![![37567, 16699, 7815, 11906, 39174]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![37567, 16699, 7815, 11906, 39174]] ![![-25, -17, 1, 2, -8]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![-223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![40735, 169675, -55306, -89791, -272782]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![40735, 169675, -55306, -89791, -272782]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![218, 36, 1, 0, 0], ![97, 57, 0, 1, 0], ![49, 35, 0, 0, 1]] where
  M :=![![![40735, 169675, -55306, -89791, -272782], ![81816, 340789, -111082, -180344, -547878], ![164304, 684462, -223129, -362234, -1100452], ![330000, 1374756, -448224, -727597, -2210372], ![-207144, -862899, 281306, 456671, 1387337]]]
  hmulB := by decide  
  f := ![![![34661, 9961, 5748, 9161, 29904]], ![![-58104, -14611, -9078, -14666, -47762]], ![![24470, 7336, 4139, 6568, 21456]], ![![-353, 482, 98, 100, 358]], ![![-1505, -119, -166, -294, -943]]]
  g := ![![![150544, 74124, -55306, -89791, -272782], ![302366, 148877, -111082, -180344, -547878], ![607336, 299032, -223129, -362234, -1100452], ![1219947, 600647, -448224, -727597, -2210372], ![-765676, -376991, 281306, 456671, 1387337]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [111, 214, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 226], [0, 1]]
 g := ![![[96, 26], [147, 186], [182], [155], [177], [59, 186], [13, 1]], ![[207, 201], [68, 41], [182], [155], [177], [207, 41], [26, 226]]]
 h' := ![![[13, 226], [27, 88], [182, 169], [194, 78], [123, 137], [34, 75], [146, 58], [0, 1]], ![[0, 1], [36, 139], [109, 58], [73, 149], [88, 90], [101, 152], [219, 169], [13, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [222, 123]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [111, 214, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3757014, 959468, 3718225, 2738580, 8432124]
  a := ![-391, -131, -396, -270, -858]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6544636, -2573216, 3718225, 2738580, 8432124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13943, -3707, -2233, -3586, -11690]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![-13943, -3707, -2233, -3586, -11690]] 
 ![![227, 0, 0, 0, 0], ![95, 1, 0, 0, 0], ![55, 0, 1, 0, 0], ![223, 0, 0, 1, 0], ![141, 0, 0, 0, 1]] where
  M :=![![![-13943, -3707, -2233, -3586, -11690], ![22368, 5203, 3385, 5507, 17912], ![-33384, -6672, -4762, -7857, -25494], ![46152, 7494, 6129, 10292, 33294], ![3408, 1569, 720, 1095, 3605]]]
  hmulB := by decide  
  f := ![![![90707, -4133, 154775, 117294, 325948]], ![![40703, -1852, 69450, 52631, 146256]], ![![40783, -1837, 69573, 52719, 146498]], ![![218119, -9775, 372046, 281906, 783374]], ![![11829, -594, 20229, 15345, 42647]]]
  g := ![![![12815, -3707, -2233, -3586, -11690], ![-19435, 5203, 3385, 5507, 17912], ![27353, -6672, -4762, -7857, -25494], ![-35209, 7494, 6129, 10292, 33294], ![-4131, 1569, 720, 1095, 3605]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1

def I227N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 3, 10, 15, 48]] i)))

def SI227N2: IdealEqSpanCertificate' Table ![![13, 3, 10, 15, 48]] 
 ![![227, 0, 0, 0, 0], ![115, 1, 0, 0, 0], ![168, 0, 1, 0, 0], ![202, 0, 0, 1, 0], ![226, 0, 0, 0, 1]] where
  M :=![![![13, 3, 10, 15, 48], ![-72, -59, -6, -8, -30], ![144, 6, 47, 74, 236], ![-336, -204, -20, -29, -108], ![48, 69, -18, -29, -87]]]
  hmulB := by decide  
  f := ![![![-25, 33, -96, -77, -190]], ![![-17, 16, -54, -43, -108]], ![![-24, 30, -93, -74, -184]], ![![-206, 6, -324, -247, -688]], ![![34, 39, -16, -17, -17]]]
  g := ![![![-70, 3, 10, 15, 48], ![71, -59, -6, -8, -30], ![-338, 6, 47, 74, 236], ![250, -204, -20, -29, -108], ![91, 69, -18, -29, -87]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N2 : Nat.card (O ⧸ I227N2) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N2)

lemma isPrimeI227N2 : Ideal.IsPrime I227N2 := prime_ideal_of_norm_prime hp227.out _ NI227N2

def I227N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-131, -19, -18, -29, -94]] i)))

def SI227N3: IdealEqSpanCertificate' Table ![![-131, -19, -18, -29, -94]] 
 ![![227, 0, 0, 0, 0], ![208, 1, 0, 0, 0], ![93, 0, 1, 0, 0], ![178, 0, 0, 1, 0], ![174, 0, 0, 0, 1]] where
  M :=![![![-131, -19, -18, -29, -94], ![168, 19, 26, 36, 118], ![-240, -30, -67, -62, -212], ![624, 180, 320, 225, 804], ![-72, -45, -78, -43, -161]]]
  hmulB := by decide  
  f := ![![![-1225, 95, -2128, -1621, -4508]], ![![-1160, 89, -2014, -1534, -4266]], ![![-759, 51, -1311, -997, -2772]], ![![-2726, 154, -4680, -3553, -9876]], ![![-330, 45, -592, -455, -1267]]]
  g := ![![![119, -19, -18, -29, -94], ![-146, 19, 26, 36, 118], ![265, -30, -67, -62, -212], ![-1086, 180, 320, 225, 804], ![230, -45, -78, -43, -161]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N3 : Nat.card (O ⧸ I227N3) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N3)

lemma isPrimeI227N3 : Ideal.IsPrime I227N3 := prime_ideal_of_norm_prime hp227.out _ NI227N3
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![40735, 169675, -55306, -89791, -272782]] ![![-13943, -3707, -2233, -3586, -11690]]
  ![![-17489, -72700, 23713, 38495, 116950]] where
 M := ![![![-17489, -72700, 23713, 38495, 116950]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI227N1 : IdealMulLeCertificate' Table 
  ![![-17489, -72700, 23713, 38495, 116950]] ![![13, 3, 10, 15, 48]]
  ![![1100995, 4595681, -1499179, -2433878, -7394314]] where
 M := ![![![1100995, 4595681, -1499179, -2433878, -7394314]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI227N2 : IdealMulLeCertificate' Table 
  ![![1100995, 4595681, -1499179, -2433878, -7394314]] ![![-131, -19, -18, -29, -94]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![1297759, 6020494, -1969679, -3202289, -9730582]]]
 hmul := by decide  
 g := ![![![![5717, 26522, -8677, -14107, -42866]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1, I227N2, I227N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
    exact isPrimeI227N2
    exact isPrimeI227N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0 ⊙ MulI227N1 ⊙ MulI227N2)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![121, -637, 2628, 1757, 4656]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![121, -637, 2628, 1757, 4656]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![72, 200, 211, 1, 0], ![154, 192, 59, 0, 1]] where
  M :=![![![121, -637, 2628, 1757, 4656], ![14760, 385, 20536, 15982, 44806], ![75360, -4926, 136533, 102740, 284856], ![560736, -22584, 943406, 715837, 1990120], ![-190656, 8577, -325054, -246257, -684271]]]
  hmulB := by decide  
  f := ![![![3157, 13951, -4706, -7521, -22898]], ![![8040, 28735, -8428, -14388, -43418]], ![![6096, 53490, -22975, -33140, -102404]], ![![13944, 79346, -30055, -45647, -139980]], ![![10306, 46921, -16081, -25517, -77765]]]
  g := ![![![-3683, -5441, -2807, 1757, 4656], ![-35092, -51523, -26180, 15982, 44806], ![-223536, -328582, -167459, 102740, 284856], ![-1560952, -2293856, -1168189, 715837, 1990120], ![536758, 788821, 401778, -246257, -684271]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [98, 224, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 93, 150], [91, 135, 79], [0, 1]]
 g := ![![[130, 7, 49], [206, 129], [114, 36, 210], [56, 169], [75, 176], [133, 6, 168], [1]], ![[134, 160, 70, 113], [59, 228], [159, 212, 60, 142], [30, 37], [43, 125], [67, 48, 121, 201], [170, 74, 31, 227]], ![[69, 210, 84, 122], [97, 108], [228, 179, 210, 190], [115, 130], [176, 64], [83, 40, 118, 13], [157, 48, 24, 2]]]
 h' := ![![[84, 93, 150], [75, 75, 7], [49, 173, 75], [200, 216, 179], [110, 177, 13], [19, 63, 136], [131, 5, 175], [0, 1]], ![[91, 135, 79], [156, 184, 58], [30, 153, 122], [183, 26, 2], [157, 87, 138], [97, 164, 101], [109, 150, 101], [84, 93, 150]], ![[0, 1], [167, 199, 164], [183, 132, 32], [34, 216, 48], [147, 194, 78], [137, 2, 221], [118, 74, 182], [91, 135, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114, 221], []]
 b := ![[], [126, 178, 226], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [98, 224, 54, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10433655458, 4183169904, 6748377440, 4775311360, 16664546928]
  a := ![216, 72, 220, 140, 474]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12662572006, -18124332368, -8663976368, 4775311360, 16664546928]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 12008989 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3157, 13951, -4706, -7521, -22898]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![3157, 13951, -4706, -7521, -22898]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![79, 18, 1, 0, 0], ![181, 213, 0, 1, 0], ![206, 39, 0, 0, 1]] where
  M :=![![![3157, 13951, -4706, -7521, -22898], ![8040, 28735, -8428, -14388, -43418], ![6096, 53490, -22975, -33140, -102404], ![71616, 132372, -10438, -41511, -115920], ![-29448, -76575, 15876, 32597, 96199]]]
  hmulB := by decide  
  f := ![![![121, -637, 2628, 1757, 4656]], ![![14760, 385, 20536, 15982, 44806]], ![![1531, -211, 3117, 2311, 6372]], ![![16273, -244, 25298, 19380, 54046]], ![![1790, -470, 4442, 3227, 8831]]]
  g := ![![![28180, 11326, -4706, -7521, -22898], ![53372, 21565, -8428, -14388, -43418], ![126265, 50304, -22975, -33140, -102404], ![141001, 59751, -10438, -41511, -115920], ![-117907, -48285, 15876, 32597, 96199]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P1 : CertificateIrreducibleZModOfList' 229 2 2 7 [83, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [203, 228], [0, 1]]
 g := ![![[210, 149], [135], [31, 16], [94], [53], [35, 134], [203, 1]], ![[0, 80], [135], [73, 213], [94], [53], [215, 95], [177, 228]]]
 h' := ![![[203, 228], [184, 148], [175, 140], [199, 4], [98, 134], [72, 125], [97, 135], [0, 1]], ![[0, 1], [0, 81], [199, 89], [95, 225], [49, 95], [28, 104], [22, 94], [203, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [221]]
 b := ![[], [177, 225]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N1 : CertifiedPrimeIdeal' SI229N1 229 where
  n := 2
  hpos := by decide
  P := [83, 26, 1]
  hirr := P229P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8939978, 1576612, 10576180, 7866998, 23292568]
  a := ![619, 214, 629, 437, 1358]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30780672, -12108626, 10576180, 7866998, 23292568]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N1 B_one_repr
lemma NI229N1 : Nat.card (O ⧸ I229N1) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![121, -637, 2628, 1757, 4656]] ![![3157, 13951, -4706, -7521, -22898]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![229, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![761, 303, 187, 240, 800]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![761, 303, 187, 240, 800]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![107, 209, 68, 1, 0], ![127, 150, 184, 0, 1]] where
  M :=![![![761, 303, 187, 240, 800], ![-1920, -679, -577, -613, -2080], ![5784, 2088, 2412, 2053, 7146], ![-23688, -9258, -12401, -9274, -32926], ![5544, 2247, 3262, 2291, 8215]]]
  hmulB := by decide  
  f := ![![![-1367, -5685, 1853, 3008, 9138]], ![![-2736, -11417, 3725, 6045, 18364]], ![![-5496, -22932, 7496, 12151, 36910]], ![![-4733, -19742, 6445, 10455, 31760]], ![![-6817, -28434, 9287, 15061, 45751]]]
  g := ![![![-543, -729, -701, 240, 800], ![1407, 1886, 1819, -613, -2080], ![-4813, -6433, -6232, 2053, 7146], ![22104, 29476, 28655, -9274, -32926], ![-5506, -7334, -7142, 2291, 8215]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [76, 163, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 221, 165], [126, 11, 68], [0, 1]]
 g := ![![[79, 90, 184], [4, 8], [223, 226], [171, 118, 19], [224, 129], [11, 46, 13], [1]], ![[76, 116, 33, 17], [163, 157], [1, 50], [230, 46, 165, 198], [144, 215], [122, 217, 113, 67], [102, 30, 168, 118]], ![[175, 61, 91, 156], [215, 129], [182, 167], [167, 137, 207, 118], [4, 218], [174, 87, 68, 125], [62, 171, 173, 115]]]
 h' := ![![[54, 221, 165], [191, 123, 76], [202, 4, 170], [52, 154, 172], [114, 122, 187], [96, 21, 96], [157, 70, 180], [0, 1]], ![[126, 11, 68], [217, 194, 161], [16, 168, 200], [201, 92, 41], [62, 125, 52], [145, 18, 94], [126, 74, 16], [54, 221, 165]], ![[0, 1], [148, 149, 229], [90, 61, 96], [116, 220, 20], [176, 219, 227], [108, 194, 43], [19, 89, 37], [126, 11, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [180, 96], []]
 b := ![[], [217, 103, 207], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [76, 163, 53, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![65902213, 25309578, 45300200, 32262811, 110287224]
  a := ![41, 10, 42, 27, 90]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-74646764, -99831337, -96315108, 32262811, 110287224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1367, -5685, 1853, 3008, 9138]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-1367, -5685, 1853, 3008, 9138]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![176, 165, 1, 0, 0], ![85, 212, 0, 1, 0], ![69, 217, 0, 0, 1]] where
  M :=![![![-1367, -5685, 1853, 3008, 9138], ![-2736, -11417, 3725, 6045, 18364], ![-5496, -22932, 7496, 12151, 36910], ![-10968, -46062, 15161, 24486, 74358], ![6912, 28911, -9474, -15337, -46583]]]
  hmulB := by decide  
  f := ![![![761, 303, 187, 240, 800]], ![![-1920, -679, -577, -613, -2080]], ![![-760, -243, -257, -244, -838]], ![![-1571, -547, -510, -510, -1742]], ![![-1539, -533, -468, -490, -1665]]]
  g := ![![![-5209, -12584, 1853, 3008, 9138], ![-10469, -25290, 3725, 6045, 18364], ![-21049, -50838, 7496, 12151, 36910], ![-42452, -102465, 15161, 24486, 74358], ![26576, 64172, -9474, -15337, -46583]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P1 : CertificateIrreducibleZModOfList' 233 2 2 7 [208, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [200, 232], [0, 1]]
 g := ![![[8, 205], [129], [178], [60, 183], [51], [181, 38], [200, 1]], ![[0, 28], [129], [178], [79, 50], [51], [92, 195], [167, 232]]]
 h' := ![![[200, 232], [65, 122], [175, 137], [102, 90], [161, 79], [98, 135], [107, 182], [0, 1]], ![[0, 1], [0, 111], [81, 96], [161, 143], [117, 154], [70, 98], [159, 51], [200, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [194]]
 b := ![[], [86, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N1 : CertifiedPrimeIdeal' SI233N1 233 where
  n := 2
  hpos := by decide
  P := [208, 33, 1]
  hirr := P233P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5412646, 1439775, 5251923, 3854424, 11936928]
  a := ![453, 153, 463, 312, 994]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8884978, -18337248, 5251923, 3854424, 11936928]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N1 B_one_repr
lemma NI233N1 : Nat.card (O ⧸ I233N1) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![761, 303, 187, 240, 800]] ![![-1367, -5685, 1853, 3008, 9138]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![233, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1141, -818, -327, -469, -1554]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-1141, -818, -327, -469, -1554]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![5, 153, 103, 1, 0], ![221, 88, 118, 0, 1]] where
  M :=![![![-1141, -818, -327, -469, -1554], ![3528, 1589, 687, 1087, 3598], ![-8088, -2766, -1814, -2531, -8154], ![13464, 4554, 13, 2100, 7802], ![-768, -72, 742, 428, 1091]]]
  hmulB := by decide  
  f := ![![![2365, 9862, -3217, -5221, -15862]], ![![4776, 19819, -6445, -10475, -31818]], ![![9432, 39738, -13042, -21107, -64150]], ![![7255, 30355, -9921, -16087, -48880]], ![![8551, 35826, -11719, -18995, -57719]]]
  g := ![![![1442, 869, 968, -469, -1554], ![-3335, -2014, -2242, 1087, 3598], ![7559, 4611, 5109, -2531, -8154], ![-7202, -4198, -4757, 2100, 7802], ![-1021, -676, -720, 428, 1091]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [43, 156, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 144, 134], [153, 94, 105], [0, 1]]
 g := ![![[200, 119, 8], [23, 154, 68], [140, 59, 68], [98, 6, 218], [133, 120], [228, 16, 32], [1]], ![[119, 11, 83, 40], [32, 206, 161, 113], [154, 35, 147, 120], [157, 178, 41, 162], [208, 72], [178, 224, 184, 128], [233, 173, 194, 91]], ![[233, 107, 204, 138], [157, 200, 108, 139], [216, 181, 229, 209], [196, 60, 232, 47], [82, 180], [185, 28, 227, 26], [60, 42, 191, 148]]]
 h' := ![![[4, 144, 134], [206, 180, 198], [194, 97, 32], [88, 80, 207], [42, 53, 74], [234, 9, 169], [196, 83, 157], [0, 1]], ![[153, 94, 105], [106, 192, 190], [27, 192, 232], [7, 201, 64], [61, 153, 196], [65, 122, 123], [83, 170, 68], [4, 144, 134]], ![[0, 1], [133, 106, 90], [177, 189, 214], [179, 197, 207], [52, 33, 208], [145, 108, 186], [211, 225, 14], [153, 94, 105]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 157], []]
 b := ![[], [164, 123, 154], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [43, 156, 82, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8312662320, 1538529402, 9642256775, 7166800888, 21308474816]
  a := ![247, 84, 250, 171, 542]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19818804504, -12427312930, -13568779343, 7166800888, 21308474816]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2365, -9862, 3217, 5221, 15862]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-2365, -9862, 3217, 5221, 15862]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![134, 136, 1, 0, 0], ![179, 41, 0, 1, 0], ![71, 167, 0, 0, 1]] where
  M :=![![![-2365, -9862, 3217, 5221, 15862], ![-4776, -19819, 6445, 10475, 31818], ![-9432, -39738, 13042, 21107, 64150], ![-19896, -80214, 25623, 41992, 127406], ![12240, 50244, -16232, -26462, -80345]]]
  hmulB := by decide  
  f := ![![![1141, 818, 327, 469, 1554]], ![![-3528, -1589, -687, -1087, -3598]], ![![-1334, -434, -200, -345, -1142]], ![![193, 321, 127, 156, 514]], ![![-2123, -867, -386, -622, -2057]]]
  g := ![![![-10436, -13851, 3217, 5221, 15862], ![-20931, -27780, 6445, 10475, 31818], ![-42217, -56033, 13042, 21107, 64150], ![-83748, -111144, 25623, 41992, 127406], ![52839, 70127, -16232, -26462, -80345]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P1 : CertificateIrreducibleZModOfList' 239 2 2 7 [100, 146, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 238], [0, 1]]
 g := ![![[207, 98], [188, 201], [93, 192], [46, 68], [174], [102, 157], [93, 1]], ![[0, 141], [0, 38], [24, 47], [156, 171], [174], [124, 82], [186, 238]]]
 h' := ![![[93, 238], [81, 215], [21, 100], [180, 108], [1, 207], [77, 202], [21, 184], [0, 1]], ![[0, 1], [0, 24], [0, 139], [186, 131], [132, 32], [221, 37], [164, 55], [93, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [129, 136]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N1 : CertifiedPrimeIdeal' SI239N1 239 where
  n := 2
  hpos := by decide
  P := [100, 146, 1]
  hirr := P239P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1268968, 222236, 1511866, 1123865, 3323417]
  a := ![232, 80, 235, 164, 509]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2671362, -3374396, 1511866, 1123865, 3323417]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N1 B_one_repr
lemma NI239N1 : Nat.card (O ⧸ I239N1) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-1141, -818, -327, -469, -1554]] ![![-2365, -9862, 3217, 5221, 15862]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![-239, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0, 0, 0]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]] where
  M :=![![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 5 2 7 [187, 81, 116, 24, 41, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [154, 114, 115, 145, 114], [149, 158, 205, 159, 238], [136, 0, 96, 98, 62], [2, 209, 66, 80, 68], [0, 1]]
 g := ![![[226, 157, 72, 192, 108], [71, 29, 25, 229], [186, 125, 85, 205], [208, 159, 216, 8], [235, 137, 240, 146, 221], [211, 200, 1], []], ![[92, 43, 99, 55, 50, 108, 67, 127], [213, 68, 236, 123], [157, 24, 214, 80], [239, 91, 157, 128], [107, 114, 3, 124, 23, 63, 57, 114], [140, 26, 235, 231, 87, 187, 183, 26], [36, 10, 177, 161, 3, 12, 146, 117]], ![[107, 3, 39, 70, 110, 112, 10, 211], [115, 214, 85, 236], [32, 30, 153, 212], [40, 105, 114, 77], [189, 93, 108, 38, 211, 20, 171, 48], [204, 27, 173, 187, 135, 195, 87, 200], [235, 155, 157, 172, 134, 212, 98, 214]], ![[190, 6, 19, 136, 120, 147, 79, 89], [1, 86, 48, 10], [216, 131, 132, 196], [170, 118, 97, 6], [202, 119, 110, 65, 120, 69, 43, 92], [154, 87, 137, 206, 227, 139, 169, 199], [198, 184, 221, 95, 172, 166, 225, 220]], ![[59, 18, 2, 230, 172, 36, 192, 22], [236, 128, 130, 135], [42, 137, 13, 48], [239, 226, 74, 154], [0, 159, 78, 141, 108, 209, 156, 213], [236, 100, 35, 140, 148, 147, 60, 138], [132, 153, 2, 31, 21, 34, 56, 168]]]
 h' := ![![[154, 114, 115, 145, 114], [28, 77, 14, 37, 95], [110, 61, 104, 142, 62], [46, 57, 140, 28, 143], [158, 82, 173, 191, 197], [67, 216, 107, 93, 170], [0, 0, 0, 1], [0, 1]], ![[149, 158, 205, 159, 238], [235, 63, 29, 147, 177], [209, 73, 96, 199, 72], [86, 36, 15, 68, 171], [215, 134, 0, 116, 176], [185, 43, 54, 223, 240], [166, 51, 182, 151, 113], [154, 114, 115, 145, 114]], ![[136, 0, 96, 98, 62], [87, 222, 7, 237, 144], [25, 3, 30, 185, 156], [226, 88, 135, 195, 137], [41, 89, 52, 191, 42], [68, 91, 138, 44, 226], [141, 189, 120, 173, 217], [149, 158, 205, 159, 238]], ![[2, 209, 66, 80, 68], [64, 191, 108, 230, 114], [144, 189, 189, 20, 144], [17, 64, 44, 154, 14], [156, 44, 37, 109, 27], [27, 96, 33, 81, 150], [227, 164, 115, 75, 82], [136, 0, 96, 98, 62]], ![[0, 1], [217, 170, 83, 72, 193], [103, 156, 63, 177, 48], [239, 237, 148, 37, 17], [180, 133, 220, 116, 40], [50, 36, 150, 41, 178], [147, 78, 65, 82, 70], [2, 209, 66, 80, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [178, 45, 51, 57], [], [], []]
 b := ![[], [233, 72, 156, 4, 120], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 5
  hpos := by decide
  P := [187, 81, 116, 24, 41, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2290855301955062334, -369586389219404272, -2786582308703400122, -2076999881965495701, -6115814146943645596]
  a := ![-359, -113, -376, -246, -788]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9505623659564574, -1533553482238192, -11562582193790042, -8618256771641061, -25376822186488156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 812990017201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def PBC241 : ContainsPrimesAboveP 241 ![I241N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![241, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 241 (by decide) 𝕀

instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45115, 3843, -77990, -59639, -166126]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![-45115, 3843, -77990, -59639, -166126]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![128, 92, 196, 1, 0], ![103, 42, 209, 0, 1]] where
  M :=![![![-45115, 3843, -77990, -59639, -166126], ![-306984, 18683, -528906, -401924, -1116662], ![-2138640, 96798, -3638543, -2758514, -7670892], ![-14511600, 695052, -24844208, -18829971, -52300612], ![5011224, -242211, 8576926, 6501755, 18061151]]]
  hmulB := by decide  
  f := ![![![451927, -385239, -61860, -50987, -193580]], ![![974856, 970459, 345050, 486070, 1623054]], ![![-3956256, -1966950, -876673, -1320314, -4353640]], ![![-2464016, -1362596, -582540, -867823, -2867324]], ![![-2952157, -1634394, -698439, -1040360, -3437467]]]
  g := ![![![98405, 49673, 184588, -59639, -166126], ![661974, 334245, 1241556, -401924, -1116662], ![4546028, 2295050, 8526879, -2758514, -7670892], ![31006724, 15656088, 58154016, -18829971, -52300612], ![-10707219, -5406263, -20081863, 6501755, 18061151]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [90, 113, 151, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [110, 179, 121], [241, 71, 130], [0, 1]]
 g := ![![[194, 226, 164], [110, 235, 41], [40, 36], [22, 180, 100], [17, 146, 195], [140, 6, 211], [1]], ![[104, 171, 105, 80], [234, 41, 245, 100], [31, 16], [137, 54, 209, 245], [248, 156, 101, 125], [210, 132, 30, 225], [102, 212, 193, 3]], ![[53, 129, 216, 128], [40, 115, 165, 71], [186, 100], [108, 223, 110, 163], [240, 245, 162, 216], [189, 225, 5, 216], [11, 242, 60, 248]]]
 h' := ![![[110, 179, 121], [140, 67, 179], [196, 152, 36], [28, 213, 245], [227, 240, 241], [201, 23, 114], [161, 138, 100], [0, 1]], ![[241, 71, 130], [33, 214, 234], [198, 91, 115], [224, 102, 247], [119, 167, 218], [158, 198, 84], [54, 79, 204], [110, 179, 121]], ![[0, 1], [246, 221, 89], [45, 8, 100], [138, 187, 10], [138, 95, 43], [81, 30, 53], [18, 34, 198], [241, 71, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 104], []]
 b := ![[], [70, 170, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [90, 113, 151, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6179395109, -955456750, -7614836997, -5680056244, -16682032535]
  a := ![-221, -70, -227, -154, -485]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9717598228, 4869542168, 18295701142, -5680056244, -16682032535]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 2, -34, -26, -72]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![-19, 2, -34, -26, -72]] 
 ![![251, 0, 0, 0, 0], ![132, 1, 0, 0, 0], ![146, 0, 1, 0, 0], ![55, 0, 0, 1, 0], ![72, 0, 0, 0, 1]] where
  M :=![![![-19, 2, -34, -26, -72], ![-144, 5, -240, -182, -508], ![-912, 60, -1597, -1212, -3356], ![-6720, 204, -11228, -8501, -23696], ![2304, -78, 3866, 2928, 8157]]]
  hmulB := by decide  
  f := ![![![14791, 1562, 1730, 3006, 9672]], ![![7716, 821, 904, 1570, 5052]], ![![8650, 896, 1007, 1752, 5636]], ![![3251, 382, 390, 673, 2168]], ![![4200, 438, 490, 852, 2741]]]
  g := ![![![45, 2, -34, -26, -72], ![322, 5, -240, -182, -508], ![2122, 60, -1597, -1212, -3356], ![15057, 204, -11228, -8501, -23696], ![-5180, -78, 3866, 2928, 8157]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 9, 226, 167, 462]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![139, 9, 226, 167, 462]] 
 ![![251, 0, 0, 0, 0], ![174, 1, 0, 0, 0], ![95, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![227, 0, 0, 0, 1]] where
  M :=![![![139, 9, 226, 167, 462], ![936, -11, 1574, 1184, 3286], ![6384, -222, 10843, 8198, 22772], ![43728, -1812, 74476, 56391, 156684], ![-15096, 591, -25686, -19439, -54007]]]
  hmulB := by decide  
  f := ![![![-28615, -3381, -3472, -5965, -19220]], ![![-19710, -2339, -2394, -4112, -13250]], ![![-10939, -1263, -1321, -2271, -7316]], ![![-4068, -540, -500, -865, -2788]], ![![-25807, -3042, -3132, -5378, -17329]]]
  g := ![![![-533, 9, 226, 167, 462], ![-3726, -11, 1574, 1184, 3286], ![-25695, -222, 10843, 8198, 22772], ![-176548, -1812, 74476, 56391, 156684], ![60883, 591, -25686, -19439, -54007]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![-45115, 3843, -77990, -59639, -166126]] ![![-19, 2, -34, -26, -72]]
  ![![89450449, -3958943, 152545196, 115571655, 321146438]] where
 M := ![![![89450449, -3958943, 152545196, 115571655, 321146438]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![89450449, -3958943, 152545196, 115571655, 321146438]] ![![139, 9, 226, 167, 462]]
  ![![251, 0, 0, 0, 0]] where
 M := ![![![1188267274819, -52634725100, 2026379156732, 1535251942102, 4266149739006]]]
 hmul := by decide  
 g := ![![![![4734132569, -209700100, 8073223732, 6116541602, 16996612506]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1, I251N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
    exact isPrimeI251N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0 ⊙ MulI251N1)


lemma PB2088I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB2088I5 : PrimesBelowBoundCertificateInterval O 197 251 2088 where
  m := 9
  g := ![4, 1, 3, 4, 2, 2, 2, 1, 3]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB2088I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1, I199N2, I199N3]
    · exact ![I211N0]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0, I227N1, I227N2, I227N3]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
    · exact ![I251N0, I251N1, I251N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![39601, 199, 199, 199]
    · exact ![418227202051]
    · exact ![49729, 49729, 223]
    · exact ![51529, 227, 227, 227]
    · exact ![12008989, 52441]
    · exact ![12649337, 54289]
    · exact ![13651919, 57121]
    · exact ![812990017201]
    · exact ![15813251, 251, 251]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
      exact NI199N2
      exact NI199N3
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
      exact NI227N2
      exact NI227N3
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
      exact NI251N2
  β := ![I199N1, I199N2, I199N3, I223N2, I227N1, I227N2, I227N3, I251N1, I251N2]
  Il := ![[I199N1, I199N2, I199N3], [], [I223N2], [I227N1, I227N2, I227N3], [], [], [], [], [I251N1, I251N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
