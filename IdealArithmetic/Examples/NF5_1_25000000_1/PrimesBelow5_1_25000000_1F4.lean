
import IdealArithmetic.Examples.NF5_1_25000000_1.RI5_1_25000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-107, -34, 14, -8, 57]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-107, -34, 14, -8, 57]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![55, 140, 1, 0, 0], ![10, 68, 0, 1, 0], ![132, 93, 0, 0, 1]] where
  M :=![![![-107, -34, 14, -8, 57], ![-212, -77, 26, -18, 115], ![-424, -150, 47, -36, 219], ![64, 18, -8, 5, -37], ![-268, -98, 30, -22, 137]]]
  hmulB := by decide  
  f := ![![![-11, 16, -4, -2, -3]], ![![16, -11, 16, 0, -23]], ![![11, -4, 13, 0, -22]], ![![6, -4, 6, -1, -9]], ![![0, 7, 6, -2, -16]]]
  g := ![![![-53, -43, 14, -8, 57], ![-106, -84, 26, -18, 115], ![-201, -157, 47, -36, 219], ![34, 27, -8, 5, -37], ![-126, -99, 30, -22, 137]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [10, 126, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 156], [0, 1]]
 g := ![![[44, 110], [75], [154, 109], [71, 148], [46, 19], [19], [1]], ![[0, 47], [75], [79, 48], [106, 9], [7, 138], [19], [1]]]
 h' := ![![[31, 156], [150, 61], [30, 46], [75, 57], [11, 73], [67, 126], [147, 31], [0, 1]], ![[0, 1], [0, 96], [43, 111], [115, 100], [76, 84], [48, 31], [9, 126], [31, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [6, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [10, 126, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-35138, -2828, -21694, -46858, 37086]
  a := ![26, 17, 31, 30, -91]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20820, 17654, -21694, -46858, 37086]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -3, -5, 0, 9]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![3, -3, -5, 0, 9]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![29, 70, 1, 0, 0], ![106, 82, 0, 1, 0], ![156, 56, 0, 0, 1]] where
  M :=![![![3, -3, -5, 0, 9], ![-36, -2, -13, -38, 27], ![-32, 27, 124, 84, -185], ![168, -32, -74, 79, 94], ![16, -18, -58, -32, 91]]]
  hmulB := by decide  
  f := ![![![259, -77, -29, -22, -39]], ![![200, 274, -47, 72, -271]], ![![143, 108, -27, 28, -130]], ![![278, 92, -44, 23, -168]], ![![332, 22, -46, 4, -137]]]
  g := ![![![-8, -1, -5, 0, 9], ![1, 16, -13, -38, 27], ![104, -33, 124, 84, -185], ![-132, -42, -74, 79, 94], ![-58, 10, -58, -32, 91]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P1 : CertificateIrreducibleZModOfList' 157 2 2 7 [32, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 156], [0, 1]]
 g := ![![[155, 76], [47], [3, 52], [97, 156], [41, 146], [14], [1]], ![[152, 81], [47], [34, 105], [33, 1], [122, 11], [14], [1]]]
 h' := ![![[64, 156], [19, 62], [61, 138], [36, 113], [101, 28], [105, 97], [125, 64], [0, 1]], ![[0, 1], [62, 95], [101, 19], [46, 44], [9, 129], [33, 60], [139, 93], [64, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135]]
 b := ![[], [38, 146]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N1 : CertifiedPrimeIdeal' SI157N1 157 where
  n := 2
  hpos := by decide
  P := [32, 93, 1]
  hirr := P157P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2291112, -817459, -2894277, -3886746, 5339717]
  a := ![239, 117, 236, 172, -835]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2161515, 1410643, -2894277, -3886746, 5339717]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N1 B_one_repr
lemma NI157N1 : Nat.card (O ⧸ I157N1) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, 29, 1, 8, -12]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![-29, 29, 1, 8, -12]] 
 ![![157, 0, 0, 0, 0], ![104, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![73, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-29, 29, 1, 8, -12], ![32, -44, -1, -12, 20], ![-56, 55, 2, 16, -24], ![36, -38, -2, -11, 17], ![-12, 8, 0, 2, -3]]]
  hmulB := by decide  
  f := ![![![23, -3, -1, 12, -36]], ![![16, -2, -1, 8, -24]], ![![3, 0, -1, 0, -4]], ![![11, -1, 1, 7, -19]], ![![4, 0, 0, 2, -5]]]
  g := ![![![-22, 29, 1, 8, -12], ![33, -44, -1, -12, 20], ![-42, 55, 2, 16, -24], ![29, -38, -2, -11, 17], ![-6, 8, 0, 2, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-107, -34, 14, -8, 57]] ![![3, -3, -5, 0, 9]]
  ![![23, -3, -1, 12, -36]] where
 M := ![![![23, -3, -1, 12, -36]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![23, -3, -1, 12, -36]] ![![-29, 29, 1, 8, -12]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0, 0, 0]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![0, 0, 0, 0, 163]] where
  M :=![![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![0, 0, 0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 5 2 7 [25, 59, 73, 122, 110, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 4, 102, 134, 41], [52, 104, 127, 38, 59], [151, 127, 153, 17, 42], [118, 90, 107, 137, 21], [0, 1]]
 g := ![![[102, 103, 100, 73, 47], [20, 38, 59, 88, 46], [4, 7, 125, 121], [139, 51, 52, 58], [78, 61, 3, 38], [1], []], ![[34, 82, 12, 64, 119, 112, 43, 22], [12, 50, 143, 89, 18, 139, 56, 10], [78, 12, 116, 151], [101, 136, 126, 156], [122, 61, 65, 35], [161, 2, 44, 64, 67, 9, 3, 150], [53, 159, 162, 51]], ![[51, 113, 86, 18, 88, 152, 114, 139], [68, 81, 11, 130, 107, 15, 50, 112], [1, 125, 83, 133], [40, 3, 109, 81], [92, 132, 25, 40], [126, 117, 96, 112, 94, 36, 151, 67], [15, 146, 60, 58]], ![[38, 22, 105, 35, 70, 62, 149, 98], [153, 135, 24, 140, 15, 45, 72, 125], [22, 111, 147, 133], [48, 107, 156, 14], [34, 59, 124, 87], [38, 49, 76, 110, 110, 67, 99, 19], [123, 144, 54, 134]], ![[160, 10, 162, 126, 53, 40, 36, 100], [63, 56, 132, 26, 113, 139, 4, 83], [84, 88, 147, 40], [63, 54, 149, 58], [20, 8, 123, 84], [45, 34, 91, 72, 77, 138, 132, 96], [75, 63, 113, 115]]]
 h' := ![![[58, 4, 102, 134, 41], [152, 45, 124, 125, 79], [120, 126, 83, 111, 32], [63, 78, 160, 108, 152], [142, 83, 45, 107, 59], [138, 104, 90, 41, 53], [0, 0, 1], [0, 1]], ![[52, 104, 127, 38, 59], [75, 20, 146, 157, 67], [80, 147, 13, 88, 23], [143, 49, 145, 3, 71], [68, 50, 4, 99, 112], [99, 83, 44, 90, 144], [83, 45, 90, 5, 130], [58, 4, 102, 134, 41]], ![[151, 127, 153, 17, 42], [42, 133, 162, 4, 96], [21, 99, 3, 41, 137], [32, 8, 102, 80, 40], [39, 117, 53, 160, 154], [63, 131, 146, 42, 140], [47, 87, 101, 13, 134], [52, 104, 127, 38, 59]], ![[118, 90, 107, 137, 21], [20, 91, 106, 86, 130], [127, 126, 131, 128, 153], [5, 45, 146, 146, 40], [8, 21, 85, 25, 60], [83, 135, 17, 5, 24], [3, 113, 152, 43, 73], [151, 127, 153, 17, 42]], ![[0, 1], [43, 37, 114, 117, 117], [115, 154, 96, 121, 144], [111, 146, 99, 152, 23], [120, 55, 139, 98, 104], [72, 36, 29, 148, 128], [150, 81, 145, 102, 152], [118, 90, 107, 137, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 123, 29, 160], [], [], []]
 b := ![[], [37, 79, 17, 151, 12], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 5
  hpos := by decide
  P := [25, 59, 73, 122, 110, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2169026471158, -1094213547324, -5556056078430, -6569475709480, 8918352948184]
  a := ![19, 11, 21, 18, -66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13306910866, -6712966548, -34086233610, -40303531960, 54713821768]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 115063617043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![171, -86, -42, -20, -59]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![171, -86, -42, -20, -59]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![34, 26, 1, 0, 0], ![96, 119, 0, 1, 0], ![130, 53, 0, 0, 1]] where
  M :=![![![171, -86, -42, -20, -59], ![276, 169, -90, 50, -317], ![1168, 86, -211, 24, -601], ![-64, 142, 20, 35, -29], ![756, 158, -138, 42, -449]]]
  hmulB := by decide  
  f := ![![![65, -48, -176, -94, 267]], ![![-880, 77, -24, -768, 143]], ![![-118, 6, -21, -118, 47]], ![![-572, 21, -138, -603, 284]], ![![-230, -15, -154, -326, 268]]]
  g := ![![![67, 39, -42, -20, -59], ![238, 80, -90, 50, -317], ![504, 207, -211, 24, -601], ![-2, -18, 20, 35, -29], ![358, 135, -138, 42, -449]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [18, 128, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 166], [0, 1]]
 g := ![![[137, 65], [65, 54], [62, 144], [141], [100], [133, 18], [1]], ![[0, 102], [0, 113], [0, 23], [141], [100], [0, 149], [1]]]
 h' := ![![[39, 166], [166, 30], [53, 80], [134, 155], [0, 108], [111, 10], [149, 39], [0, 1]], ![[0, 1], [0, 137], [0, 87], [0, 12], [37, 59], [0, 157], [0, 128], [39, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [157, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [18, 128, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-589963, -129161, -523674, -851323, 1000746]
  a := ![-107, -61, -118, -103, 375]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-186557, 369786, -523674, -851323, 1000746]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39435, -45478, -1316, -12484, 19919]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![39435, -45478, -1316, -12484, 19919]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![108, 18, 1, 0, 0], ![128, 146, 0, 1, 0], ![119, 115, 0, 0, 1]] where
  M :=![![![39435, -45478, -1316, -12484, 19919], ![-54708, 63087, 1826, 17318, -27631], ![75888, -87518, -2533, -24024, 38333], ![-50588, 58338, 1688, 16013, -25551], ![12892, -14870, -430, -4082, 6513]]]
  hmulB := by decide  
  f := ![![![361, 92, -66, 22, -239]], ![![912, 251, -128, 104, -563]], ![![344, 90, -59, 26, -221]], ![![1072, 290, -162, 107, -675]], ![![893, 241, -136, 88, -563]]]
  g := ![![![-3538, -2933, -1316, -12484, 19919], ![4907, 4068, 1826, 17318, -27631], ![-6809, -5645, -2533, -24024, 38333], ![4539, 3763, 1688, 16013, -25551], ![-1157, -959, -430, -4082, 6513]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [129, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [155, 166], [0, 1]]
 g := ![![[70, 57], [66, 132], [12, 18], [11], [27], [32, 144], [1]], ![[54, 110], [152, 35], [130, 149], [11], [27], [141, 23], [1]]]
 h' := ![![[155, 166], [3, 70], [122, 93], [87, 128], [62, 126], [47, 19], [38, 155], [0, 1]], ![[0, 1], [165, 97], [8, 74], [54, 39], [53, 41], [153, 148], [15, 12], [155, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88]]
 b := ![[], [97, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [129, 12, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-94006, 2886, -18266, -93370, 41914]
  a := ![35, 28, 52, 60, -123]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![52948, 54752, -18266, -93370, 41914]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33599, -38777, -1121, -10644, 16988]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![33599, -38777, -1121, -10644, 16988]] 
 ![![167, 0, 0, 0, 0], ![123, 1, 0, 0, 0], ![68, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![91, 0, 0, 0, 1]] where
  M :=![![![33599, -38777, -1121, -10644, 16988], ![-46664, 53766, 1557, 14760, -23544], ![64656, -74627, -2160, -20484, 32688], ![-43108, 49738, 1438, 13653, -21789], ![10972, -12688, -368, -3482, 5557]]]
  hmulB := by decide  
  f := ![![![-3087, 221, -297, -2880, 828]], ![![-2259, 177, -152, -2052, 504]], ![![-972, 33, -250, -1040, 504]], ![![-1433, 73, -265, -1445, 583]], ![![-1831, 145, -117, -1658, 399]]]
  g := ![![![23594, -38777, -1121, -10644, 16988], ![-32722, 53766, 1557, 14760, -23544], ![45411, -74627, -2160, -20484, 32688], ![-30264, 49738, 1438, 13653, -21789], ![7721, -12688, -368, -3482, 5557]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![171, -86, -42, -20, -59]] ![![39435, -45478, -1316, -12484, 19919]]
  ![![8512109, -9815894, -284076, -2694526, 4299182]] where
 M := ![![![8512109, -9815894, -284076, -2694526, 4299182]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![8512109, -9815894, -284076, -2694526, 4299182]] ![![33599, -38777, -1121, -10644, 16988]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![889006261763, -1025204023249, -29668644351, -281424586054, 449024821128]]]
 hmul := by decide  
 g := ![![![![5323390789, -6138946247, -177656553, -1685177162, 2688771384]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 2, -2, -2, 2]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![3, 2, -2, -2, 2]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![54, 86, 1, 0, 0], ![23, 68, 0, 1, 0], ![165, 155, 0, 0, 1]] where
  M :=![![![3, 2, -2, -2, 2], ![-4, 5, 6, -2, -8], ![36, 6, 25, 50, -38], ![-4, -14, -50, -43, 80], ![-16, 0, -12, -24, 25]]]
  hmulB := by decide  
  f := ![![![-121, 170, 6, 46, -74]], ![![204, -207, -2, -58, 100]], ![![62, -48, 1, -14, 26]], ![![65, -60, 0, -17, 30]], ![![67, -23, 4, -8, 19]]]
  g := ![![![-1, 0, -2, -2, 2], ![6, 5, 6, -2, -8], ![22, 2, 25, 50, -38], ![-55, -30, -50, -43, 80], ![-17, -7, -12, -24, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [96, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [121, 172], [0, 1]]
 g := ![![[51, 164], [24], [75, 67], [7, 21], [132], [164, 109], [1]], ![[0, 9], [24], [51, 106], [126, 152], [132], [32, 64], [1]]]
 h' := ![![[121, 172], [149, 106], [66, 102], [20, 76], [131, 59], [172, 85], [77, 121], [0, 1]], ![[0, 1], [0, 67], [125, 71], [47, 97], [4, 114], [77, 88], [13, 52], [121, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [48, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [96, 52, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-83480, 15532, 38712, -39196, -49672]
  a := ![-28, -30, -56, -78, 98]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![40020, 40756, 38712, -39196, -49672]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 30, 0, 8, -16]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-17, 30, 0, 8, -16]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![31, 138, 1, 0, 0], ![126, 22, 0, 1, 0], ![10, 74, 0, 0, 1]] where
  M :=![![![-17, 30, 0, 8, -16], ![48, -33, -2, -8, 8], ![-16, 62, -5, 16, -32], ![20, -36, 0, -15, 18], ![8, 16, 0, 4, -15]]]
  hmulB := by decide  
  f := ![![![-93, -30, 12, -8, 48]], ![![-176, -65, 26, -8, 88]], ![![-159, -58, 23, -8, 80]], ![![-90, -30, 12, -7, 46]], ![![-82, -30, 12, -4, 41]]]
  g := ![![![-5, 6, 0, 8, -16], ![6, -1, -2, -8, 8], ![-9, 16, -5, 16, -32], ![10, -6, 0, -15, 18], ![-2, 6, 0, 4, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P1 : CertificateIrreducibleZModOfList' 173 2 2 7 [95, 146, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 172], [0, 1]]
 g := ![![[7, 51], [106], [38, 158], [144, 57], [138], [21, 37], [1]], ![[0, 122], [106], [152, 15], [126, 116], [138], [155, 136], [1]]]
 h' := ![![[27, 172], [147, 33], [23, 25], [160, 136], [25, 24], [81, 22], [78, 27], [0, 1]], ![[0, 1], [0, 140], [6, 148], [26, 37], [154, 149], [156, 151], [115, 146], [27, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114]]
 b := ![[], [9, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N1 : CertifiedPrimeIdeal' SI173N1 173 where
  n := 2
  hpos := by decide
  P := [95, 146, 1]
  hirr := P173P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31968, 13989, 42951, 12073, -58046]
  a := ![17, 23, 43, 61, -53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13319, -10887, 42951, 12073, -58046]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N1 B_one_repr
lemma NI173N1 : Nat.card (O ⧸ I173N1) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 8, -2, 2, -10]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![15, 8, -2, 2, -10]] 
 ![![173, 0, 0, 0, 0], ![122, 1, 0, 0, 0], ![167, 0, 1, 0, 0], ![69, 0, 0, 1, 0], ![163, 0, 0, 0, 1]] where
  M :=![![![15, 8, -2, 2, -10], ![36, 9, -4, 2, -16], ![60, 28, -7, 6, -34], ![-8, -6, 2, -1, 6], ![40, 16, -4, 4, -21]]]
  hmulB := by decide  
  f := ![![![-53, -4, -6, -14, 34]], ![![-38, -3, -4, -10, 24]], ![![-51, -4, -5, -12, 32]], ![![-21, -2, -4, -7, 16]], ![![-51, -4, -6, -14, 33]]]
  g := ![![![5, 8, -2, 2, -10], ![12, 9, -4, 2, -16], ![17, 28, -7, 6, -34], ![-3, -6, 2, -1, 6], ![11, 16, -4, 4, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![3, 2, -2, -2, 2]] ![![-17, 30, 0, 8, -16]]
  ![![53, 4, 6, 14, -34]] where
 M := ![![![53, 4, 6, 14, -34]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![53, 4, 6, 14, -34]] ![![15, 8, -2, 2, -10]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![-173, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0, 0, 0]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![0, 0, 0, 179, 0], ![0, 0, 0, 0, 179]] where
  M :=![![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![0, 0, 0, 179, 0], ![0, 0, 0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 5 2 7 [61, 147, 165, 71, 27, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 82, 117, 61, 97], [73, 124, 178, 79, 11], [59, 104, 140, 5, 148], [175, 47, 102, 34, 102], [0, 1]]
 g := ![![[161, 147, 14], [169, 62, 48, 116, 117], [33, 31, 5, 117], [86, 13, 101, 121], [20, 102, 74, 82, 13], [1], []], ![[102, 109, 83, 127, 7, 104, 49, 132], [106, 22, 103, 135, 99, 122, 49, 86], [60, 92, 103, 89], [69, 82, 156, 27], [80, 147, 27, 104, 148, 102, 173, 33], [87, 159, 16, 9, 140, 137, 171, 98], [56, 152, 157, 101]], ![[127, 85, 130, 121, 135, 151, 44, 78], [34, 109, 19, 3, 31, 30, 60, 53], [126, 136, 35, 138], [41, 87, 173, 15], [39, 3, 93, 4, 118, 49, 126, 69], [46, 56, 41, 135, 104, 9, 15, 53], [7, 68, 82, 121]], ![[63, 34, 25, 16, 153, 26, 68, 119], [91, 159, 75, 24, 171, 139, 167, 94], [147, 7, 127, 144], [88, 61, 139, 106], [7, 149, 5, 141, 168, 103, 175, 86], [163, 83, 175, 40, 25, 110, 160, 91], [26, 4, 56, 66]], ![[58, 50, 163, 148, 168, 44, 175, 50], [108, 154, 33, 134, 175, 154, 134, 86], [166, 113, 142, 151], [125, 83, 142, 139], [162, 117, 137, 129, 63, 122, 29, 32], [29, 165, 92, 102, 72, 149, 176, 165], [123, 65, 77, 22]]]
 h' := ![![[24, 82, 117, 61, 97], [73, 176, 48, 67], [124, 19, 35, 39, 81], [139, 137, 121, 144, 98], [33, 108, 138, 91, 168], [118, 32, 14, 108, 152], [0, 0, 1], [0, 1]], ![[73, 124, 178, 79, 11], [164, 21, 169, 99, 29], [121, 158, 67, 142, 51], [77, 25, 130, 0, 140], [166, 105, 19, 69, 57], [104, 165, 136, 56, 104], [24, 36, 177, 157, 174], [24, 82, 117, 61, 97]], ![[59, 104, 140, 5, 148], [147, 35, 131, 21, 168], [1, 62, 160, 91, 80], [166, 109, 122, 103, 73], [124, 5, 142, 63, 33], [172, 28, 148, 123, 13], [69, 39, 151, 3, 80], [73, 124, 178, 79, 11]], ![[175, 47, 102, 34, 102], [136, 2, 111, 52, 163], [35, 44, 109, 166, 53], [54, 105, 44, 130, 12], [125, 47, 34, 36, 74], [70, 61, 138, 14, 19], [105, 151, 68, 89, 97], [59, 104, 140, 5, 148]], ![[0, 1], [169, 124, 78, 119, 177], [45, 75, 166, 99, 93], [133, 161, 120, 160, 35], [47, 93, 25, 99, 26], [115, 72, 101, 57, 70], [31, 132, 140, 109, 7], [175, 47, 102, 34, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 142, 64, 20], [], [], []]
 b := ![[], [104, 30, 46, 148, 57], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 5
  hpos := by decide
  P := [61, 147, 165, 71, 27, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41868347378, 1706390353, 24208723972, 56218186499, -42733568401]
  a := ![-1, -5, -8, -15, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![233901382, 9532907, 135244268, 314068081, -238735019]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 183765996899 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def PBC179 : ContainsPrimesAboveP 179 ![I179N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![179, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 179 (by decide) 𝕀

instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1761, 2030, 58, 556, -888]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-1761, 2030, 58, 556, -888]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![68, 47, 1, 0, 0], ![72, 75, 0, 1, 0], ![163, 104, 0, 0, 1]] where
  M :=![![![-1761, 2030, 58, 556, -888], ![2440, -2815, -78, -772, 1228], ![-3368, 3906, 117, 1092, -1720], ![2248, -2608, -96, -741, 1174], ![-584, 664, 16, 172, -285]]]
  hmulB := by decide  
  f := ![![![-3221, -1254, 310, -284, 1592]], ![![-5800, -2343, 502, -524, 2788]], ![![-2772, -1103, 251, -248, 1348]], ![![-3672, -1465, 330, -329, 1782]], ![![-6267, -2490, 570, -560, 3051]]]
  g := ![![![547, 276, 58, 556, -888], ![-756, -381, -78, -772, 1228], ![1052, 527, 117, 1092, -1720], ![-714, -357, -96, -741, 1174], ![179, 92, 16, 172, -285]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [65, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 180], [0, 1]]
 g := ![![[180, 39], [38], [156, 152], [147], [68, 73], [105, 62], [1]], ![[0, 142], [38], [81, 29], [147], [107, 108], [153, 119], [1]]]
 h' := ![![[65, 180], [80, 138], [177, 20], [22, 141], [105, 131], [53, 142], [116, 65], [0, 1]], ![[0, 1], [0, 43], [29, 161], [137, 40], [113, 50], [52, 39], [178, 116], [65, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128]]
 b := ![[], [92, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [65, 116, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-137478, -11316, -63891, -158978, 133884]
  a := ![-45, -32, -57, -62, 159]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-34086, 5475, -63891, -158978, 133884]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 16, -4, 4, -18]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![41, 16, -4, 4, -18]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![94, 88, 1, 0, 0], ![57, 80, 0, 1, 0], ![80, 118, 0, 0, 1]] where
  M :=![![![41, 16, -4, 4, -18], ![64, 29, -8, 0, -26], ![104, 56, 13, 20, -78], ![0, -16, -4, 17, 22], ![72, 28, -12, 4, -15]]]
  hmulB := by decide  
  f := ![![![637, -744, -20, -204, 330]], ![![-912, 1025, 32, 280, -438]], ![![-106, 104, 5, 28, -38]], ![![-207, 224, 8, 61, -92]], ![![-312, 338, 12, 92, -139]]]
  g := ![![![9, 12, -4, 4, -18], ![16, 21, -8, 0, -26], ![22, 36, 13, 20, -78], ![-13, -20, -4, 17, 22], ![12, 14, -12, 4, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P1 : CertificateIrreducibleZModOfList' 181 2 2 7 [27, 137, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 180], [0, 1]]
 g := ![![[52, 114], [125], [94, 64], [64], [30, 114], [91, 126], [1]], ![[0, 67], [125], [14, 117], [64], [159, 67], [24, 55], [1]]]
 h' := ![![[44, 180], [80, 64], [177, 46], [57, 173], [95, 8], [77, 64], [154, 44], [0, 1]], ![[0, 1], [0, 117], [29, 135], [67, 8], [85, 173], [178, 117], [99, 137], [44, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [103, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N1 : CertifiedPrimeIdeal' SI181N1 181 where
  n := 2
  hpos := by decide
  P := [27, 137, 1]
  hirr := P181P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40753, -3030, -17410, -46226, 37659]
  a := ![-23, -17, -32, -35, 81]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6729, 4328, -17410, -46226, 37659]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N1 B_one_repr
lemma NI181N1 : Nat.card (O ⧸ I181N1) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77, 38, -2, 8, -30]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![77, 38, -2, 8, -30]] 
 ![![181, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![56, 0, 1, 0, 0], ![131, 0, 0, 1, 0], ![105, 0, 0, 0, 1]] where
  M :=![![![77, 38, -2, 8, -30], ![104, 59, 2, 12, -34], ![112, 82, 15, 16, -18], ![-72, -32, 4, -7, 32], ![48, 44, 12, 8, 1]]]
  hmulB := by decide  
  f := ![![![185, -182, 10, -16, 54]], ![![46, -45, 2, -4, 14]], ![![56, -58, 3, -8, 18]], ![![135, -130, 10, -7, 34]], ![![109, -106, 6, -8, 31]]]
  g := ![![![3, 38, -2, 8, -30], ![-4, 59, 2, 12, -34], ![-26, 82, 15, 16, -18], ![-7, -32, 4, -7, 32], ![-21, 44, 12, 8, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-1761, 2030, 58, 556, -888]] ![![41, 16, -4, 4, -18]]
  ![![-185, 182, -10, 16, -54]] where
 M := ![![![-185, 182, -10, 16, -54]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![-185, 182, -10, 16, -54]] ![![77, 38, -2, 8, -30]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![-181, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-813, -356, 52, -78, 364]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-813, -356, 52, -78, 364]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![44, 17, 1, 0, 0], ![173, 26, 0, 1, 0], ![176, 126, 0, 0, 1]] where
  M :=![![![-813, -356, 52, -78, 364], ![-1300, -605, 60, -130, 546], ![-1924, -980, 35, -202, 728], ![660, 270, -58, 57, -308], ![-1072, -572, 0, -120, 381]]]
  hmulB := by decide  
  f := ![![![-5923, 6832, 200, 1878, -2996]], ![![8228, -9479, -280, -2598, 4158]], ![![-692, 799, 23, 220, -350]], ![![-4205, 4852, 142, 1335, -2128]], ![![-40, 54, 0, 20, -23]]]
  g := ![![![-281, -236, 52, -78, 364], ![-406, -351, 60, -130, 546], ![-506, -461, 35, -202, 728], ![249, 202, -58, 57, -308], ![-248, -238, 0, -120, 381]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [127, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 190], [0, 1]]
 g := ![![[35, 180], [178, 156], [70, 117], [101, 8], [51, 162], [188, 30], [1]], ![[34, 11], [88, 35], [98, 74], [67, 183], [31, 29], [156, 161], [1]]]
 h' := ![![[139, 190], [123, 84], [87, 164], [161, 133], [17, 77], [190, 60], [64, 139], [0, 1]], ![[0, 1], [148, 107], [154, 27], [121, 58], [24, 114], [126, 131], [94, 52], [139, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [104, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [127, 52, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-103, 689, 3323, 3293, -4142]
  a := ![2, 5, 9, 15, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![68, 1992, 3323, 3293, -4142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![365, -430, -12, -118, 190]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![365, -430, -12, -118, 190]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![47, 113, 1, 0, 0], ![129, 58, 0, 1, 0], ![84, 61, 0, 0, 1]] where
  M :=![![![365, -430, -12, -118, 190], ![-524, 589, 18, 162, -256], ![700, -830, -23, -226, 366], ![-472, 550, 14, 149, -240], ![112, -144, -4, -40, 65]]]
  hmulB := by decide  
  f := ![![![35, 6, -4, 6, -34]], ![![124, 19, -26, 22, -60]], ![![83, 13, -17, 14, -44]], ![![61, 10, -10, 11, -42]], ![![56, 9, -10, 10, -35]]]
  g := ![![![1, -20, -12, -118, 190], ![-4, 25, 18, 162, -256], ![1, -39, -23, -226, 366], ![-1, 26, 14, 149, -240], ![0, -7, -4, -40, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P1 : CertificateIrreducibleZModOfList' 191 2 2 7 [187, 177, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 190], [0, 1]]
 g := ![![[99, 125], [64, 169], [55, 86], [106, 13], [123, 78], [182, 5], [1]], ![[130, 66], [138, 22], [113, 105], [97, 178], [69, 113], [61, 186], [1]]]
 h' := ![![[14, 190], [65, 121], [29, 13], [42, 75], [110, 83], [155, 101], [4, 14], [0, 1]], ![[0, 1], [40, 70], [20, 178], [137, 116], [126, 108], [41, 90], [9, 177], [14, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [128, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N1 : CertifiedPrimeIdeal' SI191N1 191 where
  n := 2
  hpos := by decide
  P := [187, 177, 1]
  hirr := P191P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-953513, -60076, -465434, -1145438, 887509]
  a := ![127, 90, 156, 164, -441]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![492841, 339431, -465434, -1145438, 887509]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N1 B_one_repr
lemma NI191N1 : Nat.card (O ⧸ I191N1) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 6, 0, 0, -2]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![-7, 6, 0, 0, -2]] 
 ![![191, 0, 0, 0, 0], ![61, 1, 0, 0, 0], ![99, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![91, 0, 0, 0, 1]] where
  M :=![![![-7, 6, 0, 0, -2], ![8, -7, 6, 4, -6], ![16, 6, -11, 16, 10], ![-28, -8, -16, -45, 32], ![-16, 4, 4, -8, -5]]]
  hmulB := by decide  
  f := ![![![3783, 1430, -396, 328, -1922]], ![![1245, 471, -130, 108, -632]], ![![2027, 768, -211, 176, -1028]], ![![957, 362, -100, 83, -486]], ![![1843, 698, -192, 160, -935]]]
  g := ![![![-1, 6, 0, 0, -2], ![1, -7, 6, 4, -6], ![-5, 6, -11, 16, 10], ![7, -8, -16, -45, 32], ![1, 4, 4, -8, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-813, -356, 52, -78, 364]] ![![365, -430, -12, -118, 190]]
  ![![3783, 1430, -396, 328, -1922]] where
 M := ![![![3783, 1430, -396, 328, -1922]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![3783, 1430, -396, 328, -1922]] ![![-7, 6, 0, 0, -2]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![191, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0, 0, 0]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![0, 0, 0, 0, 193]] where
  M :=![![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![0, 0, 0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 5 2 7 [192, 183, 37, 34, 140, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 95, 167, 131, 71], [63, 14, 108, 117, 145], [36, 116, 64, 165, 107], [116, 160, 47, 166, 63], [0, 1]]
 g := ![![[31, 115, 23, 178, 134], [147, 186, 92, 157], [71, 172, 101, 161], [182, 179, 21, 179], [77, 27, 47, 118], [53, 1], []], ![[158, 9, 105, 60, 32, 21, 120, 155], [121, 127, 83, 161], [90, 10, 168, 50], [73, 43, 98, 31], [72, 73, 120, 177], [88, 131, 187, 92], [184, 46, 119, 182, 131, 178, 53, 89]], ![[35, 181, 129, 157, 39, 66, 109, 75], [116, 142, 140, 162], [187, 28, 24, 179], [177, 102, 97, 48], [28, 48, 47, 107], [83, 164, 143, 130], [97, 74, 168, 125, 66, 97, 68, 190]], ![[52, 83, 170, 61, 64, 100, 123, 108], [66, 183, 190, 130], [99, 163, 123, 138], [174, 151, 0, 161], [45, 92, 181, 170], [168, 172, 166, 109], [129, 18, 184, 127, 61, 134, 152, 72]], ![[94, 13, 86, 154, 31, 75, 171, 186], [95, 122, 75, 75], [161, 111, 129, 23], [77, 157, 117, 93], [82, 110, 68, 46], [48, 157, 157, 112], [87, 37, 38, 92, 1, 66, 2, 112]]]
 h' := ![![[31, 95, 167, 131, 71], [40, 9, 45, 42, 83], [146, 36, 161, 10, 100], [70, 107, 165, 162, 136], [184, 148, 55, 141, 117], [53, 145, 172, 91, 73], [0, 0, 0, 1], [0, 1]], ![[63, 14, 108, 117, 145], [130, 16, 106, 146, 174], [190, 188, 77, 152, 136], [183, 94, 5, 186, 67], [127, 30, 157, 76, 113], [21, 14, 102, 42, 131], [60, 167, 34, 130, 51], [31, 95, 167, 131, 71]], ![[36, 116, 64, 165, 107], [181, 111, 65, 83, 140], [79, 23, 51, 45, 82], [49, 101, 88, 99, 76], [114, 181, 115, 189, 137], [146, 57, 108, 180, 53], [16, 25, 6, 165, 55], [63, 14, 108, 117, 145]], ![[116, 160, 47, 166, 63], [130, 119, 41, 93, 155], [185, 190, 44, 96, 138], [146, 78, 85, 69, 36], [101, 13, 45, 130, 57], [40, 73, 134, 180, 154], [79, 117, 43, 43, 130], [36, 116, 64, 165, 107]], ![[0, 1], [63, 131, 129, 22, 27], [136, 142, 53, 83, 123], [174, 6, 43, 63, 71], [167, 14, 14, 43, 155], [49, 97, 63, 86, 168], [192, 77, 110, 47, 150], [116, 160, 47, 166, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [148, 110, 184, 102], [], [], []]
 b := ![[], [148, 57, 90, 145, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 5
  hpos := by decide
  P := [192, 183, 37, 34, 140, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-79262561597801, 3584698840932, -16656939680578, -81620716546440, 35443392733648]
  a := ![31, 23, 39, 42, -108]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-410686847657, 18573569124, -86305386946, -422905267080, 183644521936]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 267785184193 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def PBC193 : ContainsPrimesAboveP 193 ![I193N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![193, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 193 (by decide) 𝕀

instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1037, -335, -1851, -2456, 3009]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-1037, -335, -1851, -2456, 3009]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![70, 121, 1, 0, 0], ![113, 40, 0, 1, 0], ![30, 182, 0, 0, 1]] where
  M :=![![![-1037, -335, -1851, -2456, 3009], ![-7124, 2024, 5787, -1142, -8165], ![34944, 947, 18166, 45188, -32489], ![-5796, -10296, -46398, -44383, 72998], ![-15536, -1106, -11002, -22576, 19005]]]
  hmulB := by decide  
  f := ![![![404691, -464925, -13603, -127642, 203201]], ![![-557520, 646372, 18437, 177396, -283891]], ![![-194674, 227271, 6357, 62358, -100186]], ![![116299, -132411, -3971, -36365, 57589]], ![![-452758, 525588, 14938, 144240, -230999]]]
  g := ![![![1603, -1146, -1851, -2456, 3009], ![-194, 4231, 5787, -1142, -8165], ![-27250, 9687, 18166, 45188, -32489], ![30799, -29982, -46398, -44383, 72998], ![13886, -6222, -11002, -22576, 19005]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [63, 172, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 196], [0, 1]]
 g := ![![[34, 172], [196], [77, 34], [10], [133], [53], [25, 1]], ![[0, 25], [196], [139, 163], [10], [133], [53], [50, 196]]]
 h' := ![![[25, 196], [23, 70], [74, 183], [20, 25], [16, 73], [11, 85], [1, 168], [0, 1]], ![[0, 1], [0, 127], [118, 14], [54, 172], [68, 124], [166, 112], [64, 29], [25, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [102, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [63, 172, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2168, -9604, -19193, -7118, 45860]
  a := ![-17, -5, -8, 4, 61]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3908, -29183, -19193, -7118, 45860]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-239, 268, 6, 74, -121]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-239, 268, 6, 74, -121]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![112, 157, 1, 0, 0], ![79, 190, 0, 1, 0], ![7, 112, 0, 0, 1]] where
  M :=![![![-239, 268, 6, 74, -121], ![336, -381, -16, -104, 155], ![-412, 528, 3, 146, -263], ![312, -344, -10, -95, 151], ![-44, 94, -6, 26, -63]]]
  hmulB := by decide  
  f := ![![![9, -2, 20, 32, -29]], ![![52, -35, -90, -22, 137]], ![![44, -29, -61, -2, 94]], ![![55, -34, -76, -5, 116]], ![![31, -20, -50, -10, 76]]]
  g := ![![![-30, -6, 6, 74, -121], ![47, 23, -16, -104, 155], ![-53, 9, 3, 146, -263], ![40, 12, -10, -95, 151], ![-5, 16, -6, 26, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P1 : CertificateIrreducibleZModOfList' 197 2 2 7 [142, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [133, 196], [0, 1]]
 g := ![![[6, 154], [9], [88, 92], [16], [16], [196], [133, 1]], ![[0, 43], [9], [110, 105], [16], [16], [196], [69, 196]]]
 h' := ![![[133, 196], [37, 96], [112, 3], [141, 17], [7, 4], [30, 4], [26, 14], [0, 1]], ![[0, 1], [0, 101], [117, 194], [38, 180], [145, 193], [168, 193], [115, 183], [133, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [113, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N1 : CertifiedPrimeIdeal' SI197N1 197 where
  n := 2
  hpos := by decide
  P := [142, 64, 1]
  hirr := P197P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-520325, 22808, -81859, -502422, 197556]
  a := ![83, 68, 123, 144, -289]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![238357, 437607, -81859, -502422, 197556]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N1 B_one_repr
lemma NI197N1 : Nat.card (O ⧸ I197N1) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-601, 617, 25, 170, -250]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![-601, 617, 25, 170, -250]] 
 ![![197, 0, 0, 0, 0], ![116, 1, 0, 0, 0], ![137, 0, 1, 0, 0], ![165, 0, 0, 1, 0], ![112, 0, 0, 0, 1]] where
  M :=![![![-601, 617, 25, 170, -250], ![660, -916, -13, -250, 440], ![-1260, 1147, 58, 318, -430], ![736, -804, -28, -221, 339], ![-308, 160, 20, 46, -25]]]
  hmulB := by decide  
  f := ![![![-773, 101, 91, -590, -58]], ![![-448, 62, 67, -330, -56]], ![![-485, 56, 23, -400, 16]], ![![-737, 89, 59, -585, -11]], ![![-468, 64, 68, -346, -55]]]
  g := ![![![-384, 617, 25, 170, -250], ![511, -916, -13, -250, 440], ![-744, 1147, 58, 318, -430], ![489, -804, -28, -221, 339], ![-134, 160, 20, 46, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-1037, -335, -1851, -2456, 3009]] ![![-239, 268, 6, 74, -121]]
  ![![-773, 101, 91, -590, -58]] where
 M := ![![![-773, 101, 91, -590, -58]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![-773, 101, 91, -590, -58]] ![![-601, 617, 25, 170, -250]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![197, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)


lemma PB312I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB312I4 : PrimesBelowBoundCertificateInterval O 151 197 312 where
  m := 9
  g := ![3, 1, 3, 3, 1, 3, 3, 1, 3]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB312I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1, I191N2]
    · exact ![I193N0]
    · exact ![I197N0, I197N1, I197N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
    · exact PBC197
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![24649, 24649, 157]
    · exact ![115063617043]
    · exact ![27889, 27889, 167]
    · exact ![29929, 29929, 173]
    · exact ![183765996899]
    · exact ![32761, 32761, 181]
    · exact ![36481, 36481, 191]
    · exact ![267785184193]
    · exact ![38809, 38809, 197]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
  β := ![I157N2, I167N2, I173N2, I181N2, I191N2, I197N2]
  Il := ![[I157N2], [], [I167N2], [I173N2], [], [I181N2], [I191N2], [], [I197N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
