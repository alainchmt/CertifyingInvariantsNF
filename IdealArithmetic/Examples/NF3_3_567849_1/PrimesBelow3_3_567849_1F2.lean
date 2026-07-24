
import IdealArithmetic.Examples.NF3_3_567849_1.RI3_3_567849_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-805, 282, 38]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-805, 282, 38]] 
 ![![83, 0, 0], ![0, 83, 0], ![64, 38, 1]] where
  M :=![![![-805, 282, 38], ![-4408, 1263, 564], ![-30508, 11050, 981]]]
  hmulB := by decide  
  f := ![![![-60159, 1726, 1338]], ![![-155208, 4453, 3452]], ![![-118924, 3412, 2645]]]
  g := ![![![-39, -14, 38], ![-488, -243, 564], ![-1124, -316, 981]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [65, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 82], [0, 1]]
 g := ![![[25, 23], [79, 41], [21], [78], [62, 63], [1]], ![[0, 60], [20, 42], [21], [78], [26, 20], [1]]]
 h' := ![![[35, 82], [11, 40], [40, 37], [34, 41], [37, 59], [18, 35], [0, 1]], ![[0, 1], [0, 43], [7, 46], [58, 42], [27, 24], [81, 48], [35, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [31, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [65, 48, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-805, -50, 287]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-231, -132, 287]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![60159, -1726, -1338]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![60159, -1726, -1338]] 
 ![![83, 0, 0], ![7, 1, 0], ![55, 0, 1]] where
  M :=![![![60159, -1726, -1338], ![155208, -4453, -3452], ![122612, -3518, -2727]]]
  hmulB := by decide  
  f := ![![![805, -282, -38]], ![![121, -39, -10]], ![![901, -320, -37]]]
  g := ![![![1757, -1726, -1338], ![4533, -4453, -3452], ![3581, -3518, -2727]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-805, 282, 38]] ![![60159, -1726, -1338]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-788331, 253150, 66342]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-788331, 253150, 66342]] 
 ![![89, 0, 0], ![0, 89, 0], ![73, 37, 1]] where
  M :=![![![-788331, 253150, 66342], ![-7695672, 2582893, 506300], ![-25517564, 8050214, 2329743]]]
  hmulB := by decide  
  f := ![![![-21816331891, 625922958, 485218454]], ![![-56285340664, 1614858405, 1251845916]], ![![-41793418263, 1199076917, 929530129]]]
  g := ![![![-63273, -24736, 66342], ![-501748, -181463, 506300], ![-2197627, -878093, 2329743]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [15, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 88], [0, 1]]
 g := ![![[6, 18], [40], [9], [51, 9], [29, 1], [1]], ![[77, 71], [40], [9], [42, 80], [28, 88], [1]]]
 h' := ![![[88, 88], [39, 14], [4, 29], [36, 3], [10, 3], [74, 88], [0, 1]], ![[0, 1], [25, 75], [64, 60], [33, 86], [7, 86], [75, 1], [88, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [86, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [15, 1, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15, -552, 750]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-615, -318, 750]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![399483, -175852, 33672]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![399483, -175852, 33672]] 
 ![![89, 0, 0], ![15, 1, 0], ![58, 0, 1]] where
  M :=![![![399483, -175852, 33672], ![-3905952, 1806215, -351704], ![22351808, -10218020, 1982067]]]
  hmulB := by decide  
  f := ![![![13679359675, -4489276644, -1028980328]], ![![3646652957, -1196754405, -274306272]], ![![14095259470, -4625766164, -1060264885]]]
  g := ![![![12183, -175852, 33672], ![-119105, 1806215, -351704], ![681598, -10218020, 1982067]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-788331, 253150, 66342]] ![![399483, -175852, 33672]]
  ![![89, 0, 0]] where
 M := ![![![179147064663, -82010972578, 15915739882]]]
 hmul := by decide  
 g := ![![![![2012888367, -921471602, 178828538]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [30, 87, 92, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 86, 52], [86, 10, 45], [0, 1]]
 g := ![![[90, 72, 61], [1, 11], [8, 1], [35, 24], [31, 25], [1]], ![[3, 42, 56, 29], [44, 2], [95, 81], [59, 86], [57, 47], [90, 89, 89, 55]], ![[69, 70, 78, 15], [92, 44], [42, 64], [37, 50], [82, 49], [92, 83, 44, 42]]]
 h' := ![![[16, 86, 52], [45, 23, 35], [47, 15, 37], [44, 47, 96], [67, 27, 11], [67, 10, 5], [0, 1]], ![[86, 10, 45], [60, 92, 91], [33, 75, 83], [19, 69, 9], [25, 47, 59], [38, 64, 85], [16, 86, 52]], ![[0, 1], [71, 79, 68], [55, 7, 74], [65, 78, 89], [60, 23, 27], [80, 23, 7], [86, 10, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 56], []]
 b := ![[], [84, 25, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [30, 87, 92, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![93896, 11252, -7566]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![968, 116, -78]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![114734027, -37653282, -8630452]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![114734027, -37653282, -8630452]] 
 ![![101, 0, 0], ![0, 101, 0], ![27, 39, 1]] where
  M :=![![![114734027, -37653282, -8630452], ![1001132432, -328550499, -75306564], ![3867214496, -1269138038, -290897217]]]
  hmulB := by decide  
  f := ![![![9104751, -261218, -202500]], ![![23490000, -673967, -522436]], ![![11688065, -335345, -259953]]]
  g := ![![![3443131, 2959746, -8630452], ![30043660, 25825797, -75306564], ![116053855, 99760925, -290897217]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [59, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 100], [0, 1]]
 g := ![![[35, 85], [96], [11, 54], [80], [88], [56, 1]], ![[48, 16], [96], [5, 47], [80], [88], [11, 100]]]
 h' := ![![[56, 100], [23, 40], [58, 55], [91, 85], [93, 79], [29, 47], [0, 1]], ![[0, 1], [41, 61], [7, 46], [3, 16], [73, 22], [35, 54], [56, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [12, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [59, 45, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-765, -600, 948]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-261, -372, 948]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9104751, -261218, -202500]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![9104751, -261218, -202500]] 
 ![![101, 0, 0], ![23, 1, 0], ![27, 0, 1]] where
  M :=![![![9104751, -261218, -202500], ![23490000, -673967, -522436], ![18556288, -532246, -412749]]]
  hmulB := by decide  
  f := ![![![114734027, -37653282, -8630452]], ![![36039753, -11827485, -2710960]], ![![68960725, -22631452, -5187321]]]
  g := ![![![203765, -261218, -202500], ![525713, -673967, -522436], ![415269, -532246, -412749]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![114734027, -37653282, -8630452]] ![![9104751, -261218, -202500]]
  ![![101, 0, 0]] where
 M := ![![![101, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1606651, 735534, -142746]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-1606651, 735534, -142746]] 
 ![![103, 0, 0], ![0, 103, 0], ![21, 61, 1]] where
  M :=![![![-1606651, 735534, -142746], ![16558536, -7580179, 1471068], ![-93601212, 42849366, -8315713]]]
  hmulB := by decide  
  f := ![![![-2542813, 834498, 191274]], ![![-22187784, 7281563, 1668996]], ![![-14490891, 4755605, 1090025]]]
  g := ![![![13505, 91680, -142746], ![-139164, -944809, 1471068], ![786687, 5340853, -8315713]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [65, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 102], [0, 1]]
 g := ![![[26, 1], [75, 28], [95, 64], [18], [26], [61, 1]], ![[87, 102], [32, 75], [85, 39], [18], [26], [19, 102]]]
 h' := ![![[61, 102], [69, 102], [5, 53], [13, 8], [87, 92], [52, 51], [0, 1]], ![[0, 1], [8, 1], [45, 50], [89, 95], [34, 11], [73, 52], [61, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [99, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [65, 42, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-805, -38, 305]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-70, -181, 305]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2542813, -834498, -191274]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![2542813, -834498, -191274]] 
 ![![103, 0, 0], ![84, 1, 0], ![35, 0, 1]] where
  M :=![![![2542813, -834498, -191274], ![22187784, -7281563, -1668996], ![85707876, -28127514, -6447065]]]
  hmulB := by decide  
  f := ![![![1606651, -735534, 142746]], ![![1149516, -526259, 102132]], ![![1454699, -665952, 129241]]]
  g := ![![![770245, -834498, -191274], ![6720912, -7281563, -1668996], ![25961809, -28127514, -6447065]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-1606651, 735534, -142746]] ![![2542813, -834498, -191274]]
  ![![103, 0, 0]] where
 M := ![![![-103, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-267, 8, 6]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-267, 8, 6]] 
 ![![107, 0, 0], ![31, 1, 0], ![39, 0, 1]] where
  M :=![![![-267, 8, 6], ![-696, 23, 16], ![-580, 28, 15]]]
  hmulB := by decide  
  f := ![![![103, -48, 10]], ![![19, -9, 2]], ![![95, -44, 9]]]
  g := ![![![-7, 8, 6], ![-19, 23, 16], ![-19, 28, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-460983, 12124, 10538]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-460983, 12124, 10538]] 
 ![![107, 0, 0], ![91, 1, 0], ![94, 0, 1]] where
  M :=![![![-460983, 12124, 10538], ![-1222408, 46427, 24248], ![-795180, -41376, 34303]]]
  hmulB := by decide  
  f := ![![![-2595870629, 851909860, 195264974]], ![![-2419392189, 793993367, 181990022]], ![![-3098205742, 1016765624, 233051315]]]
  g := ![![![-23877, 12124, 10538], ![-72211, 46427, 24248], ![-2378, -41376, 34303]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-267, 8, 6]] ![![-460983, 12124, 10538]]
  ![![108532117, -3113948, -2413844]] where
 M := ![![![108532117, -3113948, -2413844]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![108532117, -3113948, -2413844]] ![![-460983, 12124, 10538]]
  ![![107, 0, 0]] where
 M := ![![![-44305505472307, 1271147332056, 985402347110]]]
 hmul := by decide  
 g := ![![![![-414070144601, 11879881608, 9209367730]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16647, -5462, -1252]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![16647, -5462, -1252]] 
 ![![109, 0, 0], ![0, 109, 0], ![89, 101, 1]] where
  M :=![![![16647, -5462, -1252], ![145232, -47659, -10924], ![560976, -184098, -42197]]]
  hmulB := by decide  
  f := ![![![-181, 98, -20]], ![![2320, -1023, 196]], ![![1887, -815, 155]]]
  g := ![![![1175, 1110, -1252], ![10252, 9685, -10924], ![39601, 37411, -42197]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [106, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 108], [0, 1]]
 g := ![![[38, 36], [48], [96, 26], [23, 97], [21], [5, 1]], ![[0, 73], [48], [8, 83], [72, 12], [21], [10, 108]]]
 h' := ![![[5, 108], [30, 103], [70, 87], [69, 74], [70, 73], [15, 28], [0, 1]], ![[0, 1], [0, 6], [69, 22], [3, 35], [108, 36], [46, 81], [5, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [62, 106]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [106, 104, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-71651, 16422, 23753]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20052, -21859, 23753]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, -98, 20]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![181, -98, 20]] 
 ![![109, 0, 0], ![16, 1, 0], ![82, 0, 1]] where
  M :=![![![181, -98, 20], ![-2320, 1023, -196], ![12528, -5766, 1121]]]
  hmulB := by decide  
  f := ![![![-16647, 5462, 1252]], ![![-3776, 1239, 284]], ![![-17670, 5798, 1329]]]
  g := ![![![1, -98, 20], ![-24, 1023, -196], ![118, -5766, 1121]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![16647, -5462, -1252]] ![![181, -98, 20]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-187, 62, 14]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-187, 62, 14]] 
 ![![113, 0, 0], ![0, 113, 0], ![27, 69, 1]] where
  M :=![![![-187, 62, 14], ![-1624, 533, 124], ![-6380, 2102, 471]]]
  hmulB := by decide  
  f := ![![![85, -2, -2]], ![![232, -11, -4]], ![![163, -7, -3]]]
  g := ![![![-5, -8, 14], ![-44, -71, 124], ![-169, -269, 471]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [77, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 112], [0, 1]]
 g := ![![[18, 91], [81], [26], [2], [52, 7], [83, 1]], ![[0, 22], [81], [26], [2], [68, 106], [53, 112]]]
 h' := ![![[83, 112], [38, 54], [88, 104], [100, 79], [64, 62], [50, 32], [0, 1]], ![[0, 1], [0, 59], [19, 9], [103, 34], [12, 51], [107, 81], [83, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [24, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [77, 30, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-358, 190, 83]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23, -49, 83]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85, -2, -2]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![85, -2, -2]] 
 ![![113, 0, 0], ![88, 1, 0], ![39, 0, 1]] where
  M :=![![![85, -2, -2], ![232, -11, -4], ![116, 22, -9]]]
  hmulB := by decide  
  f := ![![![-187, 62, 14]], ![![-160, 53, 12]], ![![-121, 40, 9]]]
  g := ![![![3, -2, -2], ![12, -11, -4], ![-13, 22, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-187, 62, 14]] ![![85, -2, -2]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [90, 53, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 19, 119], [73, 107, 8], [0, 1]]
 g := ![![[52, 114, 18], [38, 104, 18], [23, 0, 104], [89, 25, 21], [1, 78, 82], [1]], ![[72, 22, 8, 93], [81, 118, 27, 111], [37, 101, 95, 97], [69, 22, 20, 27], [82, 7, 58, 33], [40, 30, 105, 123]], ![[48, 97, 29, 15], [23, 118, 90, 2], [89, 75, 24, 52], [122, 70, 18, 26], [5, 82, 19, 87], [79, 17, 84, 4]]]
 h' := ![![[19, 19, 119], [9, 103, 48], [89, 5, 48], [118, 117, 72], [37, 11, 23], [37, 74, 92], [0, 1]], ![[73, 107, 8], [125, 52, 121], [121, 95, 16], [24, 64, 37], [65, 82, 87], [84, 9, 108], [19, 19, 119]], ![[0, 1], [89, 99, 85], [0, 27, 63], [104, 73, 18], [88, 34, 17], [18, 44, 54], [73, 107, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 43], []]
 b := ![[], [57, 30, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [90, 53, 35, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-122174, -192151, 312039]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-962, -1513, 2457]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8054987, 2643492, 605910]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-8054987, 2643492, 605910]] 
 ![![131, 0, 0], ![0, 131, 0], ![32, 121, 1]] where
  M :=![![![-8054987, 2643492, 605910], ![-70285560, 23066275, 5286984], ![-271502292, 89101344, 20422783]]]
  hmulB := by decide  
  f := ![![![1136159, -520116, 100938]], ![![-11708808, 5360129, -1040232]], ![![-10032220, 4592611, -891281]]]
  g := ![![![-209497, -539478, 605910], ![-1828008, -4707319, 5286984], ![-7061308, -18183629, 20422783]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [79, 123, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 130], [0, 1]]
 g := ![![[111, 16], [79, 109], [48], [3], [108], [64], [1]], ![[108, 115], [34, 22], [48], [3], [108], [64], [1]]]
 h' := ![![[8, 130], [47, 4], [56, 90], [124, 21], [19, 93], [6, 34], [52, 8], [0, 1]], ![[0, 1], [79, 127], [121, 41], [30, 110], [108, 38], [16, 97], [116, 123], [8, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [27, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [79, 123, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8719, 1472, 1058]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-325, -966, 1058]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1136159, -520116, 100938]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![1136159, -520116, 100938]] 
 ![![131, 0, 0], ![20, 1, 0], ![52, 0, 1]] where
  M :=![![![1136159, -520116, 100938], ![-11708808, 5360129, -1040232], ![66187860, -30299856, 5880245]]]
  hmulB := by decide  
  f := ![![![-8054987, 2643492, 605910]], ![![-1766300, 579665, 132864]], ![![-5269936, 1729488, 396413]]]
  g := ![![![48013, -520116, 100938], ![-494804, 5360129, -1040232], ![2797040, -30299856, 5880245]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-8054987, 2643492, 605910]] ![![1136159, -520116, 100938]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [94, 33, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 15, 28], [13, 121, 109], [0, 1]]
 g := ![![[92, 17, 121], [42, 16], [91, 101], [108, 102, 7], [18, 15], [133, 1], []], ![[70, 99, 90, 98], [60, 130], [80, 87], [86, 55, 6, 81], [57, 60], [93, 119], [33, 99]], ![[7, 8, 64, 120], [51, 136], [54, 130], [60, 132, 23, 112], [71, 135], [53, 88], [89, 99]]]
 h' := ![![[120, 15, 28], [26, 29, 11], [136, 116, 4], [123, 122, 52], [81, 131, 12], [102, 38, 120], [0, 0, 1], [0, 1]], ![[13, 121, 109], [100, 81, 88], [64, 42, 33], [7, 32, 118], [129, 22, 51], [12, 46, 103], [64, 55, 121], [120, 15, 28]], ![[0, 1], [108, 27, 38], [92, 116, 100], [28, 120, 104], [5, 121, 74], [68, 53, 51], [23, 82, 15], [13, 121, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 60], []]
 b := ![[], [86, 20, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [94, 33, 4, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15344, -7946, 4932]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![112, -58, 36]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB168I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB168I2 : PrimesBelowBoundCertificateInterval O 79 137 168 where
  m := 11
  g := ![2, 2, 1, 2, 2, 3, 2, 2, 1, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB168I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0, I131N1]
    · exact ![I137N0]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![17161, 131]
    · exact ![2571353]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I89N1, I101N1, I103N1, I107N0, I107N1, I109N1, I113N1, I131N1]
  Il := ![[I83N1], [I89N1], [], [I101N1], [I103N1], [I107N0, I107N1, I107N1], [I109N1], [I113N1], [], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
