
import IdealArithmetic.Examples.NF3_1_912968_1.RI3_1_912968_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18073335939506611929020, -4153129085135218622765, -928818857794248155312]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-18073335939506611929020, -4153129085135218622765, -928818857794248155312]] 
 ![![83, 0, 0], ![0, 83, 0], ![56, 67, 1]] where
  M :=![![![-18073335939506611929020, -4153129085135218622765, -928818857794248155312], ![-179699893208248119976733, -41293807384362815811820, -9235077028064685400842], ![-884325014874540872320969, -203211844912365018187509, -45446936469498034434585]]]
  hmulB := by decide  
  f := ![![![136970152866, 33448360599, -9596216630]], ![![-1780236582471, -102935262884, 57300504568]], ![![-1280850331220, -62820970893, 38942876777]]]
  g := ![![![408921928879172105644, 699731739603366358833, -928818857794248155312], ![4065836389920171836993, 6957305463806880795718, -9235077028064685400842], ![20008475029124687421877, 34237745765590401071442, -45446936469498034434585]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [48, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 82], [0, 1]]
 g := ![![[7, 64], [56, 44], [40], [49], [71, 16], [1]], ![[0, 19], [46, 39], [40], [49], [7, 67], [1]]]
 h' := ![![[79, 82], [51, 75], [81, 25], [80, 66], [78, 7], [35, 79], [0, 1]], ![[0, 1], [0, 8], [64, 58], [65, 17], [50, 76], [51, 4], [79, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [17, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [48, 4, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1230, 526, 102]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-54, -76, 102]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8672687217106150352053, -1992924253065549803170, -445703851351042623562]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-8672687217106150352053, -1992924253065549803170, -445703851351042623562]] 
 ![![83, 0, 0], ![31, 1, 0], ![18, 0, 1]] where
  M :=![![![-8672687217106150352053, -1992924253065549803170, -445703851351042623562], ![-86230952158412605656388, -19815283500882215941103, -4431552357482142229902], ![-424352995923950473520264, -97513418421200305800384, -21808207753947765744273]]]
  hmulB := by decide  
  f := ![![![1456720329249, -121922302398, -4996320454]], ![![531230160705, -29491313933, -4864179028]], ![![31843909454, -69605605924, 13493448763]]]
  g := ![![![736513662075236876751, -1992924253065549803170, -445703851351042623562], ![7323021431368851188627, -19815283500882215941103, -4431552357482142229902], ![36037478490413479393838, -97513418421200305800384, -21808207753947765744273]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-18073335939506611929020, -4153129085135218622765, -928818857794248155312]] ![![-8672687217106150352053, -1992924253065549803170, -445703851351042623562]]
  ![![83, 0, 0]] where
 M := ![![![909019729996682042062716598646545141482993248, 208886521682949786210364534499606396727243003, 46716039039719371706584284830461915943016446]]]
 hmul := by decide  
 g := ![![![![10952044939719060747743573477669218572084256, 2516705080517467303739331740959113213581241, 562843843852040622970894997957372481241162]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![26, -16, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![26, -16, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![26, 73, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![26, -16, 1], ![173, 51, -31], ![-2917, -293, 35]]]
  hmulB := by decide  
  f := ![![![-25, 16, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -73, 89]], ![![0, -1, 1], ![11, 26, -31], ![-43, -32, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [60, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 88], [0, 1]]
 g := ![![[22, 22], [50], [22], [47, 5], [62, 47], [1]], ![[85, 67], [50], [22], [33, 84], [55, 42], [1]]]
 h' := ![![[15, 88], [30, 72], [87, 36], [28, 17], [18, 19], [29, 15], [0, 1]], ![[0, 1], [42, 17], [4, 53], [16, 72], [36, 70], [76, 74], [15, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [88, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [60, 74, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-889, 2019, 1003]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-303, -800, 1003]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![31, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![31, 1, 0]] 
 ![![89, 0, 0], ![31, 1, 0], ![54, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![31, 1, 0], ![1, 31, 2], ![189, 25, 32]]]
  hmulB := by decide  
  f := ![![![1392, 55601, 3588], ![1157, -159666, 0]], ![![469, 19339, 1248], ![446, -55536, 0]], ![![831, 33735, 2177], ![741, -96876, 0]]]
  g := ![![![1, 0, 0], ![-31, 89, 0], ![-54, 0, 89]], ![![0, 1, 0], ![-12, 31, 2], ![-26, 25, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![26, -16, 1]] ![![89, 0, 0], ![31, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![2759, 89, 0]], ![![2314, -1424, 89], ![979, -445, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![31, 1, 0]]], ![![![26, -16, 1]], ![![11, -5, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2577544771486, 592302173463, 132464321948]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![2577544771486, 592302173463, 132464321948]] 
 ![![97, 0, 0], ![43, 1, 0], ![46, 0, 1]] where
  M :=![![![2577544771486, 592302173463, 132464321948], ![25628059021635, 5889152820186, 1317068668874], ![126118793232943, 28981236785011, 6481454993649]]]
  hmulB := by decide  
  f := ![![![-16448900, 3384941, -351666]], ![![-7942089, 1240329, -89726]], ![![-1593029, 2089717, -392085]]]
  g := ![![![-298812448423, 592302173463, 132464321948], ![-2971037845511, 5889152820186, 1317068668874], ![-14620838332272, 28981236785011, 6481454993649]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20751, 344, -494]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![20751, 344, -494]] 
 ![![97, 0, 0], ![74, 1, 0], ![27, 0, 1]] where
  M :=![![![20751, 344, -494], ![-93022, 8401, 194], ![12158, -44258, 8745]]]
  hmulB := by decide  
  f := ![![![-82052797, -18855172, -4216830]], ![![-71007660, -16317075, -3649202]], ![![-64229421, -14759482, -3300857]]]
  g := ![![![89, 344, -494], ![-7422, 8401, 194], ![31455, -44258, 8745]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![78, 189, -40]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![78, 189, -40]] 
 ![![97, 0, 0], ![76, 1, 0], ![71, 0, 1]] where
  M :=![![![78, 189, -40], ![-7371, -922, 338], ![31441, 445, -733]]]
  hmulB := by decide  
  f := ![![![-525416, -120737, -27002]], ![![-465523, -106974, -23924]], ![![-649619, -149278, -33385]]]
  g := ![![![-118, 189, -40], ![399, -922, 338], ![512, 445, -733]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![2577544771486, 592302173463, 132464321948]] ![![20751, 344, -494]]
  ![![-525416, -120737, -27002]] where
 M := ![![![-525416, -120737, -27002]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![-525416, -120737, -27002]] ![![78, 189, -40]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-3, -13, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-3, -13, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![98, 88, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-3, -13, 1], ![176, 22, -25], ![-2350, -218, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-98, -88, 101]], ![![-1, -1, 1], ![26, 22, -25], ![-32, -10, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [89, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 100], [0, 1]]
 g := ![![[52, 4], [33], [56, 52], [24], [79], [18, 1]], ![[23, 97], [33], [83, 49], [24], [79], [36, 100]]]
 h' := ![![[18, 100], [5, 99], [66, 72], [64, 31], [33, 23], [14, 33], [0, 1]], ![[0, 1], [70, 2], [49, 29], [16, 70], [43, 78], [2, 68], [18, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [31, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [89, 83, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![440064, 462745, 111872]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-104192, -92891, 111872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![25, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![25, 1, 0]] 
 ![![101, 0, 0], ![25, 1, 0], ![92, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![25, 1, 0], ![1, 25, 2], ![189, 25, 26]]]
  hmulB := by decide  
  f := ![![![-8067, -227908, -18236], ![-4242, 920918, 0]], ![![-2006, -56390, -4512], ![-1009, 227856, 0]], ![![-7364, -207600, -16611], ![-3800, 838856, 0]]]
  g := ![![![1, 0, 0], ![-25, 101, 0], ![-92, 0, 101]], ![![0, 1, 0], ![-8, 25, 2], ![-28, 25, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-3, -13, 1]] ![![101, 0, 0], ![25, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![2525, 101, 0]], ![![-303, -1313, 101], ![101, -303, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![25, 1, 0]]], ![![![-3, -13, 1]], ![![1, -3, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![3, -4, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![3, -4, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![3, 99, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![3, -4, 1], ![185, 28, -7], ![-649, 7, 24]]]
  hmulB := by decide  
  f := ![![![-2, 4, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -99, 103]], ![![0, -1, 1], ![2, 7, -7], ![-7, -23, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [101, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 102], [0, 1]]
 g := ![![[40, 98], [84, 56], [53, 30], [46], [50], [80, 1]], ![[52, 5], [32, 47], [84, 73], [46], [50], [57, 102]]]
 h' := ![![[80, 102], [65, 43], [3, 57], [17, 37], [53, 56], [57, 16], [0, 1]], ![[0, 1], [3, 60], [31, 46], [93, 66], [1, 47], [101, 87], [80, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [13, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [101, 23, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![845, 2444, 522]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7, -478, 522]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![7, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![7, 1, 0]] 
 ![![103, 0, 0], ![7, 1, 0], ![79, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![7, 1, 0], ![1, 7, 2], ![189, 25, 8]]]
  hmulB := by decide  
  f := ![![![-117, -826, -236], ![0, 12154, 0]], ![![-8, -56, -16], ![1, 824, 0]], ![![-93, -634, -181], ![48, 9322, 0]]]
  g := ![![![1, 0, 0], ![-7, 103, 0], ![-79, 0, 103]], ![![0, 1, 0], ![-2, 7, 2], ![-6, 25, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![3, -4, 1]] ![![103, 0, 0], ![7, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![721, 103, 0]], ![![309, -412, 103], ![206, 0, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![7, 1, 0]]], ![![![3, -4, 1]], ![![2, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-25, 0, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-25, 0, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![82, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-25, 0, 1], ![189, 0, 1], ![107, 107, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-82, 0, 107]], ![![-1, 0, 1], ![1, 0, 1], ![1, 1, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [89, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 106], [0, 1]]
 g := ![![[30, 101], [48, 76], [39], [82, 35], [30], [5, 1]], ![[0, 6], [0, 31], [39], [43, 72], [30], [10, 106]]]
 h' := ![![[5, 106], [8, 84], [9, 41], [85, 57], [80, 79], [90, 43], [0, 1]], ![[0, 1], [0, 23], [0, 66], [49, 50], [47, 28], [91, 64], [5, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [53, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [89, 102, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1173, 428, -94]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![83, 4, -94]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-1, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-1, 1, 0]] 
 ![![107, 0, 0], ![106, 1, 0], ![0, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-1, 1, 0], ![1, -1, 2], ![189, 25, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![54, 54, 0]]]
  g := ![![![1, 0, 0], ![-106, 107, 0], ![0, 0, 107]], ![![-1, 1, 0], ![1, -1, 2], ![-23, 25, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-25, 0, 1]] ![![107, 0, 0], ![-1, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-107, 107, 0]], ![![-2675, 0, 107], ![214, 0, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-1, 1, 0]]], ![![![-25, 0, 1]], ![![2, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![8, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![8, 1, 0]] 
 ![![109, 0, 0], ![8, 1, 0], ![23, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![8, 1, 0], ![1, 8, 2], ![189, 25, 9]]]
  hmulB := by decide  
  f := ![![![-3083, -24924, -6232], ![-436, 339644, 0]], ![![-228, -1824, -456], ![1, 24852, 0]], ![![-657, -5260, -1315], ![-4, 71668, 0]]]
  g := ![![![1, 0, 0], ![-8, 109, 0], ![-23, 0, 109]], ![![0, 1, 0], ![-1, 8, 2], ![-2, 25, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![41, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![41, 1, 0]] 
 ![![109, 0, 0], ![41, 1, 0], ![32, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![41, 1, 0], ![1, 41, 2], ![189, 25, 42]]]
  hmulB := by decide  
  f := ![![![445, 24924, 1216], ![436, -66272, 0]], ![![146, 9346, 456], ![219, -24852, 0]], ![![125, 7317, 357], ![143, -19456, 0]]]
  g := ![![![1, 0, 0], ![-41, 109, 0], ![-32, 0, 109]], ![![0, 1, 0], ![-16, 41, 2], ![-20, 25, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-50, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-50, 1, 0]] 
 ![![109, 0, 0], ![59, 1, 0], ![4, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-50, 1, 0], ![1, -50, 2], ![189, 25, -49]]]
  hmulB := by decide  
  f := ![![![4881, -373948, 14960], ![-5668, -815320, 0]], ![![2649, -202372, 8096], ![-3051, -441232, 0]], ![![186, -13723, 549], ![-193, -29920, 0]]]
  g := ![![![1, 0, 0], ![-59, 109, 0], ![-4, 0, 109]], ![![-1, 1, 0], ![27, -50, 2], ![-10, 25, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![8, 1, 0]] ![![109, 0, 0], ![41, 1, 0]]
  ![![109, 0, 0], ![1, -30, 1]] where
 M := ![![![11881, 0, 0], ![4469, 109, 0]], ![![872, 109, 0], ![329, 49, 2]]]
 hmul := by decide  
 g := ![![![![108, 30, -1], ![109, 0, 0]], ![![40, 31, -1], ![109, 0, 0]]], ![![![8, 1, 0], ![0, 0, 0]], ![![3, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![1, -30, 1]] ![![109, 0, 0], ![-50, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-5450, 109, 0]], ![![109, -3270, 109], ![109, 1526, -109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-50, 1, 0]]], ![![![1, -30, 1]], ![![1, 14, -1]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [58, 31, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 61, 4], [92, 51, 109], [0, 1]]
 g := ![![[20, 8, 99], [34, 111], [30, 81], [33, 95], [28, 9, 2], [1]], ![[20, 15, 111, 100], [13, 41], [29, 100], [79, 81], [101, 85, 97, 111], [7, 56, 3, 64]], ![[97, 53, 64, 14], [46, 15], [41, 1], [37, 111], [61, 30, 26, 1], [73, 50, 62, 49]]]
 h' := ![![[83, 61, 4], [69, 41, 41], [81, 103, 26], [76, 89, 104], [71, 53, 78], [55, 82, 62], [0, 1]], ![[92, 51, 109], [89, 83, 108], [74, 56, 43], [20, 70, 10], [46, 33, 9], [53, 97, 100], [83, 61, 4]], ![[0, 1], [18, 102, 77], [55, 67, 44], [88, 67, 112], [58, 27, 26], [65, 47, 64], [92, 51, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 11], []]
 b := ![[], [15, 33, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [58, 31, 51, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7688972, 1787095, 385895]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![68044, 15815, 3415]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [86, 24, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 83, 107], [72, 43, 20], [0, 1]]
 g := ![![[10, 110, 25], [65, 43, 82], [0, 45, 87], [113, 43, 42], [94, 55, 41], [1]], ![[63, 28, 35, 11], [121, 110, 42, 113], [76, 1, 20, 122], [23, 50, 77, 70], [80, 70, 34, 74], [44, 121, 6, 1]], ![[97, 32, 98, 93], [25, 80, 90, 23], [48, 117, 69, 110], [99, 47, 41, 10], [41, 29, 83, 56], [52, 120, 64, 126]]]
 h' := ![![[29, 83, 107], [125, 76, 5], [0, 105, 92], [61, 98, 50], [44, 29, 13], [41, 103, 101], [0, 1]], ![[72, 43, 20], [126, 82, 92], [51, 100, 78], [50, 103, 63], [34, 37, 106], [31, 81, 124], [29, 83, 107]], ![[0, 1], [18, 96, 30], [4, 49, 84], [95, 53, 14], [98, 61, 8], [95, 70, 29], [72, 43, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115, 58], []]
 b := ![[], [40, 27, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [86, 24, 26, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-282448, -91059, -2667]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2224, -717, -21]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [107, 126, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 100, 69], [77, 30, 62], [0, 1]]
 g := ![![[60, 82, 44], [124, 121, 9], [32, 20], [61, 101], [68, 27], [76, 1], []], ![[122, 50], [99, 55, 69, 23], [87, 4], [91, 74], [33, 109], [40, 114], [59, 45]], ![[27, 95, 73, 108], [64, 32, 53, 7], [14, 77], [84, 84], [0, 52], [83, 44], [66, 45]]]
 h' := ![![[130, 100, 69], [94, 15, 31], [40, 59, 3], [78, 113, 85], [29, 113, 106], [121, 11, 17], [0, 0, 1], [0, 1]], ![[77, 30, 62], [121, 66], [40, 124, 100], [21, 87, 129], [123, 3, 104], [95, 115, 90], [107, 127, 30], [130, 100, 69]], ![[0, 1], [55, 50, 100], [5, 79, 28], [113, 62, 48], [113, 15, 52], [47, 5, 24], [46, 4, 100], [77, 30, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 33], []]
 b := ![[], [8, 51, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [107, 126, 55, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1897666, 497145, 92224]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14486, 3795, 704]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀


def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![14, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![14, 1, 0]] 
 ![![137, 0, 0], ![14, 1, 0], ![108, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![14, 1, 0], ![1, 14, 2], ![189, 25, 15]]]
  hmulB := by decide  
  f := ![![![-2260, -32239, -4606], ![-411, 315511, 0]], ![![-235, -3290, -470], ![1, 32195, 0]], ![![-1786, -25415, -3631], ![-281, 248724, 0]]]
  g := ![![![1, 0, 0], ![-14, 137, 0], ![-108, 0, 137]], ![![0, 1, 0], ![-3, 14, 2], ![-13, 25, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![61, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![61, 1, 0]] 
 ![![137, 0, 0], ![61, 1, 0], ![58, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![61, 1, 0], ![1, 61, 2], ![189, 25, 62]]]
  hmulB := by decide  
  f := ![![![140, 15919, 522], ![274, -35757, 0]], ![![55, 7075, 232], ![138, -15892, 0]], ![![33, 6739, 221], ![175, -15138, 0]]]
  g := ![![![1, 0, 0], ![-61, 137, 0], ![-58, 0, 137]], ![![0, 1, 0], ![-28, 61, 2], ![-36, 25, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![14, 1, 0]] ![![137, 0, 0], ![61, 1, 0]]
  ![![137, 0, 0], ![-52, -31, 1]] where
 M := ![![![18769, 0, 0], ![8357, 137, 0]], ![![1918, 137, 0], ![855, 75, 2]]]
 hmul := by decide  
 g := ![![![![137, 0, 0], ![0, 0, 0]], ![![61, 1, 0], ![0, 0, 0]]], ![![![14, 1, 0], ![0, 0, 0]], ![![7, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-52, -31, 1]] ![![137, 0, 0], ![61, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![8357, 137, 0]], ![![-7124, -4247, 137], ![-3014, -1918, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![61, 1, 0]]], ![![![-52, -31, 1]], ![![-22, -14, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB271I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB271I2 : PrimesBelowBoundCertificateInterval O 79 137 271 where
  m := 11
  g := ![2, 2, 3, 2, 2, 2, 3, 1, 1, 1, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB271I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
    · exact ![I127N0]
    · exact ![I131N0]
    · exact ![I137N0, I137N1, I137N1]
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
    · exact ![97, 97, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![1442897]
    · exact ![2048383]
    · exact ![2248091]
    · exact ![137, 137, 137]
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
      exact NI97N1
      exact NI97N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N1
  β := ![I83N1, I89N1, I97N0, I97N1, I97N2, I101N1, I103N1, I107N1, I109N0, I109N1, I109N2, I137N0, I137N1]
  Il := ![[I83N1], [I89N1], [I97N0, I97N1, I97N2], [I101N1], [I103N1], [I107N1], [I109N0, I109N1, I109N2], [], [], [], [I137N0, I137N1, I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
