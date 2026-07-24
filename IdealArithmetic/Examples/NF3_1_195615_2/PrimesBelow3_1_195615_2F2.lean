
import IdealArithmetic.Examples.NF3_1_195615_2.RI3_1_195615_2
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [81, 79, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 11, 81], [30, 71, 2], [0, 1]]
 g := ![![[41, 77, 75], [44], [26, 28], [26, 37], [15, 29, 1], []], ![[37, 60, 77, 75], [67, 8, 82, 63], [34, 23], [78, 40], [14, 18, 76, 44], [72, 4]], ![[37, 72, 58, 53], [3, 28, 54, 20], [45, 38], [41, 38], [50, 49, 67, 76], [68, 4]]]
 h' := ![![[82, 11, 81], [5, 26, 65], [79, 58], [39, 37, 32], [30, 35, 55], [0, 0, 1], [0, 1]], ![[30, 71, 2], [25, 2, 81], [21, 57, 50], [77, 45, 40], [2, 17, 17], [62, 25, 71], [82, 11, 81]], ![[0, 1], [65, 55, 20], [76, 51, 33], [22, 1, 11], [43, 31, 11], [40, 58, 11], [30, 71, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25], []]
 b := ![[], [32, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [81, 79, 54, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-171478, 664, -3320]
  a := ![2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2066, 8, -40]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![835756751789093647234419494358733544363224819281, 119215871896089952363663952553601228439627594660, 88611548527698040709265559305902934603886005868]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![835756751789093647234419494358733544363224819281, 119215871896089952363663952553601228439627594660, 88611548527698040709265559305902934603886005868]] 
 ![![89, 0, 0], ![0, 89, 0], ![3, 57, 1]] where
  M :=![![![835756751789093647234419494358733544363224819281, 119215871896089952363663952553601228439627594660, 88611548527698040709265559305902934603886005868], ![7293549881062153555560244635894546984451055309460, 1040382750635403946053419385781045760503399659301, 773302456535845843236850881379812011405909985036], ![15981711313995716637722962881245698101224821933388, 2279698781506712535294365389580161899671972084792, 1694469335275159836926606314607256543469682049677]]]
  hmulB := by decide  
  f := ![![![1337834286525749064201385, 92941594246172536692524, -112377088793109433856972]], ![![-9737935735906646951227668, 590065654067856821531477, 239953793644643815748676]], ![![-6186131308275530180259197, 362270902795147639073617, 158172054211592104457205]]]
  g := ![![![6403619170853927248389020409449716185972660693, -55411712294187622113083965481829955550358143144, 88611548527698040709265559305902934603886005868], ![55883623724209168829771820132079898317228374768, -483571430021436057510641357897395942580151342559, 773302456535845843236850881379812011405909985036], ![122452846159216147493743190308134027761975008813, -1059607340777274136736204433067791697506740502773, 1694469335275159836926606314607256543469682049677]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [54, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 88], [0, 1]]
 g := ![![[6, 87], [18], [67], [7, 68], [31, 45], [1]], ![[31, 2], [18], [67], [47, 21], [47, 44], [1]]]
 h' := ![![[32, 88], [12, 40], [70, 75], [67, 45], [17, 54], [35, 32], [0, 1]], ![[0, 1], [46, 49], [67, 14], [83, 44], [54, 35], [80, 57], [32, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [30, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [54, 57, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5080, 1469, 1481]
  a := ![-5, -7, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-107, -932, 1481]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1033069, -153733, 16135]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![1033069, -153733, 16135]] 
 ![![89, 0, 0], ![69, 1, 0], ![54, 0, 1]] where
  M :=![![![1033069, -153733, 16135], ![1678941, 1421210, -736395], ![-12002395, -462100, 838548]]]
  hmulB := by decide  
  f := ![![![851464673580, 121456516184, 90276989185]], ![![743614533993, 106072316897, 78842121495]], ![![699563792530, 99788733139, 74171618497]]]
  g := ![![![121004, -153733, 16135], ![-636171, 1421210, -736395], ![-285383, -462100, 838548]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![835756751789093647234419494358733544363224819281, 119215871896089952363663952553601228439627594660, 88611548527698040709265559305902934603886005868]] ![![1033069, -153733, 16135]]
  ![![89, 0, 0]] where
 M := ![![![20447531430096605451244420716835804589, 2916722218927194671814635769352609827, 2167960258425615283127720472338047899]]]
 hmul := by decide  
 g := ![![![![229747544158388825294881131649840501, 32772159763226906424883547970254043, 24359104027254104304805848003798291]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-298819, 130935, -44128]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-298819, 130935, -44128]] 
 ![![97, 0, 0], ![0, 97, 0], ![47, 81, 1]] where
  M :=![![![-298819, 130935, -44128], ![-4012750, -781329, 566419], ![8217027, -183757, -345845]]]
  hmulB := by decide  
  f := ![![![3858785404, 550433443, 409129749]], ![![33675161779, 4803567263, 3570426713]], ![![30750932208, 4386442810, 3260383737]]]
  g := ![![![18301, 38199, -44128], ![-315819, -481044, 566419], ![252286, 286904, -345845]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [38, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 96], [0, 1]]
 g := ![![[42, 18], [65], [85], [64], [18], [53, 1]], ![[26, 79], [65], [85], [64], [18], [9, 96]]]
 h' := ![![[53, 96], [3, 42], [57, 68], [59, 52], [39, 89], [23, 55], [0, 1]], ![[0, 1], [95, 55], [72, 29], [2, 45], [3, 8], [28, 42], [53, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [55, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [38, 44, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![315884, 608195, 206640]
  a := ![66, 67, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-96868, -166285, 206640]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3858785404, 550433443, 409129749]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![3858785404, 550433443, 409129749]] 
 ![![97, 0, 0], ![78, 1, 0], ![75, 0, 1]] where
  M :=![![![3858785404, 550433443, 409129749], ![33675161779, 4803567263, 3570426713], ![73789406089, 10525632446, 7823560533]]]
  hmulB := by decide  
  f := ![![![-298819, 130935, -44128]], ![![-281656, 97233, -29645]], ![![-146334, 99344, -37685]]]
  g := ![![![-719172725, 550433443, 409129749], ![-6276134930, 4803567263, 3570426713], ![-13752339842, 10525632446, 7823560533]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-298819, 130935, -44128]] ![![3858785404, 550433443, 409129749]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [76, 38, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 59, 31], [47, 41, 70], [0, 1]]
 g := ![![[98, 99, 33], [63, 77], [18, 61, 96], [33, 24], [73, 77], [1]], ![[24, 84, 47, 80], [68, 13], [80, 52, 50, 81], [46, 47], [44, 9], [39, 29, 24, 97]], ![[76, 44, 1, 84], [13, 49], [79, 88, 46, 25], [59, 58], [87, 52], [49, 14, 22, 4]]]
 h' := ![![[26, 59, 31], [55, 96, 29], [46, 27, 28], [87, 20, 46], [26, 79, 23], [25, 63, 73], [0, 1]], ![[47, 41, 70], [80, 48, 24], [20, 40, 66], [17, 21, 82], [68, 92, 59], [68, 18, 98], [26, 59, 31]], ![[0, 1], [98, 58, 48], [51, 34, 7], [47, 60, 74], [17, 31, 19], [8, 20, 31], [47, 41, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 40], []]
 b := ![[], [1, 27, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [76, 38, 28, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2379661, -249066, 14544]
  a := ![5, 6, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23561, -2466, 144]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6206997267703836, -885392298108165, -658100145073342]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-6206997267703836, -885392298108165, -658100145073342]] 
 ![![103, 0, 0], ![0, 103, 0], ![101, 79, 1]] where
  M :=![![![-6206997267703836, -885392298108165, -658100145073342], ![-54167727735017740, -7726713396854216, -5743161780687509], ![-118692954914034597, -16930864246934323, -12584482879433560]]]
  hmulB := by decide  
  f := ![![![121665849, -6612622, -3344671]], ![![-271071791, 118167738, -39752452]], ![![-96206232, 83211307, -32943957]]]
  g := ![![![585059392084502, 496160380220251, -658100145073342], ![5105743806936123, 4329932692014165, -5743161780687509], ![11187765202997621, 9487798866294339, -12584482879433560]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [39, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 102], [0, 1]]
 g := ![![[99, 8], [72, 100], [31, 13], [7], [18], [53, 1]], ![[8, 95], [16, 3], [102, 90], [7], [18], [3, 102]]]
 h' := ![![[53, 102], [76, 27], [27, 10], [25, 61], [68, 78], [96, 92], [0, 1]], ![[0, 1], [65, 76], [42, 93], [65, 42], [82, 25], [28, 11], [53, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [2, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [39, 50, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![941, 477, -110]
  a := ![2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![117, 89, -110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-121665849, 6612622, 3344671]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-121665849, 6612622, 3344671]] 
 ![![103, 0, 0], ![15, 1, 0], ![43, 0, 1]] where
  M :=![![![-121665849, 6612622, 3344671], ![271071791, -118167738, 39752452], ![782821156, 96611859, -85027908]]]
  hmulB := by decide  
  f := ![![![6206997267703836, 885392298108165, 658100145073342]], ![![1429831910199760, 203957260858997, 151598679192113]], ![![3743629489566015, 534007117141606, 396920282695022]]]
  g := ![![![-3540544, 6612622, 3344671], ![3244975, -118167738, 39752452], ![29027605, 96611859, -85027908]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-6206997267703836, -885392298108165, -658100145073342]] ![![-121665849, 6612622, 3344671]]
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
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67959, -1957, 4447]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-67959, -1957, 4447]] 
 ![![107, 0, 0], ![0, 107, 0], ![39, 94, 1]] where
  M :=![![![-67959, -1957, 4447], ![381909, -41810, -891], ![127157, 74708, -40744]]]
  hmulB := by decide  
  f := ![![![16542724, 2359724, 1753951]], ![![144366387, 20593031, 15306522]], ![![135812560, 19372877, 14399598]]]
  g := ![![![-2256, -3925, 4447], ![3894, 392, -891], ![16039, 36492, -40744]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [44, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 106], [0, 1]]
 g := ![![[3, 90], [75, 3], [27], [11, 30], [83], [82, 1]], ![[0, 17], [0, 104], [27], [10, 77], [83], [57, 106]]]
 h' := ![![[82, 106], [17, 82], [22, 18], [51, 54], [30, 43], [30, 46], [0, 1]], ![[0, 1], [0, 25], [0, 89], [92, 53], [25, 64], [57, 61], [82, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [9, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [44, 25, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25450, 2288, 2392]
  a := ![-3, 16, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-634, -2080, 2392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16542724, -2359724, -1753951]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-16542724, -2359724, -1753951]] 
 ![![107, 0, 0], ![63, 1, 0], ![87, 0, 1]] where
  M :=![![![-16542724, -2359724, -1753951], ![-144366387, -20593031, -15306522], ![-316337306, -45123689, -33539829]]]
  hmulB := by decide  
  f := ![![![67959, 1957, -4447]], ![![36444, 1543, -2610]], ![![54068, 893, -3235]]]
  g := ![![![2660875, -2359724, -1753951], ![23221140, -20593031, -15306522], ![50882432, -45123689, -33539829]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-67959, -1957, 4447]] ![![-16542724, -2359724, -1753951]]
  ![![107, 0, 0]] where
 M := ![![![-107, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-740401, -44955, 59235]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-740401, -44955, 59235]] 
 ![![109, 0, 0], ![0, 109, 0], ![28, 24, 1]] where
  M :=![![![-740401, -44955, 59235], ![5124885, -354316, -106305], ![88335, 900690, -415666]]]
  hmulB := by decide  
  f := ![![![-2229586834, -318037680, -236393115]], ![![-19457339415, -2775477049, -2062974630]], ![![-5248070878, -748606989, -556429471]]]
  g := ![![![-22009, -13455, 59235], ![74325, 20156, -106305], ![107587, 99786, -415666]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [34, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 108], [0, 1]]
 g := ![![[88, 93], [12], [48, 74], [59, 104], [89], [60, 1]], ![[0, 16], [12], [19, 35], [86, 5], [89], [11, 108]]]
 h' := ![![[60, 108], [37, 23], [3, 11], [65, 40], [6, 39], [31, 78], [0, 1]], ![[0, 1], [0, 86], [9, 98], [67, 69], [57, 70], [24, 31], [60, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [52, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [34, 49, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3818, 994, -4]
  a := ![3, 6, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34, 10, -4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2229586834, -318037680, -236393115]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-2229586834, -318037680, -236393115]] 
 ![![109, 0, 0], ![96, 1, 0], ![26, 0, 1]] where
  M :=![![![-2229586834, -318037680, -236393115], ![-19457339415, -2775477049, -2062974630], ![-42635148390, -6081657585, -4520413999]]]
  hmulB := by decide  
  f := ![![![-740401, -44955, 59235]], ![![-605079, -42844, 51195]], ![![-175799, -2460, 10316]]]
  g := ![![![316039004, -318037680, -236393115], ![2758034841, -2775477049, -2062974630], ![6043438016, -6081657585, -4520413999]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-740401, -44955, 59235]] ![![-2229586834, -318037680, -236393115]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-278935754071, 41114157512, -4176381211]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-278935754071, 41114157512, -4176381211]] 
 ![![113, 0, 0], ![0, 113, 0], ![102, 79, 1]] where
  M :=![![![-278935754071, 41114157512, -4176381211], ![-437220717959, -382045975150, 197218025138], ![3219062228594, 126219544551, -225942107524]]]
  hmulB := by decide  
  f := ![![![543606225542360204474, 77542287283284977779, 57636135551988271062]], ![![4743986947352433084712, 676702328735731604226, 502983707520401431019]], ![![3899273302758171712831, 556208807831168730145, 413422499729091723507]]]
  g := ![![![1301372827, 3283613037, -4176381211], ![-181889020195, -141259026204, 197218025138], ![232435019434, 159076513619, -225942107524]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [42, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [102, 112], [0, 1]]
 g := ![![[46, 83], [30], [26], [50], [51, 26], [102, 1]], ![[37, 30], [30], [26], [50], [104, 87], [91, 112]]]
 h' := ![![[102, 112], [107, 99], [24, 16], [72, 79], [5, 29], [10, 79], [0, 1]], ![[0, 1], [35, 14], [74, 97], [107, 34], [25, 84], [45, 34], [102, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [94, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [42, 11, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1496, 1573, 655]
  a := ![-4, -3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-578, -444, 655]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5073241, 23551307, -11013378]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![5073241, 23551307, -11013378]] 
 ![![113, 0, 0], ![55, 1, 0], ![72, 0, 1]] where
  M :=![![![5073241, 23551307, -11013378], ![-983239744, -97096263, 95729779], ![1274978147, -91497647, -24917791]]]
  hmulB := by decide  
  f := ![![![-11178473914645046, -1594544718124403, -1185203567464739]], ![![-6304152912422403, -899250989491700, -668401123328426]], ![![-9014246534050357, -1285830186525744, -955740222837241]]]
  g := ![![![-4400756, 23551307, -11013378], ![-22437959, -97096263, 95729779], ![71694068, -91497647, -24917791]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-278935754071, 41114157512, -4176381211]] ![![5073241, 23551307, -11013378]]
  ![![113, 0, 0]] where
 M := ![![![-47164976788359867056, -10179203574429687936, 7111940303845936587]]]
 hmul := by decide  
 g := ![![![![-417389175118228912, -90081447561324672, 62937524812795899]]]]
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


lemma PB126I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 125 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 125 (by omega)

def PB126I2 : PrimesBelowBoundCertificateInterval O 79 125 126 where
  m := 8
  g := ![1, 2, 2, 1, 2, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB126I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
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
      exact NI113N1
  β := ![I89N1, I97N1, I103N1, I107N1, I109N1, I113N1]
  Il := ![[], [I89N1], [I97N1], [], [I103N1], [I107N1], [I109N1], [I113N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
