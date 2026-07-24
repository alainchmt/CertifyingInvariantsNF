
import IdealArithmetic.Examples.NF3_1_628963_1.RI3_1_628963_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [21, 23, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 21, 10], [50, 61, 73], [0, 1]]
 g := ![![[59, 60, 36], [25, 71, 75], [51, 26], [44, 51], [42, 56, 1], []], ![[26, 26, 35, 41], [5, 61, 38, 48], [3, 17], [47, 27], [81, 19, 37, 26], [44, 17]], ![[46, 74, 41, 53], [56, 35, 51, 56], [8, 38], [34, 9], [24, 27, 33, 72], [64, 17]]]
 h' := ![![[6, 21, 10], [56, 3, 6], [49, 49, 18], [37, 71, 62], [31, 16, 47], [0, 0, 1], [0, 1]], ![[50, 61, 73], [58, 1, 64], [46, 13, 11], [21, 48, 10], [57, 44, 39], [25, 45, 61], [6, 21, 10]], ![[0, 1], [4, 79, 13], [67, 21, 54], [61, 47, 11], [51, 23, 80], [77, 38, 21], [50, 61, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 56], []]
 b := ![[], [81, 54, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [21, 23, 27, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-467373, 49551, -18675]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5631, 597, -225]
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


def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49826, 8342, -11389]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![49826, 8342, -11389]] 
 ![![89, 0, 0], ![53, 1, 0], ![4, 0, 1]] where
  M :=![![![49826, 8342, -11389], ![-1759201, 134844, 64488], ![2643006, -425889, 78698]]]
  hmulB := by decide  
  f := ![![![-38076682944, -4193951105, -2073697212]], ![![-26145527722, -2879795623, -1423913633]], ![![-6125141409, -674652874, -333581806]]]
  g := ![![![-3896, 8342, -11389], ![-102965, 134844, 64488], ![279779, -425889, 78698]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39998946510358573094, -4405678566136420498, -2178385758640197085]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-39998946510358573094, -4405678566136420498, -2178385758640197085]] 
 ![![89, 0, 0], ![72, 1, 0], ![2, 0, 1]] where
  M :=![![![-39998946510358573094, -4405678566136420498, -2178385758640197085], ![-324481663939677313009, -35739989090790231580, -17671621313401708320], ![-412662529582048685994, -45452658638307980817, -22474046343524943758]]]
  hmulB := by decide  
  f := ![![![42293819800, -6390966961, 925800940]], ![![35950387678, -4901039786, 369114955]], ![![-11284566497, 630508976, 598024178]]]
  g := ![![![3163670581671281988, -4405678566136420498, -2178385758640197085], ![25664503294651941319, -35739989090790231580, -17671621313401708320], ![32639067247900851914, -45452658638307980817, -22474046343524943758]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![49826, 8342, -11389]] ![![49826, 8342, -11389]]
  ![![-42293819800, 6390966961, -925800940]] where
 M := ![![![-42293819800, 6390966961, -925800940]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI89N1 : IdealMulLeCertificate' Table 
  ![![-42293819800, 6390966961, -925800940]] ![![-39998946510358573094, -4405678566136420498, -2178385758640197085]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![256718397421941382, -14514344010465847, -13470636543682390]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![256718397421941382, -14514344010465847, -13470636543682390]] 
 ![![97, 0, 0], ![0, 97, 0], ![37, 23, 1]] where
  M :=![![![256718397421941382, -14514344010465847, -13470636543682390], ![-2031978703162473976, 308513528663104028, -45630446964964455], ![-604218248359387791, -357444941878723788, 339629631617602636]]]
  hmulB := by decide  
  f := ![![![912061480676338195860715953114044, 100458888720326159403214256751196, 49671851732272421920939825857065]], ![![7398875537597028235097364842628553, 814948147723355983141505511474046, 402950740137085953174191632041850]], ![![2199278349650447158889328699234655, 242239217063219468836549309035807, 119775070449006729107749579689251]]]
  g := ![![![7784865459156596, 3044436046332259, -13470636543682390], ![-3542805829472053, 14000142359353469, -45630446964964455], ![-135778501218666859, -84215736794676128, 339629631617602636]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [54, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 96], [0, 1]]
 g := ![![[54, 9], [54], [48], [8], [33], [91, 1]], ![[0, 88], [54], [48], [8], [33], [85, 96]]]
 h' := ![![[91, 96], [79, 94], [45, 65], [55, 57], [83, 69], [33, 79], [0, 1]], ![[0, 1], [0, 3], [43, 32], [4, 40], [57, 28], [44, 18], [91, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [55, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [54, 6, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9895, 4464, -700]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![165, 212, -700]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![912061480676338195860715953114044, 100458888720326159403214256751196, 49671851732272421920939825857065]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![912061480676338195860715953114044, 100458888720326159403214256751196, 49671851732272421920939825857065]] 
 ![![97, 0, 0], ![81, 1, 0], ![13, 0, 1]] where
  M :=![![![912061480676338195860715953114044, 100458888720326159403214256751196, 49671851732272421920939825857065], ![7398875537597028235097364842628553, 814948147723355983141505511474046, 402950740137085953174191632041850], ![9409587766337211758179002180085188, 1036417774843032966971728712775969, 512456296306596189370528136183392]]]
  hmulB := by decide  
  f := ![![![256718397421941382, -14514344010465847, -13470636543682390]], ![![193424860701183278, -8939673568913707, -11719092855703485]], ![![28176504310575775, -5630220763038967, 1695993366492078]]]
  g := ![![![-81142706991645589698678933813141, 100458888720326159403214256751196, 49671851732272421920939825857065], ![-658250351028628080315763637147559, 814948147723355983141505511474046, 402950740137085953174191632041850], ![-837135915958084629158225663145901, 1036417774843032966971728712775969, 512456296306596189370528136183392]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![256718397421941382, -14514344010465847, -13470636543682390]] ![![912061480676338195860715953114044, 100458888720326159403214256751196, 49671851732272421920939825857065]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [24, 33, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 75, 69], [29, 25, 32], [0, 1]]
 g := ![![[75, 24, 96], [36, 33], [21, 56, 31], [15, 95], [24, 88], [1]], ![[89, 75, 66, 60], [69, 21], [67, 58, 52, 72], [62, 19], [45, 81], [67, 84, 72, 57]], ![[61, 25, 80, 72], [22, 88], [71, 72, 64, 40], [73, 6], [98, 5], [29, 70, 88, 44]]]
 h' := ![![[18, 75, 69], [46, 40, 55], [1, 0, 29], [44, 53, 43], [0, 94, 87], [77, 68, 47], [0, 1]], ![[29, 25, 32], [9, 0, 95], [94, 25, 18], [4, 87, 86], [52, 55, 76], [83, 94, 9], [18, 75, 69]], ![[0, 1], [42, 61, 52], [41, 76, 54], [87, 62, 73], [18, 53, 39], [59, 40, 45], [29, 25, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 7], []]
 b := ![[], [10, 100, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [24, 33, 54, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30052318104, 1780587984, -1090635572]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-297547704, 17629584, -10798372]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [83, 0, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 16, 99], [97, 86, 4], [0, 1]]
 g := ![![[74, 15, 98], [26, 42, 9], [31, 15, 58], [97, 14], [14, 97], [1]], ![[11, 22, 91, 45], [17, 66, 77, 12], [76, 62, 25, 70], [100, 46], [47, 17], [52, 22, 59, 39]], ![[79, 72, 15, 81], [70, 4, 10, 58], [71, 52, 17, 100], [76, 61], [2, 9], [71, 65, 99, 64]]]
 h' := ![![[38, 16, 99], [5, 20, 43], [2, 41, 100], [16, 26, 26], [62, 86, 80], [20, 0, 32], [0, 1]], ![[97, 86, 4], [49, 36, 13], [41, 65, 93], [92, 79, 72], [96, 38, 47], [86, 21, 74], [38, 16, 99]], ![[0, 1], [34, 47, 47], [57, 100, 13], [101, 101, 5], [34, 82, 79], [71, 82, 100], [97, 86, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 74], []]
 b := ![[], [82, 12, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [83, 0, 71, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9138984, 931017, 10506]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-88728, 9039, 102]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [64, 27, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 45, 61], [58, 61, 46], [0, 1]]
 g := ![![[97, 53, 1], [67, 60, 75], [3, 75], [23, 35, 4], [1, 33], [1]], ![[56, 96, 48, 62], [41, 36, 11, 44], [63, 61], [13, 17, 92, 27], [46, 39], [26, 93, 55, 34]], ![[103, 23, 68, 67], [70, 50, 31, 94], [20, 11], [56, 77, 102, 93], [14, 36], [17, 53, 17, 73]]]
 h' := ![![[105, 45, 61], [99, 55, 106], [56, 84, 90], [26, 7, 90], [73, 33, 2], [43, 80, 56], [0, 1]], ![[58, 61, 46], [76, 69, 84], [83, 7, 21], [100, 73, 32], [47, 91, 102], [40, 92, 57], [105, 45, 61]], ![[0, 1], [13, 90, 24], [61, 16, 103], [59, 27, 92], [86, 90, 3], [33, 42, 101], [58, 61, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 6], []]
 b := ![[], [40, 45, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [64, 27, 51, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-429498, 65163, -21935]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4014, 609, -205]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![716085093975974, -62776865360457, -20047150028646]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![716085093975974, -62776865360457, -20047150028646]] 
 ![![109, 0, 0], ![0, 109, 0], ![7, 87, 1]] where
  M :=![![![716085093975974, -62776865360457, -20047150028646], ![-2941660223661924, 710814263426936, -273790026744993], ![-7199202396712401, -284894758782576, 921827424811472]]]
  hmulB := by decide  
  f := ![![![-5295841636215833804107917136, -583309762428034770449857200, -288417246123189285136632573]], ![![-42961219131991891085005069269, -4731957684332767634187836098, -2339714319893795281976020854]], ![![-35131497982142311620978244855, -3869554104783890507837619015, -1913299263123757079362678117]]]
  g := ![![![7857019671344, 15425001716805, -20047150028646], ![-9404862719697, 225050886149003, -273790026744993], ![-125247654774245, -738384226764960, 921827424811472]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [36, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 108], [0, 1]]
 g := ![![[20, 106], [36], [10, 20], [7, 61], [74], [43, 1]], ![[0, 3], [36], [107, 89], [14, 48], [74], [86, 108]]]
 h' := ![![[43, 108], [11, 91], [76, 103], [75, 67], [0, 37], [87, 69], [0, 1]], ![[0, 1], [0, 18], [36, 6], [13, 42], [65, 72], [2, 40], [43, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [52, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [36, 66, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![47413, 2342, 2133]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![298, -1681, 2133]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5295841636215833804107917136, -583309762428034770449857200, -288417246123189285136632573]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-5295841636215833804107917136, -583309762428034770449857200, -288417246123189285136632573]] 
 ![![109, 0, 0], ![3, 1, 0], ![62, 0, 1]] where
  M :=![![![-5295841636215833804107917136, -583309762428034770449857200, -288417246123189285136632573], ![-42961219131991891085005069269, -4731957684332767634187836098, -2339714319893795281976020854], ![-54636324116706605662432242840, -6017910547497037786809731709, -2975553126867007122661672444]]]
  hmulB := by decide  
  f := ![![![716085093975974, -62776865360457, -20047150028646]], ![![-7278944419578, 4793428140785, -3063591530559]], ![![341266728713743, -38321655147990, -2945833733620]]]
  g := ![![![131522540465192717300118110, -583309762428034770449857200, -288417246123189285136632573], ![1066944419765336874312584697, -4731957684332767634187836098, -2339714319893795281976020854], ![1356896343041641736724960035, -6017910547497037786809731709, -2975553126867007122661672444]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![716085093975974, -62776865360457, -20047150028646]] ![![-5295841636215833804107917136, -583309762428034770449857200, -288417246123189285136632573]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, 8, -4]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-23, 8, -4]] 
 ![![113, 0, 0], ![0, 113, 0], ![34, 111, 1]] where
  M :=![![![-23, 8, -4], ![-628, 17, 48], ![1704, -180, -23]]]
  hmulB := by decide  
  f := ![![![73, 8, 4]], ![![596, 65, 32]], ![![614, 67, 33]]]
  g := ![![![1, 4, -4], ![-20, -47, 48], ![22, 21, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [77, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 112], [0, 1]]
 g := ![![[41, 91], [97], [72], [91], [77, 106], [7, 1]], ![[0, 22], [97], [72], [91], [28, 7], [14, 112]]]
 h' := ![![[7, 112], [74, 54], [56, 60], [96, 33], [60, 59], [26, 85], [0, 1]], ![[0, 1], [0, 59], [24, 53], [101, 80], [21, 54], [56, 28], [7, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [58, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [77, 106, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4830, 1906, -1179]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![312, 1175, -1179]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, -8, -4]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-73, -8, -4]] 
 ![![113, 0, 0], ![12, 1, 0], ![79, 0, 1]] where
  M :=![![![-73, -8, -4], ![-596, -65, -32], ![-744, -84, -41]]]
  hmulB := by decide  
  f := ![![![23, -8, 4]], ![![8, -1, 0]], ![![1, -4, 3]]]
  g := ![![![3, -8, -4], ![24, -65, -32], ![31, -84, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-23, 8, -4]] ![![-73, -8, -4]]
  ![![113, 0, 0]] where
 M := ![![![-113, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [105, 122, 112, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 93, 85], [106, 33, 42], [0, 1]]
 g := ![![[94, 56, 70], [41, 92, 104], [99, 95, 61], [104, 39, 31], [75, 96, 98], [1]], ![[35, 48, 55, 108], [88, 112, 7, 125], [29, 41, 102, 56], [117, 75, 118, 14], [19, 11, 87, 24], [85, 94, 88, 80]], ![[38, 28, 57, 76], [126, 26, 37, 72], [57, 92, 30, 98], [45, 104, 98, 103], [94, 117, 5, 99], [3, 100, 81, 47]]]
 h' := ![![[36, 93, 85], [13, 50, 18], [19, 49, 55], [2, 109, 51], [126, 50, 44], [22, 5, 15], [0, 1]], ![[106, 33, 42], [61, 15, 18], [28, 110, 11], [105, 116, 26], [14, 51, 114], [12, 95, 31], [36, 93, 85]], ![[0, 1], [119, 62, 91], [81, 95, 61], [57, 29, 50], [25, 26, 96], [76, 27, 81], [106, 33, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125, 35], []]
 b := ![[], [87, 81, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [105, 122, 112, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4712970, 7620, 15240]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![37110, 60, 120]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [15, 80, 97, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 36, 11], [109, 94, 120], [0, 1]]
 g := ![![[5, 101, 55], [50, 77, 45], [85, 15], [80, 64], [42, 129], [34, 1], []], ![[115, 114, 61, 58], [116, 66, 119, 49], [1, 27], [22, 108], [49, 105], [29, 59], [59, 121]], ![[13, 55, 130, 86], [109, 43, 5, 72], [128, 21], [119, 21], [96, 20], [8, 117], [81, 121]]]
 h' := ![![[56, 36, 11], [36, 96, 102], [50, 17, 69], [88, 107, 88], [90, 0, 8], [14, 16, 28], [0, 0, 1], [0, 1]], ![[109, 94, 120], [0, 63, 33], [38, 39, 123], [70, 0, 17], [20, 19, 97], [10, 53, 57], [24, 117, 94], [56, 36, 11]], ![[0, 1], [128, 103, 127], [65, 75, 70], [85, 24, 26], [6, 112, 26], [23, 62, 46], [55, 14, 36], [109, 94, 120]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 45], []]
 b := ![[], [25, 104, 115], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [15, 80, 97, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11424510, 1296900, -605875]
  a := ![5, -10, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-87210, 9900, -4625]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [118, 125, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 66, 106], [130, 70, 31], [0, 1]]
 g := ![![[128, 126, 59], [79, 32], [13, 38], [33, 69, 81], [14, 72], [96, 1], []], ![[124, 87, 41, 116], [119, 25], [21, 44], [16, 125, 33, 90], [119, 81], [43, 105], [73, 2]], ![[39, 117, 78, 55], [131, 50], [34, 130], [112, 62, 62, 23], [18, 76], [129, 109], [11, 2]]]
 h' := ![![[103, 66, 106], [66, 86, 14], [49, 122, 13], [79, 101, 60], [60, 40, 128], [43, 75, 49], [0, 0, 1], [0, 1]], ![[130, 70, 31], [1, 28, 95], [53, 87, 5], [32, 55, 110], [62, 8, 48], [33, 115, 9], [77, 125, 70], [103, 66, 106]], ![[0, 1], [62, 23, 28], [83, 65, 119], [56, 118, 104], [61, 89, 98], [104, 84, 79], [121, 12, 66], [130, 70, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25], []]
 b := ![[], [123, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [118, 125, 41, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22694324, -1072162, -991332]
  a := ![-6, -2, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![165652, -7826, -7236]
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



lemma PB225I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB225I2 : PrimesBelowBoundCertificateInterval O 79 137 225 where
  m := 11
  g := ![1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB225I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0]
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
    · exact ![571787]
    · exact ![89, 89, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![2248091]
    · exact ![2571353]
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
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I89N0, I89N1, I97N1, I109N1, I113N1]
  Il := ![[], [I89N0, I89N0, I89N1], [I97N1], [], [], [], [I109N1], [I113N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
