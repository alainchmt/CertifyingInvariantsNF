
import IdealArithmetic.Examples.NF3_1_470372_1.RI3_1_470372_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [7, 12, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 1, 29], [17, 35, 8], [0, 1]]
 g := ![![[1, 15, 12], [3, 21], [1, 32, 11], [10, 1], []], ![[27, 9, 1, 18], [24, 25], [23, 12, 19, 31], [20, 4], [32, 27]], ![[19, 27, 2, 13], [5, 27], [16, 13, 10, 35], [0, 1], [16, 27]]]
 h' := ![![[30, 1, 29], [28, 11, 7], [30, 2, 13], [4, 21, 14], [0, 0, 1], [0, 1]], ![[17, 35, 8], [21, 9, 9], [35, 30, 32], [34, 17, 26], [10, 5, 35], [30, 1, 29]], ![[0, 1], [11, 17, 21], [34, 5, 29], [27, 36, 34], [29, 32, 1], [17, 35, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 28], []]
 b := ![[], [30, 17, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [7, 12, 27, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20239, 15836, -47360]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![547, 428, -1280]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [37, 23, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 9, 3], [20, 31, 38], [0, 1]]
 g := ![![[38, 35, 33], [3, 8], [40, 10], [0, 8, 1], []], ![[40, 33, 34, 12], [24, 16], [17, 18], [5, 0, 36, 13], [3, 9]], ![[10, 10, 5, 35], [36, 9], [13, 36], [38, 32, 36, 3], [9, 9]]]
 h' := ![![[29, 9, 3], [28, 33, 22], [37, 22, 7], [0, 32, 25], [0, 0, 1], [0, 1]], ![[20, 31, 38], [30, 26, 2], [4, 13, 37], [31, 8, 10], [33, 38, 31], [29, 9, 3]], ![[0, 1], [30, 23, 17], [3, 6, 38], [19, 1, 6], [26, 3, 9], [20, 31, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 29], []]
 b := ![[], [8, 3, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [37, 23, 33, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5607406, -1125040, 358176]
  a := ![-3, 0, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![136766, -27440, 8736]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-94406150720717491061, 526197036220754008, 40222691297873650214]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-94406150720717491061, 526197036220754008, 40222691297873650214]] 
 ![![43, 0, 0], ![0, 43, 0], ![28, 14, 1]] where
  M :=![![![-94406150720717491061, 526197036220754008, 40222691297873650214], ![4342998266097912715096, -736916817414254386469, -75183412233539760348], ![-1552078372003104575696, 554698525590699038868, -698798914261263752287]]]
  hmulB := by decide  
  f := ![![![12945599995924863631729612019680619483969, 527422638972532843664810394821095277536, 688400380706391248565952210907672094874]], ![![73292395838345189157793217988386395691320, 2986039182567669342003997434800056521057, 3897425628312545939516199526395608585612]], ![![32976650497755970396992921455647402125780, 1343516873337377730045512087854914975662, 1753579499152058775092654961427364799089]]]
  g := ![![![-28387011792120458071, -13083522817070008116, 40222691297873650214], ![149956600200861069880, 7340719857100052521, -75183412233539760348], ![418937005286332104380, 240415891284846315602, -698798914261263752287]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [10, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 42], [0, 1]]
 g := ![![[21, 13], [10, 41], [23], [25, 25], [1]], ![[0, 30], [0, 2], [23], [21, 18], [1]]]
 h' := ![![[5, 42], [29, 20], [6, 16], [8, 18], [33, 5], [0, 1]], ![[0, 1], [0, 23], [0, 27], [12, 25], [15, 38], [5, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [14, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [10, 38, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![755273, -69026, -50879]
  a := ![1, -64, -69]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![50695, 14960, -50879]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12945599995924863631729612019680619483969, -527422638972532843664810394821095277536, -688400380706391248565952210907672094874]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-12945599995924863631729612019680619483969, -527422638972532843664810394821095277536, -688400380706391248565952210907672094874]] 
 ![![43, 0, 0], ![34, 1, 0], ![15, 0, 1]] where
  M :=![![![-12945599995924863631729612019680619483969, -527422638972532843664810394821095277536, -688400380706391248565952210907672094874], ![-73292395838345189157793217988386395691320, -2986039182567669342003997434800056521057, -3897425628312545939516199526395608585612], ![-29425629780777897173161434204371406178928, -1198843106328951981286364635569884887660, -1564749007383929215910708066423347505787]]]
  hmulB := by decide  
  f := ![![![94406150720717491061, -526197036220754008, -40222691297873650214]], ![![-26353235851012046954, 16721537632156947679, -30055537020794519696]], ![![69027224018927138177, -13083522817070008116, 2219966157980441839]]]
  g := ![![![356111056738072599566586617857016311055, -527422638972532843664810394821095277536, -688400380706391248565952210907672094874], ![2016146995201017617746178783505805925786, -2986039182567669342003997434800056521057, -3897425628312545939516199526395608585612], ![809448161515474614633385683752439362519, -1198843106328951981286364635569884887660, -1564749007383929215910708066423347505787]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-94406150720717491061, 526197036220754008, 40222691297873650214]] ![![-12945599995924863631729612019680619483969, -527422638972532843664810394821095277536, -688400380706391248565952210907672094874]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-342693847637, 304891350774, -608647639132]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-342693847637, 304891350774, -608647639132]] 
 ![![47, 0, 0], ![12, 1, 0], ![30, 0, 1]] where
  M :=![![![-342693847637, 304891350774, -608647639132], ![-66343727727804, 10005451080023, 4266208786004], ![57274171448872, -13399328560232, 8177238037795]]]
  hmulB := by decide  
  f := ![![![138981288387077225956062213, 5662300543195336647695294, 7390524337755384824027132]], ![![52226116766725906365367792, 2127768225270761315731111, 2777196783181004568451580]], ![![95432896526961654120678146, 3888075496453406395832212, 5074777709936538830235715]]]
  g := ![![![303362534405, 304891350774, -608647639132], ![-6689263920600, 10005451080023, 4266208786004], ![-579809084302, -13399328560232, 8177238037795]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-80051943, -3261433, -4256874]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-80051943, -3261433, -4256874]] 
 ![![47, 0, 0], ![37, 1, 0], ![20, 0, 1]] where
  M :=![![![-80051943, -3261433, -4256874], ![-453219526, -18464825, -24100582], ![-181959804, -7413308, -9675967]]]
  hmulB := by decide  
  f := ![![![-15519, 1519, 3044]], ![![-5287, -106, 2590]], ![![-5704, 1036, -71]]]
  g := ![![![2675714, -3261433, -4256874], ![15148737, -18464825, -24100582], ![6081956, -7413308, -9675967]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1284571356743596321, 52335312008366397, 68308878020731772]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![1284571356743596321, 52335312008366397, 68308878020731772]] 
 ![![47, 0, 0], ![45, 1, 0], ![28, 0, 1]] where
  M :=![![![1284571356743596321, 52335312008366397, 68308878020731772], ![7272688202222298582, 296299932428620763, 386735364042200426], ![2919858576074299996, 118959300156382456, 155267562415886947]]]
  hmulB := by decide  
  f := ![![![282754305, 116872073, -415496914]], ![![-689009939, 264333880, -355269076]], ![![790620872, -93925360, -113881909]]]
  g := ![![![-63471622727944280, 52335312008366397, 68308878020731772], ![-359348913835047823, 296299932428620763, 386735364042200426], ![-144272376140590320, 118959300156382456, 155267562415886947]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-342693847637, 304891350774, -608647639132]] ![![-80051943, -3261433, -4256874]]
  ![![-282754305, -116872073, 415496914]] where
 M := ![![![-282754305, -116872073, 415496914]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-282754305, -116872073, 415496914]] ![![1284571356743596321, 52335312008366397, 68308878020731772]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21303925, -867953, -1132866]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-21303925, -867953, -1132866]] 
 ![![53, 0, 0], ![0, 53, 0], ![48, 9, 1]] where
  M :=![![![-21303925, -867953, -1132866], ![-120613622, -4913975, -6413798], ![-48424284, -1972876, -2575029]]]
  hmulB := by decide  
  f := ![![![241, 57, -248]], ![![-26898, 4323, 1066]], ![![-4046, 703, 29]]]
  g := ![![![624031, 175997, -1132866], ![3532994, 996419, -6413798], ![1418436, 400045, -2575029]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [22, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 52], [0, 1]]
 g := ![![[5, 38], [11], [11, 43], [36], [49, 1]], ![[12, 15], [11], [51, 10], [36], [45, 52]]]
 h' := ![![[49, 52], [22, 12], [23, 45], [9, 19], [35, 47], [0, 1]], ![[0, 1], [27, 41], [2, 8], [39, 34], [6, 6], [49, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [3, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [22, 4, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4775, 2288, -3126]
  a := ![3, -1, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2741, 574, -3126]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 57, -248]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![241, 57, -248]] 
 ![![53, 0, 0], ![18, 1, 0], ![38, 0, 1]] where
  M :=![![![241, 57, -248], ![-26898, 4323, 1066], ![16076, -4384, 3847]]]
  hmulB := by decide  
  f := ![![![-21303925, -867953, -1132866]], ![![-9511024, -387493, -505762]], ![![-16188178, -659530, -860829]]]
  g := ![![![163, 57, -248], ![-2740, 4323, 1066], ![-966, -4384, 3847]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-21303925, -867953, -1132866]] ![![241, 57, -248]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [31, 6, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 40, 42], [18, 18, 17], [0, 1]]
 g := ![![[5, 56, 48], [55, 33, 21], [37, 3], [16, 36, 7], [1]], ![[42, 24, 2, 10], [53, 12, 47, 23], [57, 4], [31, 51, 33, 23], [19, 49, 56, 43]], ![[49, 41], [50, 46, 10, 25], [20, 51], [14, 20, 55, 25], [53, 11, 21, 16]]]
 h' := ![![[22, 40, 42], [6, 11, 44], [19, 51, 32], [35, 44, 48], [28, 53, 40], [0, 1]], ![[18, 18, 17], [58, 2, 15], [32, 48, 4], [18, 11, 57], [29, 43, 55], [22, 40, 42]], ![[0, 1], [56, 46], [57, 19, 23], [38, 4, 13], [0, 22, 23], [18, 18, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 37], []]
 b := ![[], [40, 18, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [31, 6, 19, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11033, 15576, -44250]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![187, 264, -750]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [17, 53, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 41, 37], [47, 19, 24], [0, 1]]
 g := ![![[39], [50, 14], [50, 31, 13], [49, 54, 36], [1]], ![[30, 35, 2, 43], [], [44, 21, 16, 44], [36, 22, 11, 37], [2, 26, 11, 23]], ![[38, 3, 11, 18], [41, 14], [31, 8, 41, 31], [49, 13, 30, 17], [37, 33, 30, 38]]]
 h' := ![![[8, 41, 37], [20, 51], [4, 9, 21], [21, 7, 47], [44, 8, 55], [0, 1]], ![[47, 19, 24], [1, 17, 57], [1, 39], [5, 19, 54], [51, 4, 60], [8, 41, 37]], ![[0, 1], [38, 54, 4], [8, 13, 40], [60, 35, 21], [43, 49, 7], [47, 19, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 5], []]
 b := ![[], [5, 2, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [17, 53, 6, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5297423, -189588, -808494]
  a := ![-1, 21, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![86843, -3108, -13254]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [40, 1, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 19, 50], [27, 47, 17], [0, 1]]
 g := ![![[6, 53, 16], [62], [21, 35], [65, 14], [55, 1], []], ![[49, 1, 64, 58], [32, 65, 65, 43], [14, 55], [3, 47], [34, 65], [40, 21]], ![[42, 17, 0, 1], [15, 32, 49, 24], [2, 37], [21, 29], [66, 26], [6, 21]]]
 h' := ![![[28, 19, 50], [66, 28, 63], [31, 53], [0, 32, 54], [11, 39, 9], [0, 0, 1], [0, 1]], ![[27, 47, 17], [27, 64, 6], [41, 2, 37], [47, 25, 51], [57, 52, 28], [55, 50, 47], [28, 19, 50]], ![[0, 1], [5, 42, 65], [55, 12, 30], [1, 10, 29], [38, 43, 30], [20, 17, 19], [27, 47, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 55], []]
 b := ![[], [66, 11, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [40, 1, 12, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-670804, 126764, -20502]
  a := ![1, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10012, 1892, -306]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [47, 26, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 32, 69], [7, 38, 2], [0, 1]]
 g := ![![[25, 39, 57], [46, 36, 32], [27, 46, 2], [17, 16], [39, 1], []], ![[17, 66, 5, 11], [48, 35, 29, 41], [24, 57, 35, 51], [36, 4], [64, 24], [28, 4]], ![[3, 64, 12, 37], [5, 47, 8, 8], [14, 59, 47, 30], [27, 36], [6, 30], [24, 4]]]
 h' := ![![[32, 32, 69], [39, 33, 25], [9, 57, 23], [9, 46, 12], [13, 4, 4], [0, 0, 1], [0, 1]], ![[7, 38, 2], [43, 33, 32], [16, 28, 50], [36, 4, 9], [38, 41, 2], [63, 67, 38], [32, 32, 69]], ![[0, 1], [62, 5, 14], [15, 57, 69], [21, 21, 50], [56, 26, 65], [57, 4, 32], [7, 38, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 5], []]
 b := ![[], [53, 52, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [47, 26, 32, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![672299, -192268, 227200]
  a := ![-2, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9469, -2708, 3200]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12343, 2576, -986]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-12343, 2576, -986]] 
 ![![73, 0, 0], ![0, 73, 0], ![12, 31, 1]] where
  M :=![![![-12343, 2576, -986], ![-111640, 8585, 27732], ![317648, -55020, -2705]]]
  hmulB := by decide  
  f := ![![![-20583455, -838600, -1094554]], ![![-116534632, -4747791, -6196892]], ![![-53511804, -2180149, -2845565]]]
  g := ![![![-7, 454, -986], ![-6088, -11659, 27732], ![4796, 395, -2705]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [33, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 72], [0, 1]]
 g := ![![[16, 38], [9], [12], [67, 25], [70], [1]], ![[27, 35], [9], [12], [7, 48], [70], [1]]]
 h' := ![![[56, 72], [49, 44], [45, 3], [52, 42], [20, 5], [40, 56], [0, 1]], ![[0, 1], [31, 29], [67, 70], [68, 31], [8, 68], [37, 17], [56, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [25, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [33, 17, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4383, -485, -310]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![111, 125, -310]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20583455, -838600, -1094554]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-20583455, -838600, -1094554]] 
 ![![73, 0, 0], ![57, 1, 0], ![65, 0, 1]] where
  M :=![![![-20583455, -838600, -1094554], ![-116534632, -4747791, -6196892], ![-46786640, -1906156, -2487945]]]
  hmulB := by decide  
  f := ![![![-12343, 2576, -986]], ![![-11167, 2129, -390]], ![![-6639, 1540, -915]]]
  g := ![![![1347435, -838600, -1094554], ![7628595, -4747791, -6196892], ![3062749, -1906156, -2487945]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-12343, 2576, -986]] ![![-20583455, -838600, -1094554]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [32, 16, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 68, 8], [55, 10, 71], [0, 1]]
 g := ![![[16, 61, 32], [59, 45, 49], [5, 6, 73], [42, 65, 32], [17, 1], []], ![[63, 26, 42, 19], [47, 57, 60, 36], [26, 49, 63, 32], [72, 11, 66, 64], [40, 21], [43, 64]], ![[5, 75], [36, 38, 52, 57], [18, 74, 53, 68], [53, 33, 53, 15], [73, 42], [59, 64]]]
 h' := ![![[41, 68, 8], [8, 69, 36], [77, 45, 72], [78, 15, 51], [9, 12, 36], [0, 0, 1], [0, 1]], ![[55, 10, 71], [71, 45, 43], [24, 7, 53], [53, 26, 77], [26, 40, 61], [68, 75, 10], [41, 68, 8]], ![[0, 1], [21, 44], [44, 27, 33], [35, 38, 30], [47, 27, 61], [31, 4, 68], [55, 10, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 32], []]
 b := ![[], [46, 24, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [32, 16, 62, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6253008, -919560, -458832]
  a := ![-2, -6, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![79152, -11640, -5808]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB195I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB195I1 : PrimesBelowBoundCertificateInterval O 31 79 195 where
  m := 11
  g := ![1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB195I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![300763]
    · exact ![357911]
    · exact ![5329, 73]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
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
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I43N1, I47N0, I47N1, I47N2, I53N1, I73N1]
  Il := ![[], [], [I43N1], [I47N0, I47N1, I47N2], [I53N1], [], [], [], [], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
