
import IdealArithmetic.Examples.NF3_1_189283_1.RI3_1_189283_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [27, 25, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 35, 21], [23, 1, 16], [0, 1]]
 g := ![![[0, 1, 10], [15, 4], [20, 15, 11], [23, 1], []], ![[6, 4, 20, 16], [28, 11], [30, 22, 2, 10], [28, 1], [32, 34]], ![[15, 26, 34, 36], [4, 34], [32, 2, 1, 26], [28, 4], [0, 34]]]
 h' := ![![[0, 35, 21], [5, 2, 26], [15, 10, 35], [8, 27, 23], [0, 0, 1], [0, 1]], ![[23, 1, 16], [0, 24, 31], [4, 12, 23], [5, 22, 35], [24, 21, 1], [0, 35, 21]], ![[0, 1], [4, 11, 17], [1, 15, 16], [31, 25, 16], [11, 16, 35], [23, 1, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 8], []]
 b := ![[], [28, 18, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [27, 25, 14, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-243534, 131868, -98235]
  a := ![0, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6582, 3564, -2655]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4192301041, -238335844, -229321150]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-4192301041, -238335844, -229321150]] 
 ![![41, 0, 0], ![0, 41, 0], ![5, 12, 1]] where
  M :=![![![-4192301041, -238335844, -229321150], ![-17428407400, -990819635, -953343376], ![-13756422294, -782064190, -752483791]]]
  hmulB := by decide  
  f := ![![![30955, -7656, 266]], ![![20216, 19309, -30624]], ![![-4623, 7642, -8273]]]
  g := ![![![-74285251, 61305316, -229321150], ![-308821720, 254860997, -953343376], ![-243756179, 201164422, -752483791]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [15, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 40], [0, 1]]
 g := ![![[14, 39], [9], [21], [25, 25], [1]], ![[24, 2], [9], [21], [23, 16], [1]]]
 h' := ![![[36, 40], [11, 30], [8, 38], [35, 12], [26, 36], [0, 1]], ![[0, 1], [25, 11], [23, 3], [16, 29], [10, 5], [36, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [6, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [15, 5, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![239, 508, -518]
  a := ![-1, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![69, 164, -518]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30955, -7656, 266]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![30955, -7656, 266]] 
 ![![41, 0, 0], ![34, 1, 0], ![10, 0, 1]] where
  M :=![![![30955, -7656, 266], ![20216, 19309, -30624], ![-586910, 119894, 26965]]]
  hmulB := by decide  
  f := ![![![-4192301041, -238335844, -229321150]], ![![-3901625434, -221810691, -213421036]], ![![-1358034944, -77205430, -74285251]]]
  g := ![![![7039, -7656, 266], ![-8050, 19309, -30624], ![-120316, 119894, 26965]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-4192301041, -238335844, -229321150]] ![![30955, -7656, 266]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![303635, -36592, -46174]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![303635, -36592, -46174]] 
 ![![43, 0, 0], ![0, 43, 0], ![23, 27, 1]] where
  M :=![![![303635, -36592, -46174], ![-3509224, 959653, -146368], ![-1903686, -328426, 996245]]]
  hmulB := by decide  
  f := ![![![-21115777819, -1200449748, -1155044546]], ![![-87783385496, -4990559377, -4801798992]], ![![-68025642621, -3867315059, -3721039697]]]
  g := ![![![31759, 28142, -46174], ![-3320, 114223, -146368], ![-577147, -633187, 996245]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [19, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 42], [0, 1]]
 g := ![![[7, 11], [14, 4], [36], [2, 16], [1]], ![[6, 32], [41, 39], [36], [24, 27], [1]]]
 h' := ![![[39, 42], [35, 21], [29, 2], [5, 6], [24, 39], [0, 1]], ![[0, 1], [37, 22], [21, 41], [24, 37], [40, 4], [39, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [23, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [19, 4, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3840, 19, 109]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31, -68, 109]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21115777819, 1200449748, 1155044546]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![21115777819, 1200449748, 1155044546]] 
 ![![43, 0, 0], ![21, 1, 0], ![35, 0, 1]] where
  M :=![![![21115777819, 1200449748, 1155044546], ![87783385496, 4990559377, 4801798992], ![69288334474, 3939100154, 3790109629]]]
  hmulB := by decide  
  f := ![![![-303635, 36592, 46174]], ![![-66677, -4447, 25954]], ![![-202873, 37422, 14415]]]
  g := ![![![-1035354093, 1200449748, 1155044546], ![-4304216887, 4990559377, 4801798992], ![-3397362925, 3939100154, 3790109629]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![303635, -36592, -46174]] ![![21115777819, 1200449748, 1155044546]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1992621, 13166801, -17288655]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![1992621, 13166801, -17288655]] 
 ![![47, 0, 0], ![0, 47, 0], ![26, 17, 1]] where
  M :=![![![1992621, 13166801, -17288655], ![-1313937780, 274489247, 52667204], ![1329161321, -525986460, 261322446]]]
  hmulB := by decide  
  f := ![![![-2115583779080766, -120272719112682, -115723584827387]], ![![-8794992446881412, -500002725782643, -481090876450728]], ![![-4499192093487817, -255782858729038, -246108257698817]]]
  g := ![![![9606333, 6533488, -17288655], ![-57091172, -13209643, 52667204], ![-116281325, -105712086, 261322446]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [13, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 46], [0, 1]]
 g := ![![[19, 27], [20, 36], [20, 8], [41, 3], [1]], ![[24, 20], [11, 11], [18, 39], [5, 44], [1]]]
 h' := ![![[35, 46], [22, 11], [22, 6], [31, 14], [34, 35], [0, 1]], ![[0, 1], [31, 36], [44, 41], [4, 33], [37, 12], [35, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [6, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [13, 12, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1223, 975, -1325]
  a := ![1, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![759, 500, -1325]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2115583779080766, -120272719112682, -115723584827387]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-2115583779080766, -120272719112682, -115723584827387]] 
 ![![47, 0, 0], ![26, 1, 0], ![36, 0, 1]] where
  M :=![![![-2115583779080766, -120272719112682, -115723584827387], ![-8794992446881412, -500002725782643, -481090876450728], ![-6941978540843479, -394657325030123, -379730006669961]]]
  hmulB := by decide  
  f := ![![![1992621, 13166801, -17288655]], ![![-26853822, 13123959, -8443358]], ![![29806291, -1105992, -7682322]]]
  g := ![![![110160765353934, -120272719112682, -115723584827387], ![457964893099862, -500002725782643, -481090876450728], ![361476428724645, -394657325030123, -379730006669961]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![1992621, 13166801, -17288655]] ![![-2115583779080766, -120272719112682, -115723584827387]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1777082376621276286911883, -101028629372615571732279, -97207373770630384556015]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-1777082376621276286911883, -101028629372615571732279, -97207373770630384556015]] 
 ![![53, 0, 0], ![0, 53, 0], ![43, 14, 1]] where
  M :=![![![-1777082376621276286911883, -101028629372615571732279, -97207373770630384556015], ![-7387760406567909226257140, -420000399434436090303937, -404114517490462286929116], ![-5831235730676806145088919, -331510661052743730580100, -318971770061820518571658]]]
  hmulB := by decide  
  f := ![![![-626416487282, 122433185794, 35787724447]], ![![2719867057972, -1040799168193, 489732743176]], ![![372965758761, -197416837509, 136450909466]]]
  g := ![![![45336503688977929226354, 23771218932381317208527, -97207373770630384556015], ![188474789538150360598016, 98822695196830866541579, -404114517490462286929116], ![148765101546820304782875, 78001775845523462819304, -318971770061820518571658]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [30, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 52], [0, 1]]
 g := ![![[4, 37], [1], [], [49], [39, 1]], ![[16, 16], [1], [], [49], [25, 52]]]
 h' := ![![[39, 52], [23, 39], [0, 52], [30], [49, 7], [0, 1]], ![[0, 1], [7, 14], [14, 1], [30], [4, 46], [39, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [4, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [30, 14, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1227, 487, -817]
  a := ![0, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![686, 225, -817]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1765169781567412848710, 100351388313677700120, 96555748333783315963]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![1765169781567412848710, 100351388313677700120, 96555748333783315963]] 
 ![![53, 0, 0], ![50, 1, 0], ![25, 0, 1]] where
  M :=![![![1765169781567412848710, 100351388313677700120, 96555748333783315963], ![7338236873367532013188, 417184944874340809385, 401405553254710800480], ![5792146293497622205823, 329288393636717501497, 316833556560663109265]]]
  hmulB := by decide  
  f := ![![![144324133465, -28387115189, -8018655155]], ![![124656393990, -22323375733, -9707192802]], ![![30245981702, -8230671695, 1210143055]]]
  g := ![![![-106911195140774623705, 100351388313677700120, 96555748333783315963], ![-444455645315420348454, 417184944874340809385, 401405553254710800480], ![-350813439667072275484, 329288393636717501497, 316833556560663109265]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-1777082376621276286911883, -101028629372615571732279, -97207373770630384556015]] ![![1765169781567412848710, 100351388313677700120, 96555748333783315963]]
  ![![53, 0, 0]] where
 M := ![![![-4441263453581981619439773774678180884016191727, -252489566775834640630550964278521230372018830, -242939529548995914214257024812239135730961224]]]
 hmul := by decide  
 g := ![![![![-83797423652490219234712712729776997811626259, -4763954090110087559066999326009834535321110, -4583764708471621022910509902117719542093608]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![64632795232063, 3674428828241, 3535449097137]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![64632795232063, 3674428828241, 3535449097137]] 
 ![![59, 0, 0], ![25, 1, 0], ![44, 0, 1]] where
  M :=![![![64632795232063, 3674428828241, 3535449097137], ![268694131382412, 15275487603249, 14697715312964], ![212083058100713, 12057100421988, 11601058775008]]]
  hmulB := by decide  
  f := ![![![-26251440, 7247428, -1181789]], ![![-12645796, 3049297, -9407]], ![![-9861099, 3181719, -1025819]]]
  g := ![![![-3098096368610, 3674428828241, 3535449097137], ![-12879534448631, 15275487603249, 14697715312964], ![-10165949805921, 12057100421988, 11601058775008]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1067359337, 60680277, 58385137]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![1067359337, 60680277, 58385137]] 
 ![![59, 0, 0], ![39, 1, 0], ![23, 0, 1]] where
  M :=![![![1067359337, 60680277, 58385137], ![4437270412, 252262559, 242721108], ![3502383449, 199113448, 191582282]]]
  hmulB := by decide  
  f := ![![![119254, -29738, 1333]], ![![80546, -18479, -1135]], ![![7753, -3603, 2202]]]
  g := ![![![-44780163, 60680277, 58385137], ![-186161947, 252262559, 242721108], ![-146939551, 199113448, 191582282]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5161212161, -12329186025, 17193091853]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-5161212161, -12329186025, 17193091853]] 
 ![![59, 0, 0], ![53, 1, 0], ![22, 0, 1]] where
  M :=![![![-5161212161, -12329186025, 17193091853], ![1306674980828, -275386775981, -49316744100], ![-1263686883107, 511606535582, -263057589956]]]
  hmulB := by decide  
  f := ![![![-97673350190499766213036, -5552812197000743248546, -5342785446699088385293]], ![![-94622699221112175026664, -5379380120814467387375, -5175913177339909447707]], ![![-41852788265690994309419, -2379366251970981051871, -2289370310464294659493]]]
  g := ![![![4576908922, -12329186025, 17193091853], ![287917669119, -275386775981, -49316744100], ![-382907903219, 511606535582, -263057589956]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![64632795232063, 3674428828241, 3535449097137]] ![![1067359337, 60680277, 58385137]]
  ![![97673350190499766213036, 5552812197000743248546, 5342785446699088385293]] where
 M := ![![![97673350190499766213036, 5552812197000743248546, 5342785446699088385293]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![97673350190499766213036, 5552812197000743248546, 5342785446699088385293]] ![![-5161212161, -12329186025, 17193091853]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2797, -159, -153]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-2797, -159, -153]] 
 ![![61, 0, 0], ![1, 1, 0], ![30, 0, 1]] where
  M :=![![![-2797, -159, -153], ![-11628, -661, -636], ![-9177, -522, -502]]]
  hmulB := by decide  
  f := ![![![170, -48, 9]], ![![14, -1, -3]], ![![21, -9, 5]]]
  g := ![![![32, -159, -153], ![133, -661, -636], ![105, -522, -502]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, -1]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-1, 1, -1]] 
 ![![61, 0, 0], ![60, 1, 0], ![0, 0, 1]] where
  M :=![![![-1, 1, -1], ![-76, 15, 4], ![95, -34, 14]]]
  hmulB := by decide  
  f := ![![![-346, -20, -19]], ![![-364, -21, -20]], ![![-19, -1, -1]]]
  g := ![![![-1, 1, -1], ![-16, 15, 4], ![35, -34, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-2797, -159, -153]] ![![-1, 1, -1]]
  ![![346, 20, 19]] where
 M := ![![![346, 20, 19]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![346, 20, 19]] ![![-1, 1, -1]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [49, 37, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 22, 42], [41, 44, 25], [0, 1]]
 g := ![![[9, 5, 40], [60, 4, 22], [29, 65], [45, 17], [2, 1], []], ![[36, 39, 54, 41], [58, 16, 26, 20], [64, 65], [1, 24], [34, 60], [16, 22]], ![[63, 12, 29, 25], [25, 42, 18, 29], [], [27, 56], [6, 15], [33, 22]]]
 h' := ![![[28, 22, 42], [8, 56, 43], [23, 41, 42], [29, 36, 20], [36, 11, 34], [0, 0, 1], [0, 1]], ![[41, 44, 25], [35, 19, 23], [32, 60, 19], [32, 5, 47], [9, 23, 15], [0, 31, 44], [28, 22, 42]], ![[0, 1], [31, 59, 1], [37, 33, 6], [38, 26], [50, 33, 18], [64, 36, 22], [41, 44, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 12], []]
 b := ![[], [18, 9, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [49, 37, 65, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![148168289, -72803138, 55689596]
  a := ![1, 20, 61]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2211467, -1086614, 831188]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [3, 20, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 18, 47], [38, 52, 24], [0, 1]]
 g := ![![[63, 29, 38], [46, 56, 25], [70, 17, 15], [33, 29], [62, 1], []], ![[17, 14, 68, 46], [64, 36, 62, 11], [4, 44, 15, 47], [64, 50], [36, 6], [58, 8]], ![[58, 6, 44, 20], [67, 32, 5, 36], [60, 48, 0, 43], [54, 15], [13, 40], [10, 8]]]
 h' := ![![[24, 18, 47], [4, 57, 40], [3, 50, 66], [62, 7, 21], [27, 35, 61], [0, 0, 1], [0, 1]], ![[38, 52, 24], [57, 12, 2], [45, 15, 31], [10, 9, 1], [42, 67, 60], [47, 35, 52], [24, 18, 47]], ![[0, 1], [13, 2, 29], [16, 6, 45], [60, 55, 49], [68, 40, 21], [65, 36, 18], [38, 52, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 33], []]
 b := ![[], [3, 47, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [3, 20, 9, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![53818, -33228, 31453]
  a := ![-1, 2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![758, -468, 443]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [40, 72, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 71, 45], [9, 1, 28], [0, 1]]
 g := ![![[23, 43, 6], [41, 4], [70, 1], [52, 69, 6], [38, 1], []], ![[33, 30, 48, 15], [46, 65], [49, 8], [1, 42, 39, 17], [33, 1], [47, 54]], ![[14, 58, 54, 40], [17, 46], [27, 64], [25, 38, 2, 21], [69, 4], [64, 54]]]
 h' := ![![[29, 71, 45], [4, 67, 58], [29, 46, 71], [37, 16, 1], [13, 71, 58], [0, 0, 1], [0, 1]], ![[9, 1, 28], [12, 13, 7], [10, 59, 24], [46, 2, 64], [64, 5, 41], [56, 34, 1], [29, 71, 45]], ![[0, 1], [51, 66, 8], [72, 41, 51], [38, 55, 8], [23, 70, 47], [3, 39, 71], [9, 1, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 65], []]
 b := ![[], [69, 24, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [40, 72, 35, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1163182, -450775, 277765]
  a := ![0, 3, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15934, -6175, 3805]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [5, 23, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 29, 14], [75, 49, 65], [0, 1]]
 g := ![![[73, 0, 22], [33, 31, 67], [1, 57, 9], [49, 44, 46], [26, 1], []], ![[76, 48, 72, 56], [73, 70, 65, 34], [70, 62, 28, 3], [24, 42, 70, 75], [2, 31], [62, 38]], ![[7, 48, 43, 36], [59, 5, 68, 9], [16, 62, 13, 16], [0, 29, 58, 11], [59, 51], [11, 38]]]
 h' := ![![[30, 29, 14], [72, 59, 38], [74, 72, 15], [71, 69, 76], [28, 29, 21], [0, 0, 1], [0, 1]], ![[75, 49, 65], [9, 24, 2], [24, 77, 5], [55, 49, 29], [16, 48, 13], [37, 45, 49], [30, 29, 14]], ![[0, 1], [13, 75, 39], [70, 9, 59], [70, 40, 53], [41, 2, 45], [40, 34, 29], [75, 49, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 41], []]
 b := ![[], [67, 8, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [5, 23, 53, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4287725, 3461148, -3243582]
  a := ![2, -8, -22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-54275, 43812, -41058]
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



lemma PB124I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB124I1 : PrimesBelowBoundCertificateInterval O 31 79 124 where
  m := 11
  g := ![1, 2, 2, 2, 2, 3, 3, 1, 1, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB124I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1, I61N1]
    · exact ![I67N0]
    · exact ![I71N0]
    · exact ![I73N0]
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
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![61, 61, 61]
    · exact ![300763]
    · exact ![357911]
    · exact ![389017]
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
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I41N1, I43N1, I47N1, I53N1, I59N0, I59N1, I59N2, I61N0, I61N1]
  Il := ![[], [I41N1], [I43N1], [I47N1], [I53N1], [I59N0, I59N1, I59N2], [I61N0, I61N1, I61N1], [], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
