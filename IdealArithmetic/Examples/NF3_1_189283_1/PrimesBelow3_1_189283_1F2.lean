
import IdealArithmetic.Examples.NF3_1_189283_1.RI3_1_189283_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [7, 79, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 60, 27], [50, 22, 56], [0, 1]]
 g := ![![[13, 62, 4], [53, 8, 29], [5, 23], [75, 77], [25, 42, 1], []], ![[75, 16, 31, 4], [28, 53, 49, 33], [19, 7], [2, 17], [10, 57, 69, 37], [77, 65]], ![[43, 62, 41, 34], [69, 5, 49, 56], [16, 78], [17, 27], [37, 43, 55, 76], [48, 65]]]
 h' := ![![[75, 60, 27], [44, 68, 81], [59, 10, 64], [54, 16, 40], [74, 55, 49], [0, 0, 1], [0, 1]], ![[50, 22, 56], [35, 69, 49], [40, 53, 18], [16, 6, 67], [14, 19, 73], [23, 55, 22], [75, 60, 27]], ![[0, 1], [29, 29, 36], [30, 20, 1], [15, 61, 59], [47, 9, 44], [6, 28, 60], [50, 22, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 38], []]
 b := ![[], [37, 70, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [7, 79, 41, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-211235, 145665, -118026]
  a := ![0, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2545, 1755, -1422]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-126916709632106021, -7215321803479075, -6942413133601151]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-126916709632106021, -7215321803479075, -6942413133601151]] 
 ![![89, 0, 0], ![42, 1, 0], ![38, 0, 1]] where
  M :=![![![-126916709632106021, -7215321803479075, -6942413133601151], ![-527623398153687476, -29995834431567831, -28861287213916300], ![-416458607525987831, -23676022486235744, -22780512628088756]]]
  hmulB := by decide  
  f := ![![![1181818964, -366960644, 104750981]], ![![647162596, -181671387, 32940434]], ![![168874641, -72469957, 40349343]]]
  g := ![![![4943129271807403, -7215321803479075, -6942413133601151], ![20549781596640234, -29995834431567831, -28861287213916300], ![16220155244531305, -23676022486235744, -22780512628088756]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![848563, -176667, -34777]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![848563, -176667, -34777]] 
 ![![89, 0, 0], ![63, 1, 0], ![60, 0, 1]] where
  M :=![![![848563, -176667, -34777], ![-2643052, 1193551, -706668], ![-12765929, 1989242, 1370218]]]
  hmulB := by decide  
  f := ![![![-3041158729774, -172892434372, -166353038683]], ![![-2294784617030, -130460437633, -125525968253]], ![![-2162344281615, -122931093053, -118281409781]]]
  g := ![![![158036, -176667, -34777], ![-398165, 1193551, -706668], ![-2475295, 1989242, 1370218]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![789, -189, -1]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![789, -189, -1]] 
 ![![89, 0, 0], ![72, 1, 0], ![21, 0, 1]] where
  M :=![![![789, -189, -1], ![-76, 615, -756], ![-14345, 2816, 804]]]
  hmulB := by decide  
  f := ![![![2623356, 149140, 143499]], ![![2244804, 127619, 122792]], ![![715715, 40689, 39150]]]
  g := ![![![162, -189, -1], ![-320, 615, -756], ![-2629, 2816, 804]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-126916709632106021, -7215321803479075, -6942413133601151]] ![![848563, -176667, -34777]]
  ![![2623356, 149140, 143499]] where
 M := ![![![2623356, 149140, 143499]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![2623356, 149140, 143499]] ![![789, -189, -1]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [25, 84, 85, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 64, 84], [77, 32, 13], [0, 1]]
 g := ![![[22, 11, 25], [73, 53], [44, 35], [71, 96], [3, 47], [1]], ![[75, 93, 63, 69], [36, 88], [57, 4], [85, 11], [41, 53], [81, 61, 70, 34]], ![[68, 21, 95, 57], [47, 85], [84, 86], [56, 31], [90, 22], [44, 23, 5, 63]]]
 h' := ![![[32, 64, 84], [21, 58, 92], [10, 12, 21], [25, 16, 61], [65, 57, 22], [72, 13, 12], [0, 1]], ![[77, 32, 13], [62, 0, 56], [63, 43, 31], [79, 22, 95], [78, 57, 60], [91, 2, 21], [32, 64, 84]], ![[0, 1], [20, 39, 46], [82, 42, 45], [57, 59, 38], [14, 80, 15], [18, 82, 64], [77, 32, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 80], []]
 b := ![[], [53, 76, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [25, 84, 85, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![269369, -56454, 7178]
  a := ![-1, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2777, -582, 74]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [95, 6, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 91, 29], [94, 9, 72], [0, 1]]
 g := ![![[92, 77, 92], [28, 43], [23, 38, 5], [23, 76], [92, 85], [1]], ![[29, 59, 22, 35], [90, 79], [11, 31, 41, 94], [83, 77], [25, 54], [94, 68, 21, 48]], ![[8, 21, 12, 98], [90, 5], [17, 99, 79, 73], [41, 80], [48, 71], [76, 70, 82, 53]]]
 h' := ![![[47, 91, 29], [22, 55, 71], [37, 20, 89], [58, 79, 45], [83, 88, 50], [6, 95, 40], [0, 1]], ![[94, 9, 72], [87, 77, 12], [70, 71, 68], [77, 37, 70], [36, 95, 73], [54, 32, 85], [47, 91, 29]], ![[0, 1], [68, 70, 18], [29, 10, 45], [20, 86, 87], [28, 19, 79], [12, 75, 77], [94, 9, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 35], []]
 b := ![[], [12, 92, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [95, 6, 61, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11817, -1919, -2727]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-117, -19, -27]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7495, 426, 410]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![7495, 426, 410]] 
 ![![103, 0, 0], ![0, 103, 0], ![12, 96, 1]] where
  M :=![![![7495, 426, 410], ![31160, 1771, 1704], ![24586, 1400, 1345]]]
  hmulB := by decide  
  f := ![![![-35, 10, -2]], ![![-152, 5, 40]], ![![-138, 4, 37]]]
  g := ![![![25, -378, 410], ![104, -1571, 1704], ![82, -1240, 1345]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [49, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 102], [0, 1]]
 g := ![![[13, 82], [46, 100], [76, 4], [82], [9], [84, 1]], ![[0, 21], [0, 3], [0, 99], [82], [9], [65, 102]]]
 h' := ![![[84, 102], [12, 44], [87, 10], [65, 101], [90, 59], [4, 3], [0, 1]], ![[0, 1], [0, 59], [0, 93], [0, 2], [102, 44], [50, 100], [84, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [8, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [49, 19, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1266, 961, -1388]
  a := ![1, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![174, 1303, -1388]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, 10, -2]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-35, 10, -2]] 
 ![![103, 0, 0], ![28, 1, 0], ![3, 0, 1]] where
  M :=![![![-35, 10, -2], ![-152, 5, 40], ![798, -188, -5]]]
  hmulB := by decide  
  f := ![![![7495, 426, 410]], ![![2340, 133, 128]], ![![457, 26, 25]]]
  g := ![![![-3, 10, -2], ![-4, 5, 40], ![59, -188, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![7495, 426, 410]] ![![-35, 10, -2]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-195332516, -11104818, -10684795]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-195332516, -11104818, -10684795]] 
 ![![107, 0, 0], ![26, 1, 0], ![92, 0, 1]] where
  M :=![![![-195332516, -11104818, -10684795], ![-812044420, -46165409, -44419272], ![-640955063, -36438835, -35060591]]]
  hmulB := by decide  
  f := ![![![-68599, 13613, 3659]], ![![-14070, 2281, 1398]], ![![-49963, 10446, 1992]]]
  g := ![![![10059756, -11104818, -10684795], ![41820834, -46165409, -44419272], ![33009617, -36438835, -35060591]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-112360378, 27311068, -359097]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-112360378, 27311068, -359097]] 
 ![![107, 0, 0], ![54, 1, 0], ![60, 0, 1]] where
  M :=![![![-112360378, 27311068, -359097], ![-27291372, -79662855, 109244272], ![2082464011, -416488863, -106973923]]]
  hmulB := by decide  
  f := ![![![-54020870751272901, -3071131986516475, -2954971048960561]], ![![-29361727292427470, -1669238918460473, -1606102472803142]], ![![-31948727346928743, -1816312049752262, -1747612784621478]]]
  g := ![![![-14631890, 27311068, -359097], ![-21309846, -79662855, 109244272], ![289638299, -416488863, -106973923]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-195332516, -11104818, -10684795]] ![![-195332516, -11104818, -10684795]]
  ![![54020870751272901, 3071131986516475, 2954971048960561]] where
 M := ![![![54020870751272901, 3071131986516475, 2954971048960561]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI107N1 : IdealMulLeCertificate' Table 
  ![![54020870751272901, 3071131986516475, 2954971048960561]] ![![-112360378, 27311068, -359097]]
  ![![107, 0, 0]] where
 M := ![![![-107, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54004859431579020581732, -3070221729510722114014, -2954095221053807870409]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-54004859431579020581732, -3070221729510722114014, -2954095221053807870409]] 
 ![![109, 0, 0], ![0, 109, 0], ![71, 54, 1]] where
  M :=![![![-54004859431579020581732, -3070221729510722114014, -2954095221053807870409], ![-224511236800089398151084, -12763652845282624639611, -12280886918042888456056], ![-177209042242792531127293, -10074483257361517827561, -9693431115771902525597]]]
  hmulB := by decide  
  f := ![![![83832170061, -11925771799, -10438941265]], ![![-793359536140, 228490517237, -47703087196]], ![![-344929813302, 105250502991, -28226745407]]]
  g := ![![![1428769736360012277223, 1435329543187109200808, -2954095221053807870409], ![5939740682394088827788, 5967011382835168366857, -12280886918042888456056], ![4688298779605619708166, 4709823825635974482153, -9693431115771902525597]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [24, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 108], [0, 1]]
 g := ![![[66, 48], [20], [75, 21], [64, 3], [104], [51, 1]], ![[7, 61], [20], [56, 88], [108, 106], [104], [102, 108]]]
 h' := ![![[51, 108], [40, 22], [53, 42], [99, 28], [91, 60], [84, 70], [0, 1]], ![[0, 1], [72, 87], [15, 67], [1, 81], [99, 49], [57, 39], [51, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [29, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [24, 58, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1221, 399, -1125]
  a := ![0, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![744, 561, -1125]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-83832170061, 11925771799, 10438941265]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-83832170061, 11925771799, 10438941265]] 
 ![![109, 0, 0], ![2, 1, 0], ![53, 0, 1]] where
  M :=![![![-83832170061, 11925771799, 10438941265], ![793359536140, -228490517237, 47703087196], ![708018772689, 19453307050, -240416289036]]]
  hmulB := by decide  
  f := ![![![54004859431579020581732, 3070221729510722114014, 2954095221053807870409]], ![![3050650969387591186372, 173432076186275861171, 166872269359178937586]], ![![27885014606573216715221, 1585286558912199907067, 1525325484693795593186]]]
  g := ![![![-6063739456, 11925771799, 10438941265], ![-11724064686, -228490517237, 47703087196], ![123038307133, 19453307050, -240416289036]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-54004859431579020581732, -3070221729510722114014, -2954095221053807870409]] ![![-83832170061, 11925771799, 10438941265]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [96, 64, 112, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 110, 21], [90, 2, 92], [0, 1]]
 g := ![![[28, 32, 81], [111, 14], [83, 44], [58, 53], [97, 99, 1], [1]], ![[97, 19, 54, 19], [34, 44], [77, 31], [44, 30], [67, 107, 64, 48], [18, 76, 94, 108]], ![[88, 8, 54, 90], [26, 4], [29, 53], [40, 61], [43, 0, 45, 21], [88, 13, 52, 5]]]
 h' := ![![[24, 110, 21], [51, 104, 9], [57, 77, 63], [51, 102, 65], [67, 58, 77], [17, 49, 1], [0, 1]], ![[90, 2, 92], [104, 24, 55], [59, 87, 48], [85, 49, 12], [44, 64, 16], [5, 41, 14], [24, 110, 21]], ![[0, 1], [89, 98, 49], [41, 62, 2], [0, 75, 36], [87, 104, 20], [64, 23, 98], [90, 2, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 9], []]
 b := ![[], [13, 47, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [96, 64, 112, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![153561237, -71179265, 53148872]
  a := ![1, 20, 61]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1358949, -629905, 470344]
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



lemma PB124I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 123 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 123 (by omega)

def PB124I2 : PrimesBelowBoundCertificateInterval O 79 123 124 where
  m := 8
  g := ![1, 3, 1, 1, 2, 3, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB124I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
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
    · exact ![89, 89, 89]
    · exact ![912673]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![1442897]
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
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
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
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
  β := ![I89N0, I89N1, I89N2, I103N1, I107N0, I107N1, I109N1]
  Il := ![[], [I89N0, I89N1, I89N2], [], [], [I103N1], [I107N0, I107N0, I107N1], [I109N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
