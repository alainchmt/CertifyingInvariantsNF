
import IdealArithmetic.Examples.NF3_1_863379_1.RI3_1_863379_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [69, 35, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 32, 82], [43, 50, 1], [0, 1]]
 g := ![![[58, 16, 29], [10, 38, 33], [77, 61], [63, 37], [9, 25, 1], []], ![[35, 8, 12, 32], [9, 34, 4, 2], [24, 78], [58, 41], [66, 19, 29, 73], [44, 1]], ![[8, 19, 16, 37], [15, 55, 47, 51], [18, 51], [67, 75], [3, 40, 22, 28], [42, 1]]]
 h' := ![![[65, 32, 82], [57, 1, 19], [63, 65, 38], [75, 78, 12], [43, 35, 28], [0, 0, 1], [0, 1]], ![[43, 50, 1], [54, 29, 36], [2, 82, 9], [74, 74, 24], [3, 6, 37], [27, 61, 50], [65, 32, 82]], ![[0, 1], [6, 53, 28], [14, 19, 36], [54, 14, 47], [64, 42, 18], [30, 22, 32], [43, 50, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 70], []]
 b := ![[], [40, 78, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [69, 35, 58, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17181, 166, -6142]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![207, 2, -74]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [85, 38, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 32, 69], [5, 56, 20], [0, 1]]
 g := ![![[6, 57, 80], [39, 50], [38, 67], [46, 56, 72], [2, 29, 1], []], ![[62, 0, 68, 72], [], [28, 50], [17, 81, 50, 25], [17, 25, 48, 25], [85, 44]], ![[8, 0, 0, 39], [44, 50], [78, 64], [68, 35, 86, 55], [64, 49, 43, 10], [45, 44]]]
 h' := ![![[24, 32, 69], [78, 22, 76], [10, 83, 36], [6, 53, 45], [8, 40, 28], [0, 0, 1], [0, 1]], ![[5, 56, 20], [1, 57, 78], [1, 73], [45, 47, 36], [5, 72, 56], [26, 84, 56], [24, 32, 69]], ![[0, 1], [15, 10, 24], [62, 22, 53], [62, 78, 8], [74, 66, 5], [27, 5, 32], [5, 56, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 77], []]
 b := ![[], [39, 80, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [85, 38, 60, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![440461, -340069, 44055]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4949, -3821, 495]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [12, 64, 84, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 61, 15], [90, 35, 82], [0, 1]]
 g := ![![[63, 80, 50], [77, 44], [51, 89], [71, 36], [48, 72], [1]], ![[3, 64, 43, 90], [32, 64], [20, 16], [83, 65], [49, 12], [76, 6, 78, 77]], ![[56, 24, 56, 26], [83, 31], [89, 27], [60, 61], [26, 49], [7, 85, 23, 20]]]
 h' := ![![[20, 61, 15], [3, 11, 27], [65, 4, 23], [17, 2, 63], [53, 25, 91], [85, 33, 13], [0, 1]], ![[90, 35, 82], [93, 89, 43], [63, 50, 89], [77, 25, 4], [43, 70, 68], [7, 73, 77], [20, 61, 15]], ![[0, 1], [96, 94, 27], [92, 43, 82], [44, 70, 30], [45, 2, 35], [58, 88, 7], [90, 35, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 29], []]
 b := ![[], [87, 56, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [12, 64, 84, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![74302, -1649, 1649]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![766, -17, 17]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, 58, -6]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-79, 58, -6]] 
 ![![101, 0, 0], ![47, 1, 0], ![13, 0, 1]] where
  M :=![![![-79, 58, -6], ![-558, 245, 58], ![5394, -3690, 245]]]
  hmulB := by decide  
  f := ![![![274045, 7930, 4834]], ![![131977, 3819, 2328]], ![![42575, 1232, 751]]]
  g := ![![![-27, 58, -6], ![-127, 245, 58], ![1739, -3690, 245]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9959791294500945698633, 288205903922890771774, 175685161120100069530]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![9959791294500945698633, 288205903922890771774, 175685161120100069530]] 
 ![![101, 0, 0], ![75, 1, 0], ![31, 0, 1]] where
  M :=![![![9959791294500945698633, 288205903922890771774, 175685161120100069530], ![16338719984169306466290, 472792594015541944013, 288205903922890771774], ![26803149064828841774982, 775601172333204790494, 472792594015541944013]]]
  hmulB := by decide  
  f := ![![![-98412172187, 32614358758, 16687883186]], ![![-57712275027, 14321970719, 12714906908]], ![![-174673003, 7939038464, -4774588965]]]
  g := ![![![-169325658360781825147, 288205903922890771774, 175685161120100069530], ![-277773342461445081779, 472792594015541944013, 288205903922890771774], ![-455678309649933839371, 775601172333204790494, 472792594015541944013]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-400041379, 242283124, 960056]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-400041379, 242283124, 960056]] 
 ![![101, 0, 0], ![80, 1, 0], ![64, 0, 1]] where
  M :=![![![-400041379, 242283124, 960056], ![89285208, -451884403, 242283124], ![22532330532, -12994003488, -451884403]]]
  hmulB := by decide  
  f := ![![![3352427272014202921, 97008993833039644, 59134946507605944]], ![![2709838928577659272, 78414452150956965, 47800046677638764]], ![![2213635463716650236, 64055841223146032, 39047294426636261]]]
  g := ![![![-196476583, 242283124, 960056], ![205286312, -451884403, 242283124], ![10801714964, -12994003488, -451884403]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-79, 58, -6]] ![![9959791294500945698633, 288205903922890771774, 175685161120100069530]]
  ![![3352427272014202921, 97008993833039644, 59134946507605944]] where
 M := ![![![3352427272014202921, 97008993833039644, 59134946507605944]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![3352427272014202921, 97008993833039644, 59134946507605944]] ![![-400041379, 242283124, 960056]]
  ![![101, 0, 0]] where
 M := ![![![101, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2325541110288016, -1361341014565603, -34299494550984]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![2325541110288016, -1361341014565603, -34299494550984]] 
 ![![103, 0, 0], ![0, 103, 0], ![33, 59, 1]] where
  M :=![![![2325541110288016, -1361341014565603, -34299494550984], ![-3189852993241512, 4177713816041152, -1361341014565603], ![-126604714354601079, 70322561793301050, 4177713816041152]]]
  hmulB := by decide  
  f := ![![![1098895925701804719865581662818, 31798687765569260243821028752, 19383910972887178499004823759]], ![![1802703720478507600407448609587, 52164733165897080919321179832, 31798687765569260243821028752]], ![![1413401582704751896915330276821, 40899519749412436014826763261, 24931615276114177920115738449]]]
  g := ![![![33567227480296, 6430380232451, -34299494550984], ![405188354246829, 820357608499143, -1361341014565603], ![-2567662818290865, -1710316051972106, 4177713816041152]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [16, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 102], [0, 1]]
 g := ![![[13, 58], [74, 25], [60, 81], [58], [41], [101, 1]], ![[0, 45], [24, 78], [1, 22], [58], [41], [99, 102]]]
 h' := ![![[101, 102], [52, 26], [70, 98], [81, 9], [59, 77], [32, 91], [0, 1]], ![[0, 1], [0, 77], [80, 5], [63, 94], [8, 26], [56, 12], [101, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [79, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [16, 2, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-539, 1165, -497]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![154, 296, -497]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1098895925701804719865581662818, 31798687765569260243821028752, 19383910972887178499004823759]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![1098895925701804719865581662818, 31798687765569260243821028752, 19383910972887178499004823759]] 
 ![![103, 0, 0], ![44, 1, 0], ![21, 0, 1]] where
  M :=![![![1098895925701804719865581662818, 31798687765569260243821028752, 19383910972887178499004823759], ![1802703720478507600407448609587, 52164733165897080919321179832, 31798687765569260243821028752], ![2957277962197941202675355673936, 85574581137767547241113056979, 52164733165897080919321179832]]]
  hmulB := by decide  
  f := ![![![2325541110288016, -1361341014565603, -34299494550984]], ![![962465590868264, -540983406066460, -27869114318533]], ![![-755032534354881, 405188354246829, 33567227480296]]]
  g := ![![![-6867072489455082323705290303, 31798687765569260243821028752, 19383910972887178499004823759], ![-11265213416484644904494416571, 52164733165897080919321179832, 31798687765569260243821028752], ![-18480223343181258012032656404, 85574581137767547241113056979, 52164733165897080919321179832]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![2325541110288016, -1361341014565603, -34299494550984]] ![![1098895925701804719865581662818, 31798687765569260243821028752, 19383910972887178499004823759]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [68, 16, 106, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 31, 74], [31, 75, 33], [0, 1]]
 g := ![![[98, 100, 61], [10, 13, 61], [60, 76], [96, 99, 86], [76, 1], [1]], ![[47, 94, 6, 43], [97, 26, 31, 98], [29, 61], [77, 17, 99, 95], [52, 23], [68, 30, 70, 15]], ![[37, 61, 24, 48], [76, 2, 68, 41], [63, 81], [97, 76, 100, 89], [16, 53], [67, 1, 87, 92]]]
 h' := ![![[77, 31, 74], [69, 88, 75], [94, 81, 75], [106, 52, 41], [98, 36, 73], [39, 91, 1], [0, 1]], ![[31, 75, 33], [89, 92, 46], [3, 89, 63], [100, 54, 75], [52, 54, 7], [48, 1, 68], [77, 31, 74]], ![[0, 1], [59, 34, 93], [81, 44, 76], [70, 1, 98], [57, 17, 27], [90, 15, 38], [31, 75, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92, 46], []]
 b := ![[], [48, 23, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [68, 16, 106, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26108, -535, -8667]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![244, -5, -81]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-228477976979649087145725213477216851265183908545, -6611453988825040820645341187304855672482320956, -4030224028913797149715417846727563814015763134]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-228477976979649087145725213477216851265183908545, -6611453988825040820645341187304855672482320956, -4030224028913797149715417846727563814015763134]] 
 ![![109, 0, 0], ![0, 109, 0], ![26, 100, 1]] where
  M :=![![![-228477976979649087145725213477216851265183908545, -6611453988825040820645341187304855672482320956, -4030224028913797149715417846727563814015763134], ![-374810834688983134923533859745663434703465971462, -10845879418304041061092649753928405308332699309, -6611453988825040820645341187304855672482320956], ![-614865220960728796320016730419351577540855848908, -17792319292430930608685435631201228389420639838, -10845879418304041061092649753928405308332699309]]]
  hmulB := by decide  
  f := ![![![87877363719369308135483, -59827785624136838116632, 3815567871612965070830]], ![![354847812060005751587190, -118163301347730805689337, -59827785624136838116632]], ![![295464299079444506654998, -89782608488415076606246, -55061808248619059867073]]]
  g := ![![![-1134790387411838176634168343690827450465817129, 3636797696353712606888958197114234181000862316, -4030224028913797149715417846727563814015763134], ![-1861587440179193335658302650236120983659868134, 5966050637286238908288453843821625338898159599, -6611453988825040820645341187304855672482320956], ![-3053874826466272740656952631350578344258767586, 9787115803100671334867702199648066994897699918, -10845879418304041061092649753928405308332699309]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [103, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 108], [0, 1]]
 g := ![![[70, 4], [28], [83, 29], [46, 66], [83], [93, 1]], ![[6, 105], [28], [55, 80], [80, 43], [83], [77, 108]]]
 h' := ![![[93, 108], [88, 2], [62, 30], [58, 47], [13, 34], [13, 44], [0, 1]], ![[0, 1], [56, 107], [18, 79], [69, 62], [14, 75], [72, 65], [93, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [56, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [103, 16, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3654, -1617, 325]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-44, -313, 325]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46215000501899711886031930208665, 1337320793237992529085483874854, 815206822036986160883158750246]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![46215000501899711886031930208665, 1337320793237992529085483874854, 815206822036986160883158750246]] 
 ![![109, 0, 0], ![9, 1, 0], ![28, 0, 1]] where
  M :=![![![46215000501899711886031930208665, 1337320793237992529085483874854, 815206822036986160883158750246], ![75814234449439712962133763772878, 2193832111902459198341357695381, 1337320793237992529085483874854], ![124370833771133305204950000361422, 3598911614588116391517634530762, 2193832111902459198341357695381]]]
  hmulB := by decide  
  f := ![![![-9387940232523587, 7224543304218078, -915484393292410]], ![![-1556252391457857, 963936759112195, -9310240691868]], ![![3752478906253402, -2504386921888662, 132244532046597]]]
  g := ![![![104158920602955657059946149799, 1337320793237992529085483874854, 815206822036986160883158750246], ![170869387446365040024477027693, 2193832111902459198341357695381, 1337320793237992529085483874854], ![280305780794233028694800679944, 3598911614588116391517634530762, 2193832111902459198341357695381]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-228477976979649087145725213477216851265183908545, -6611453988825040820645341187304855672482320956, -4030224028913797149715417846727563814015763134]] ![![46215000501899711886031930208665, 1337320793237992529085483874854, 815206822036986160883158750246]]
  ![![109, 0, 0]] where
 M := ![![![-11561594466308443406500680619917680311822625055416630790179621077228775953790341, -334557189545936068024855718095461777598631964939318038705260306402100910459774, -203940075304603400990606805367499320737538452646167021561911608204310147776548]]]
 hmul := by decide  
 g := ![![![![-106069674002829756022942024035942021209381881242354410919079092451640146365049, -3069332014182899706650052459591392455033320779259798520231745930294503765686, -1871009865179847715510154177683480006766407822441899280384510167012019704372]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2741084976760, -1599245233078, -43689427571]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![2741084976760, -1599245233078, -43689427571]] 
 ![![113, 0, 0], ![0, 113, 0], ![38, 53, 1]] where
  M :=![![![2741084976760, -1599245233078, -43689427571], ![-4063116764103, 5100314065594, -1599245233078], ![-148729806676254, 82296125822109, 5100314065594]]]
  hmulB := by decide  
  f := ![![![1394910535305231145177826, 40364445381618976323461, 24605443517529452667666]], ![![2288306247130239098092938, 66216585358640701123862, 40364445381618976323461]], ![![1575581635929132924900575, 45592514557807899437896, 27792380922571377412731]]]
  g := ![![![38949409066, 6338888745, -43689427571], ![501842496397, 795223994856, -1599245233078], ![-3031342842202, -1663898404021, 5100314065594]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [99, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 112], [0, 1]]
 g := ![![[100, 8], [60], [81], [99], [73, 50], [44, 1]], ![[0, 105], [60], [81], [99], [13, 63], [88, 112]]]
 h' := ![![[44, 112], [81, 11], [91, 88], [55, 104], [5, 72], [51, 29], [0, 1]], ![[0, 1], [0, 102], [8, 25], [111, 9], [9, 41], [84, 84], [44, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [42, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [99, 69, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-527, 618, -112]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![33, 58, -112]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1394910535305231145177826, 40364445381618976323461, 24605443517529452667666]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![1394910535305231145177826, 40364445381618976323461, 24605443517529452667666]] 
 ![![113, 0, 0], ![60, 1, 0], ![16, 0, 1]] where
  M :=![![![1394910535305231145177826, 40364445381618976323461, 24605443517529452667666], ![2288306247130239098092938, 66216585358640701123862, 40364445381618976323461], ![3753893420490564798081873, 108626196522814376626044, 66216585358640701123862]]]
  hmulB := by decide  
  f := ![![![2741084976760, -1599245233078, -43689427571]], ![![1419486564969, -804021238222, -37350538826]], ![![-928074752638, 501842496397, 38949409066]]]
  g := ![![![-12572064459047598910730, 40364445381618976323461, 24605443517529452667666], ![-20624070800832801685966, 66216585358640701123862, 40364445381618976323461], ![-33833130412535832012943, 108626196522814376626044, 66216585358640701123862]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![2741084976760, -1599245233078, -43689427571]] ![![1394910535305231145177826, 40364445381618976323461, 24605443517529452667666]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [35, 111, 89, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 61, 19], [113, 65, 108], [0, 1]]
 g := ![![[111, 85, 113], [37], [113, 91, 31], [49, 125, 69], [29, 81, 47], [1]], ![[16, 112, 73, 99], [59, 108, 98, 37], [4, 80, 126, 71], [124, 84, 27, 113], [116, 119, 46, 107], [112, 110, 61, 1]], ![[47, 77, 66, 97], [118, 23, 90, 90], [43, 124, 39, 90], [44, 61, 94, 75], [79, 18, 38, 67], [90, 118, 126, 126]]]
 h' := ![![[52, 61, 19], [102, 27, 42], [109, 52], [63, 93, 44], [1, 124, 14], [92, 16, 38], [0, 1]], ![[113, 65, 108], [70, 49, 68], [19, 124, 99], [14, 74, 55], [86, 4, 91], [36, 14, 107], [52, 61, 19]], ![[0, 1], [33, 51, 17], [16, 78, 28], [10, 87, 28], [19, 126, 22], [75, 97, 109], [113, 65, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115, 112], []]
 b := ![[], [118, 29, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [35, 111, 89, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42164, -30861, 5207]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![332, -243, 41]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-64, 34, 3]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-64, 34, 3]] 
 ![![131, 0, 0], ![0, 131, 0], ![66, 55, 1]] where
  M :=![![![-64, 34, 3], ![279, -226, 34], ![3162, -1557, -226]]]
  hmulB := by decide  
  f := ![![![-794, -23, -14]], ![![-1302, -38, -23]], ![![-963, -28, -17]]]
  g := ![![![-2, -1, 3], ![-15, -16, 34], ![138, 83, -226]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [46, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 130], [0, 1]]
 g := ![![[90, 94], [91, 84], [125], [129], [5], [84], [1]], ![[0, 37], [5, 47], [125], [129], [5], [84], [1]]]
 h' := ![![[52, 130], [6, 15], [123, 79], [41, 115], [92, 103], [86, 108], [85, 52], [0, 1]], ![[0, 1], [0, 116], [39, 52], [126, 16], [77, 28], [69, 23], [38, 79], [52, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [120, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [46, 79, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3512, 1702, 50]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-52, -8, 50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-794, -23, -14]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-794, -23, -14]] 
 ![![131, 0, 0], ![76, 1, 0], ![119, 0, 1]] where
  M :=![![![-794, -23, -14], ![-1302, -38, -23], ![-2139, -60, -38]]]
  hmulB := by decide  
  f := ![![![-64, 34, 3]], ![![-35, 18, 2]], ![![-34, 19, 1]]]
  g := ![![![20, -23, -14], ![33, -38, -23], ![53, -60, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-64, 34, 3]] ![![-794, -23, -14]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8255, 4120, 556]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-8255, 4120, 556]] 
 ![![137, 0, 0], ![0, 137, 0], ![47, 104, 1]] where
  M :=![![![-8255, 4120, 556], ![51708, -38279, 4120], ![383160, -170772, -38279]]]
  hmulB := by decide  
  f := ![![![15831113, 458104, 279252]], ![![25970436, 751505, 458104]], ![![25456871, 736644, 449045]]]
  g := ![![![-251, -392, 556], ![-1036, -3407, 4120], ![15929, 27812, -38279]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [91, 108, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 136], [0, 1]]
 g := ![![[87, 105], [135], [130], [24, 9], [103], [19], [1]], ![[118, 32], [135], [130], [11, 128], [103], [19], [1]]]
 h' := ![![[29, 136], [27, 67], [16, 51], [8, 33], [108, 134], [113, 68], [46, 29], [0, 1]], ![[0, 1], [52, 70], [125, 86], [6, 104], [21, 3], [30, 69], [65, 108], [29, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [98, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [91, 108, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1478, 67, 81]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17, -61, 81]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15831113, 458104, 279252]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![15831113, 458104, 279252]] 
 ![![137, 0, 0], ![33, 1, 0], ![7, 0, 1]] where
  M :=![![![15831113, 458104, 279252], ![25970436, 751505, 458104], ![42603672, 1232820, 751505]]]
  hmulB := by decide  
  f := ![![![-8255, 4120, 556]], ![![-1611, 713, 164]], ![![2375, -1036, -251]]]
  g := ![![![-9059, 458104, 279252], ![-14861, 751505, 458104], ![-24379, 1232820, 751505]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-8255, 4120, 556]] ![![15831113, 458104, 279252]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB263I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB263I2 : PrimesBelowBoundCertificateInterval O 79 137 263 where
  m := 11
  g := ![1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB263I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
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
    · exact ![704969]
    · exact ![912673]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![17161, 131]
    · exact ![18769, 137]
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
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
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
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I101N0, I101N1, I101N2, I103N1, I109N1, I113N1, I131N1, I137N1]
  Il := ![[], [], [], [I101N0, I101N1, I101N2], [I103N1], [], [I109N1], [I113N1], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
