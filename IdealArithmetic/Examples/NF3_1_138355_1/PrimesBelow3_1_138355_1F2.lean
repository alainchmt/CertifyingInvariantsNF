
import IdealArithmetic.Examples.NF3_1_138355_1.RI3_1_138355_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17131748901569013261, 4709308009559489544, 1202891236897571764]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![17131748901569013261, 4709308009559489544, 1202891236897571764]] 
 ![![83, 0, 0], ![0, 83, 0], ![57, 41, 1]] where
  M :=![![![17131748901569013261, 4709308009559489544, 1202891236897571764], ![84202386582830023480, 23146205086056872081, 5912199246457061308], ![413853947251994291560, 113763382815115330020, 29058404332513933389]]]
  hmulB := by decide  
  f := ![![![-270663297, -1409209992, 297920996]], ![![20854469720, 1218941683, -1111288996]], ![![9178496637, -181329347, -343056619]]]
  g := ![![![-619675320501115389, -537460634978806660, 1202891236897571764], ![-3045698439340029772, -2641614024321477609, 5912199246457061308], ![-14969579514473492911, -12983508371300673963, 29058404332513933389]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [56, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 82], [0, 1]]
 g := ![![[48, 65], [13, 61], [17], [41], [32, 28], [1]], ![[43, 18], [53, 22], [17], [41], [49, 55], [1]]]
 h' := ![![[51, 82], [19, 56], [30, 12], [22, 73], [34, 46], [27, 51], [0, 1]], ![[0, 1], [53, 27], [61, 71], [10, 10], [56, 37], [55, 32], [51, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [73, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [56, 32, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![266, 53, -23]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19, 12, -23]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-270663297, -1409209992, 297920996]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-270663297, -1409209992, 297920996]] 
 ![![83, 0, 0], ![41, 1, 0], ![62, 0, 1]] where
  M :=![![![-270663297, -1409209992, 297920996], ![20854469720, 1218941683, -1111288996], ![-77790229720, 15298024740, 107652687]]]
  hmulB := by decide  
  f := ![![![17131748901569013261, 4709308009559489544, 1202891236897571764]], ![![9477157729483850207, 2605154620216818595, 665430601918765104]], ![![17783402158424977274, 4888439510937393756, 1248646518315221479]]]
  g := ![![![470311381, -1409209992, 297920996], ![479250343, 1218941683, -1111288996], ![-8574502538, 15298024740, 107652687]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![17131748901569013261, 4709308009559489544, 1202891236897571764]] ![![-270663297, -1409209992, 297920996]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [76, 87, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 63, 31], [57, 25, 58], [0, 1]]
 g := ![![[32, 0, 49], [42, 84], [0, 40], [9, 35, 25], [74, 28, 1], []], ![[65, 27, 49, 33], [42, 25], [48, 42], [4, 33, 18, 23], [32, 14, 17, 62], [20, 71]], ![[0, 48, 44, 63], [41, 72], [79, 25], [76, 14, 9, 13], [27, 23, 31, 48], [82, 71]]]
 h' := ![![[60, 63, 31], [34, 80, 7], [72, 27, 66], [28, 50, 60], [72, 67, 5], [0, 0, 1], [0, 1]], ![[57, 25, 58], [81, 87, 74], [43, 48, 84], [24, 21, 24], [74, 22, 66], [33, 68, 25], [60, 63, 31]], ![[0, 1], [0, 11, 8], [88, 14, 28], [29, 18, 5], [12, 0, 18], [43, 21, 63], [57, 25, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 35], []]
 b := ![[], [60, 51, 85], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [76, 87, 61, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![120239, 55269, 3293]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1351, 621, 37]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [57, 83, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 68, 4], [33, 28, 93], [0, 1]]
 g := ![![[79, 25, 8], [66, 62], [95, 36], [74, 61], [40, 64], [1]], ![[11, 89, 15, 1], [94, 81], [78, 11], [10, 25], [26, 94], [17, 2, 36, 64]], ![[23, 8, 78, 49], [18, 43], [30, 6], [45, 27], [25, 33], [90, 3, 13, 33]]]
 h' := ![![[56, 68, 4], [22, 83, 28], [96, 60, 16], [51, 40, 6], [96, 69, 35], [40, 14, 89], [0, 1]], ![[33, 28, 93], [66, 50, 49], [63, 52, 9], [85, 94, 37], [48, 76, 92], [47, 56, 26], [56, 68, 4]], ![[0, 1], [47, 61, 20], [54, 82, 72], [55, 60, 54], [96, 49, 67], [58, 27, 79], [33, 28, 93]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92, 1], []]
 b := ![[], [64, 58, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [57, 83, 8, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-226301, -1358, -12222]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2333, -14, -126]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8514737241, 16922728892, -3795557614]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![8514737241, 16922728892, -3795557614]] 
 ![![101, 0, 0], ![0, 101, 0], ![67, 92, 1]] where
  M :=![![![8514737241, 16922728892, -3795557614], ![-265689032980, -10463050829, 13127171278], ![918901989460, -200053176590, 2664120449]]]
  hmulB := by decide  
  f := ![![![-25725321644875689899, -7071575935811888552, -1806281667492704970]], ![![-126439716724489347900, -34756729982339214749, -8877857603304593522]], ![![-138391094268227849273, -38042017334808085202, -9717013453580966785]]]
  g := ![![![2602149479, 3624891380, -3795557614], ![-11338708006, -12061017905, 13127171278], ![7330751677, -4407448098, 2664120449]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [44, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 100], [0, 1]]
 g := ![![[65, 52], [9], [4, 85], [47], [92], [69, 1]], ![[17, 49], [9], [11, 16], [47], [92], [37, 100]]]
 h' := ![![[69, 100], [78, 70], [26, 3], [29, 40], [28, 42], [95, 71], [0, 1]], ![[0, 1], [60, 31], [31, 98], [62, 61], [98, 59], [45, 30], [69, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [80, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [44, 32, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![287, 679, -53]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38, 55, -53]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25725321644875689899, -7071575935811888552, -1806281667492704970]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-25725321644875689899, -7071575935811888552, -1806281667492704970]] 
 ![![101, 0, 0], ![8, 1, 0], ![37, 0, 1]] where
  M :=![![![-25725321644875689899, -7071575935811888552, -1806281667492704970], ![-126439716724489347900, -34756729982339214749, -8877857603304593522], ![-621450032231321546540, -170829004741012315510, -43634587585643808271]]]
  hmulB := by decide  
  f := ![![![8514737241, 16922728892, -3795557614]], ![![-1956149852, 1236819607, -170666234]], ![![12217299677, 4218691014, -1364074369]]]
  g := ![![![967125817216331707, -7071575935811888552, -1806281667492704970], ![4753414400559349806, -34756729982339214749, -8877857603304593522], ![23362987587778196867, -170829004741012315510, -43634587585643808271]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![8514737241, 16922728892, -3795557614]] ![![-25725321644875689899, -7071575935811888552, -1806281667492704970]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1857, 384, -155]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![1857, 384, -155]] 
 ![![103, 0, 0], ![0, 103, 0], ![97, 56, 1]] where
  M :=![![![1857, 384, -155], ![-10850, 1082, 229], ![16030, -9705, 1311]]]
  hmulB := by decide  
  f := ![![![35349, 9717, 2482]], ![![173740, 47759, 12199]], ![![136041, 37396, 9552]]]
  g := ![![![164, 88, -155], ![-321, -114, 229], ![-1079, -807, 1311]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [57, 2, 1] where
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
 g := ![![[94, 1], [93, 19], [66, 14], [93], [28], [101, 1]], ![[92, 102], [55, 84], [38, 89], [93], [28], [99, 102]]]
 h' := ![![[101, 102], [55, 102], [49, 15], [11, 23], [70, 14], [11, 50], [0, 1]], ![[0, 1], [57, 1], [19, 88], [68, 80], [42, 89], [14, 53], [101, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [23, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [57, 2, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![267, 83, 7]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, -3, 7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35349, 9717, 2482]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![35349, 9717, 2482]] 
 ![![103, 0, 0], ![46, 1, 0], ![47, 0, 1]] where
  M :=![![![35349, 9717, 2482], ![173740, 47759, 12199], ![853930, 234735, 59958]]]
  hmulB := by decide  
  f := ![![![1857, 384, -155]], ![![724, 182, -67]], ![![1003, 81, -58]]]
  g := ![![![-5129, 9717, 2482], ![-25209, 47759, 12199], ![-123902, 234735, 59958]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![1857, 384, -155]] ![![35349, 9717, 2482]]
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


lemma PB106I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 105 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 105 (by omega)

def PB106I2 : PrimesBelowBoundCertificateInterval O 79 105 106 where
  m := 5
  g := ![2, 1, 1, 2, 2]
  P := ![83, 89, 97, 101, 103]
  hP := PB106I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![704969]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![10609, 103]
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
  β := ![I83N1, I101N1, I103N1]
  Il := ![[I83N1], [], [], [I101N1], [I103N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
