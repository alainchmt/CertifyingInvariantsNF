
import IdealArithmetic.Examples.NF3_1_89240_1.RI3_1_89240_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24, 2, -3]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-24, 2, -3]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-24, 2, -3], ![178, -15, 22], ![-224, 19, -28]]]
  hmulB := by decide  
  f := ![![![-2, 1, 1]], ![![-28, 0, 3]], ![![-11, -4, -2]]]
  g := ![![![-12, 2, -3], ![89, -15, 22], ![-112, 19, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, -5, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-37, -5, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-37, -5, 0], ![-10, -52, -40], ![290, 5, -27]]]
  hmulB := by decide  
  f := ![![![1604, -135, 200]], ![![-5133, 432, -640]], ![![8317, -700, 1037]]]
  g := ![![![-16, -5, 0], ![41, -52, -40], ![156, 5, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-24, 2, -3]] ![![-24, 2, -3]]
  ![![1604, -135, 200]] where
 M := ![![![1604, -135, 200]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![1604, -135, 200]] ![![-37, -5, 0]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [1, 0, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 0, 1], [2, 2, 2], [0, 1]]
 g := ![![[1]], ![[0, 1, 1, 1]], ![[2, 2, 2, 2]]]
 h' := ![![[2, 0, 1], [0, 1]], ![[2, 2, 2], [2, 0, 1]], ![[0, 1], [2, 2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 2], []]
 b := ![[], [1, 1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [1, 0, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-704604, 15525, 37260]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-234868, 5175, 12420]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 27 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def PBC3 : ContainsPrimesAboveP 3 ![I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![3, 0, 0]]) timesTableT_eq_Table B_one_repr 3 (by decide) 𝕀


def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1659913, 290840, 52542]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![1659913, 290840, 52542]] 
 ![![5, 0, 0], ![0, 1, 0], ![4, 0, 1]] where
  M :=![![![1659913, 290840, 52542], ![-2465756, 2479891, 2221636], ![-14977208, -658634, 1078233]]]
  hmulB := by decide  
  f := ![![![-4137145317827, 348199233348, -515842181318]], ![![6123048996628, -515341087293, 763455645884]], ![![-11062891066588, 931098593854, -1379382501959]]]
  g := ![![![289949, 290840, 52542], ![-2270460, 2479891, 2221636], ![-3858028, -658634, 1078233]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-485553, 104193, 134105]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-485553, 104193, 134105]] 
 ![![5, 0, 0], ![4, 1, 0], ![3, 0, 1]] where
  M :=![![![-485553, 104193, 134105], ![-7569704, -307079, 565334], ![-1215414, -1042928, -693939]]]
  hmulB := by decide  
  f := ![![![802696752133, -67558273213, 100084674757]], ![![-545848134760, 45940832977, -68059367238]], ![![1985903678801, -167141853945, 247613464566]]]
  g := ![![![-260928, 104193, 134105], ![-1607478, -307079, 565334], ![1007623, -1042928, -693939]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![1659913, 290840, 52542]] ![![1659913, 290840, 52542]]
  ![![1251238229793, 1169414647732, 790008281372]] where
 M := ![![![1251238229793, 1169414647732, 790008281372]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![1251238229793, 1169414647732, 790008281372]] ![![-485553, 104193, 134105]]
  ![![5, 0, 0]] where
 M := ![![![-10419852338081659865, -1052654172608809995, 280689606500308445]]]
 hmul := by decide  
 g := ![![![![-2083970467616331973, -210530834521761999, 56137921300061689]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41676403063, -3507658175, 5196444653]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![41676403063, -3507658175, 5196444653]] 
 ![![7, 0, 0], ![0, 7, 0], ![1, 0, 1]] where
  M :=![![![41676403063, -3507658175, 5196444653], ![-308409106224, 25956983885, -38454154706], ![390516181658, -32867454396, 48691719413]]]
  hmulB := by decide  
  f := ![![![-161153, 15241, 29235]], ![![-1665148, -144665, 63458]], ![![1047, -29235, -23200]]]
  g := ![![![5211422630, -501094025, 5196444653], ![-38564993074, 3708140555, -38454154706], ![48832066035, -4695350628, 48691719413]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [3, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 6], [0, 1]]
 g := ![![[5, 4], [6, 1]], ![[1, 3], [5, 6]]]
 h' := ![![[6, 6], [3, 5], [0, 1]], ![[0, 1], [5, 2], [6, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [3, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![845, -581, 5]
  a := ![2, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![120, -83, 5]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-161153, 15241, 29235]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-161153, 15241, 29235]] 
 ![![7, 0, 0], ![2, 1, 0], ![6, 0, 1]] where
  M :=![![![-161153, 15241, 29235], ![-1665148, -144665, 63458], ![168482, -219886, -191635]]]
  hmulB := by decide  
  f := ![![![41676403063, -3507658175, 5196444653]], ![![-32150900014, 2705952505, -4008752200]], ![![91510657148, -7701914778, 11410055333]]]
  g := ![![![-52435, 15241, 29235], ![-250938, -144665, 63458], ![251152, -219886, -191635]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![41676403063, -3507658175, 5196444653]] ![![-161153, 15241, 29235]]
  ![![7, 0, 0]] where
 M := ![![![7, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [10, 0, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 10, 1], [3, 0, 10], [0, 1]]
 g := ![![[1, 7, 1], [5, 4, 1], []], ![[0, 6, 2, 5], [8, 1], [2, 1]], ![[7, 3, 2, 2], [3, 9, 9, 10], [4, 1]]]
 h' := ![![[1, 10, 1], [5, 4, 10], [0, 0, 1], [0, 1]], ![[3, 0, 10], [6, 8, 4], [3, 10], [1, 10, 1]], ![[0, 1], [4, 10, 8], [2, 1, 10], [3, 0, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 1], []]
 b := ![[], [8, 6, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [10, 0, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-37281514006, 1095701288, 2149221492]
  a := ![-129, -193, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3389228546, 99609208, 195383772]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-66678929, 5611974, -8313898]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-66678929, 5611974, -8313898]] 
 ![![13, 0, 0], ![0, 13, 0], ![12, 6, 1]] where
  M :=![![![-66678929, 5611974, -8313898], ![493430032, -41529109, 61523588], ![-624794820, 52585312, -77902877]]]
  hmulB := by decide  
  f := ![![![-549, 1306, 1090]], ![![-60608, 2279, 8268]], ![![-31288, 1570, 4579]]]
  g := ![![![2545219, 4268874, -8313898], ![-18834848, -31590049, 61523588], ![23849208, 40000198, -77902877]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [11, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 12], [0, 1]]
 g := ![![[9, 1], [1], [5, 1]], ![[1, 12], [1], [10, 12]]]
 h' := ![![[5, 12], [11, 12], [10, 1], [0, 1]], ![[0, 1], [6, 1], [2, 12], [5, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [10, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [11, 8, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![80, -1247, -106]
  a := ![-3, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![104, -47, -106]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-549, 1306, 1090]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-549, 1306, 1090]] 
 ![![13, 0, 0], ![6, 1, 0], ![0, 0, 1]] where
  M :=![![![-549, 1306, 1090], ![-60608, 2279, 8268], ![-36508, -8936, -3161]]]
  hmulB := by decide  
  f := ![![![-66678929, 5611974, -8313898]], ![![7181266, -604405, 895400]], ![![-48061140, 4045024, -5992529]]]
  g := ![![![-645, 1306, 1090], ![-5714, 2279, 8268], ![1316, -8936, -3161]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-66678929, 5611974, -8313898]] ![![-549, 1306, 1090]]
  ![![13, 0, 0]] where
 M := ![![![13, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3257, 430, -8]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![3257, 430, -8]] 
 ![![17, 0, 0], ![0, 17, 0], ![3, 10, 1]] where
  M :=![![![3257, 430, -8], ![1324, 4555, 3456], ![-25228, -374, 2397]]]
  hmulB := by decide  
  f := ![![![-718287, 60454, -89560]], ![![5315388, -447365, 662752]], ![![2604031, -219166, 324685]]]
  g := ![![![193, 30, -8], ![-532, -1765, 3456], ![-1907, -1432, 2397]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [11, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 16], [0, 1]]
 g := ![![[], [], [], [1]], ![[], [], [], [1]]]
 h' := ![![[0, 16], [4], [2], [6], [0, 1]], ![[0, 1], [4], [2], [6], [0, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [0, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [11, 0, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1706, -1023, 32]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-106, -79, 32]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-718287, 60454, -89560]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-718287, 60454, -89560]] 
 ![![17, 0, 0], ![7, 1, 0], ![0, 0, 1]] where
  M :=![![![-718287, 60454, -89560], ![5315388, -447365, 662752], ![-6730492, 566466, -839195]]]
  hmulB := by decide  
  f := ![![![3257, 430, -8]], ![![1419, 445, 200]], ![![-1484, -22, 141]]]
  g := ![![![-67145, 60454, -89560], ![496879, -447365, 662752], ![-629162, 566466, -839195]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![3257, 430, -8]] ![![-718287, 60454, -89560]]
  ![![17, 0, 0]] where
 M := ![![![17, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32251, -7601, -2561]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-32251, -7601, -2561]] 
 ![![19, 0, 0], ![0, 19, 0], ![17, 14, 1]] where
  M :=![![![-32251, -7601, -2561], ![133336, -52493, -55686], ![348662, 25528, -17049]]]
  hmulB := by decide  
  f := ![![![-121921335, 10261403, -15201827]], ![![902228772, -75935299, 112494878]], ![![495584893, -41710471, 61792268]]]
  g := ![![![594, 1487, -2561], ![56842, 38269, -55686], ![33605, 13906, -17049]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [17, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 18], [0, 1]]
 g := ![![[18, 9], [16, 9], [4], [1]], ![[0, 10], [17, 10], [4], [1]]]
 h' := ![![[17, 18], [13, 16], [12, 3], [2, 17], [0, 1]], ![[0, 1], [0, 3], [6, 16], [6, 2], [17, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [3, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [17, 2, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-161884, -58055, 3840]
  a := ![23, 44, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11956, -5885, 3840]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-121921335, 10261403, -15201827]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-121921335, 10261403, -15201827]] 
 ![![19, 0, 0], ![4, 1, 0], ![11, 0, 1]] where
  M :=![![![-121921335, 10261403, -15201827], ![902228772, -75935299, 112494878], ![-1142427146, 96151386, -142444141]]]
  hmulB := by decide  
  f := ![![![-32251, -7601, -2561]], ![![228, -4363, -3470]], ![![-321, -3057, -2380]]]
  g := ![![![223850, 10261403, -15201827], ![-1656510, -75935299, 112494878], ![2097519, 96151386, -142444141]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-32251, -7601, -2561]] ![![-121921335, 10261403, -15201827]]
  ![![19, 0, 0]] where
 M := ![![![19, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1367652027, -115107242, 170526426]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![1367652027, -115107242, 170526426]] 
 ![![23, 0, 0], ![0, 1, 0], ![6, 0, 1]] where
  M :=![![![1367652027, -115107242, 170526426], ![-10120747192, 851803875, -1261910788], ![12815171372, -1078577740, 1597866511]]]
  hmulB := by decide  
  f := ![![![-128995, 15422, 25946]], ![![-64088, -4725, 3108]], ![![-31930, -4544, -181]]]
  g := ![![![14977977, -115107242, 170526426], ![-110838368, 851803875, -1261910788], ![140346622, -1078577740, 1597866511]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![220249801, 381645668, 277898292]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![220249801, 381645668, 277898292]] 
 ![![23, 0, 0], ![22, 1, 0], ![12, 0, 1]] where
  M :=![![![220249801, 381645668, 277898292], ![-15354809600, 1087288513, 2497368760], ![-12131110232, -2326933712, -543041535]]]
  hmulB := by decide  
  f := ![![![-5220768735852249665, 439401454785199524, -650954347978611884]], ![![-3314032917235634970, 278922694858971753, -413211970490897456]], ![![-4850820249347765052, 408265062542933824, -604827122659390927]]]
  g := ![![![-500466713, 381645668, 277898292], ![-3010590522, 1087288513, 2497368760], ![1981649124, -2326933712, -543041535]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![1367652027, -115107242, 170526426]] ![![1367652027, -115107242, 170526426]]
  ![![5220768735852249665, -439401454785199524, 650954347978611884]] where
 M := ![![![5220768735852249665, -439401454785199524, 650954347978611884]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI23N1 : IdealMulLeCertificate' Table 
  ![![5220768735852249665, -439401454785199524, 650954347978611884]] ![![220249801, 381645668, 277898292]]
  ![![23, 0, 0]] where
 M := ![![![-23, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-153, -46, -20]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-153, -46, -20]] 
 ![![29, 0, 0], ![8, 1, 0], ![11, 0, 1]] where
  M :=![![![-153, -46, -20], ![1068, -271, -328], ![1948, 186, -61]]]
  hmulB := by decide  
  f := ![![![77539, -6526, 9668]], ![![1604, -135, 200]], ![![54465, -4584, 6791]]]
  g := ![![![15, -46, -20], ![236, -271, -328], ![39, 186, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![165337960225, -13915525458, 20615252186]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![165337960225, -13915525458, 20615252186]] 
 ![![29, 0, 0], ![22, 1, 0], ![4, 0, 1]] where
  M :=![![![165337960225, -13915525458, 20615252186], ![-1223515677704, 102976131665, -152554708036], ![1549249555260, -130391239844, 193169011141]]]
  hmulB := by decide  
  f := ![![![-2306619, -171406, 110798]], ![![-1983266, -231123, 29128]], ![![162200, -44476, -52435]]]
  g := ![![![13414431433, -13915525458, 20615252186], ![-99267991110, 102976131665, -152554708036], ![125695889216, -130391239844, 193169011141]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3387, 416, 690]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-3387, 416, 690]] 
 ![![29, 0, 0], ![27, 1, 0], ![15, 0, 1]] where
  M :=![![![-3387, 416, 690], ![-39188, -2829, 1948], ![712, -5246, -4219]]]
  hmulB := by decide  
  f := ![![![-22154759, 1864636, -2762378]], ![![-14973493, 1260231, -1866978]], ![![-18617789, 1566950, -2321369]]]
  g := ![![![-861, 416, 690], ![275, -2829, 1948], ![7091, -5246, -4219]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-153, -46, -20]] ![![165337960225, -13915525458, 20615252186]]
  ![![22154759, -1864636, 2762378]] where
 M := ![![![22154759, -1864636, 2762378]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![22154759, -1864636, 2762378]] ![![-3387, 416, 690]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4445496839775467, -374151370702590, 554289156097742]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![4445496839775467, -374151370702590, 554289156097742]] 
 ![![31, 0, 0], ![5, 1, 0], ![3, 0, 1]] where
  M :=![![![4445496839775467, -374151370702590, 554289156097742], ![-32897073795074216, 2768753571569955, -4101789277816204], ![41655189120268932, -3505872721981604, 5193799581180647]]]
  hmulB := by decide  
  f := ![![![-328450331, -49162438, -3773250]], ![![-49088001, -23160535, -13052234]], ![![55813981, -2319746, -7788555]]]
  g := ![![![150109233064361, -374151370702590, 554289156097742], ![-1110821736112109, 2768753571569955, -4101789277816204], ![1406553354407581, -3505872721981604, 5193799581180647]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-72496847398918177, 6101634036318818, -9039308273700800]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-72496847398918177, 6101634036318818, -9039308273700800]] 
 ![![31, 0, 0], ![11, 1, 0], ![12, 0, 1]] where
  M :=![![![-72496847398918177, 6101634036318818, -9039308273700800], ![536483147947284036, -45152637016260923, 66891688837952144], ![-679309871959720244, 57173523879586782, -84700115471555813]]]
  hmulB := by decide  
  f := ![![![-954434791, 153636566, 223192608]], ![![-746344543, 31396275, 104446000]], ![![-397716272, 4117870, 45696883]]]
  g := ![![![-1004616855290825, 6101634036318818, -9039308273700800], ![7434254486152531, -45152637016260923, 66891688837952144], ![-9413459644403390, 57173523879586782, -84700115471555813]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52861, 4449, -6591]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-52861, 4449, -6591]] 
 ![![31, 0, 0], ![14, 1, 0], ![17, 0, 1]] where
  M :=![![![-52861, 4449, -6591], ![391176, -32923, 48774], ![-495318, 41688, -61759]]]
  hmulB := by decide  
  f := ![![![-1045, -183, -33]], ![![-422, -133, -60]], ![![-269, -87, -40]]]
  g := ![![![-100, 4449, -6591], ![740, -32923, 48774], ![-937, 41688, -61759]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![4445496839775467, -374151370702590, 554289156097742]] ![![-72496847398918177, 6101634036318818, -9039308273700800]]
  ![![-899544506826310250947812035905947, 75709380158742517910202181974820, -112160188957934045114631851400806]] where
 M := ![![![-899544506826310250947812035905947, 75709380158742517910202181974820, -112160188957934045114631851400806]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-899544506826310250947812035905947, 75709380158742517910202181974820, -112160188957934045114631851400806]] ![![-52861, 4449, -6591]]
  ![![31, 0, 0]] where
 M := ![![![132721475142587824719482760138350878995, -11170387391114888696363174806099357591, 16548448262207767124783778862958345111]]]
 hmul := by decide  
 g := ![![![![4281337907825413700628476133495189645, -360335077132738345043973380841914761, 533820911684121520154315447192204681]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB85I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB85I0 : PrimesBelowBoundCertificateInterval O 1 31 85 where
  m := 11
  g := ![3, 1, 3, 2, 1, 2, 2, 2, 3, 3, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB85I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0]
    · exact ![I5N0, I5N0, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N0, I23N1]
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1, I31N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2]
    · exact ![27]
    · exact ![5, 5, 5]
    · exact ![49, 7]
    · exact ![1331]
    · exact ![169, 13]
    · exact ![289, 17]
    · exact ![361, 19]
    · exact ![23, 23, 23]
    · exact ![29, 29, 29]
    · exact ![31, 31, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I7N0, I7N1, I13N1, I17N1, I19N1, I23N0, I23N1, I29N0, I29N1, I29N2, I31N0, I31N1, I31N2]
  Il := ![[I2N0, I2N0, I2N1], [I3N0], [I5N0, I5N0, I5N1], [I7N0, I7N1], [], [I13N1], [I17N1], [I19N1], [I23N0, I23N0, I23N1], [I29N0, I29N1, I29N2], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
