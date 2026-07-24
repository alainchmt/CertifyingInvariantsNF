
import IdealArithmetic.Examples.NF3_3_376300_1.RI3_3_376300_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![143923022, 217032905, -124972060]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![143923022, 217032905, -124972060]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![143923022, 217032905, -124972060], ![-1749608840, -2638373513, 1519230335], ![3288404790, 4958845600, -2855406418]]]
  hmulB := by decide  
  f := ![![![-130434, -248290, -126395]], ![![-884765, -1706102, -869015]], ![![-1611635, -3105875, -1581957]]]
  g := ![![![71961511, 217032905, -124972060], ![-874804420, -2638373513, 1519230335], ![1644202395, 4958845600, -2855406418]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1690528161135, 3266225754607, 1695229318513]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![1690528161135, 3266225754607, 1695229318513]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![1690528161135, 3266225754607, 1695229318513], ![23733210459182, 45642257560054, 22863580282249], ![42336701927472, 81779876747594, 42376031805447]]]
  hmulB := by decide  
  f := ![![![-64356980546208431995155232, -225958265904551344463393, 2696478418518698519408559]], ![![-13303141343473326361717703, -46707516784385109138301, 557385278593419554082404]], ![![-4278186279850557930652310, -15020772335917614152157, 179250749120166235325092]]]
  g := ![![![-787848796736, 3266225754607, 1695229318513], ![-10954523550436, 45642257560054, 22863580282249], ![-19721587410061, 81779876747594, 42376031805447]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![143923022, 217032905, -124972060]] ![![143923022, 217032905, -124972060]]
  ![![-769967573617435116, -1161094986294342355, 668582638623088935]] where
 M := ![![![-769967573617435116, -1161094986294342355, 668582638623088935]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-769967573617435116, -1161094986294342355, 668582638623088935]] ![![1690528161135, 3266225754607, 1695229318513]]
  ![![2, 0, 0]] where
 M := ![![![-552579653917282299807940947950, -833278553117877723414199594192, 479819119303603098973687970042]]]
 hmul := by decide  
 g := ![![![![-276289826958641149903970473975, -416639276558938861707099797096, 239909559651801549486843985021]]]]
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


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [2, 2, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1, 1], [0, 1, 2], [0, 1]]
 g := ![![[1]], ![[2, 2, 1, 1]], ![[0, 1, 2, 2]]]
 h' := ![![[1, 1, 1], [0, 1]], ![[0, 1, 2], [1, 1, 1]], ![[0, 1], [0, 1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 2], []]
 b := ![[], [1, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [2, 2, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-296766, -799080, -1293396]
  a := ![0, -2, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-98922, -266360, -431132]
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


def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46228229, 69532594, -40929177]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![46228229, 69532594, -40929177]] 
 ![![5, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![46228229, 69532594, -40929177], ![-573008478, -866539425, 486728158], ![1055314670, 1586923902, -936072019]]]
  hmulB := by decide  
  f := ![![![38742761396216559, 136026381398632, -1623274104721373]], ![![18700489344510091, 65657681699627, -783527528874739]], ![![32024392626777966, 112438093943790, -1341782707196377]]]
  g := ![![![269431, 69532594, -40929177], ![15939433, -866539425, 486728158], ![7766208, 1586923902, -936072019]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![46228229, 69532594, -40929177]] ![![46228229, 69532594, -40929177]]
  ![![-80898877621982081, -121989854615611078, 70264045381842682]] where
 M := ![![![-80898877621982081, -121989854615611078, 70264045381842682]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-80898877621982081, -121989854615611078, 70264045381842682]] ![![46228229, 69532594, -40929177]]
  ![![5, 0, 0]] where
 M := ![![![140312086949184949717099675, 211587602729359122909887200, -121836979574141839635371945]]]
 hmul := by decide  
 g := ![![![![28062417389836989943419935, 42317520545871824581977440, -24367395914828367927074389]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -4, -2]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-3, -4, -2]] 
 ![![7, 0, 0], ![0, 1, 0], ![5, 0, 1]] where
  M :=![![![-3, -4, -2], ![-28, -55, -28], ![-52, -100, -51]]]
  hmulB := by decide  
  f := ![![![-5, 4, -2]], ![![-4, -7, 4]], ![![5, 16, -9]]]
  g := ![![![1, -4, -2], ![16, -55, -28], ![29, -100, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7683, 15794, 8067]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7683, 15794, 8067]] 
 ![![7, 0, 0], ![0, 1, 0], ![6, 0, 1]] where
  M :=![![![7683, 15794, 8067], ![112938, 217085, 110558], ![204982, 395190, 201291]]]
  hmulB := by decide  
  f := ![![![5840715, 8807676, -5071643]], ![![-10143286, -15295863, 8807676]], ![![24070720, 36298142, -20901225]]]
  g := ![![![-5817, 15794, 8067], ![-78630, 217085, 110558], ![-143252, 395190, 201291]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-82873869, -124972060, 71961511]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![-82873869, -124972060, 71961511]] 
 ![![7, 0, 0], ![6, 1, 0], ![4, 0, 1]] where
  M :=![![![-82873869, -124972060, 71961511], ![1007461154, 1519230335, -874804420], ![-1893531862, -2855406418, 1644202395]]]
  hmulB := by decide  
  f := ![![![-884765, -1706102, -869015]], ![![-2496400, -4811977, -2450972]], ![![-3669494, -7072698, -3602455]]]
  g := ![![![54158921, -124972060, 71961511], ![-658386168, 1519230335, -874804420], ![1237442438, -2855406418, 1644202395]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-3, -4, -2]] ![![7683, 15794, 8067]]
  ![![-884765, -1706102, -869015]] where
 M := ![![![-884765, -1706102, -869015]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-884765, -1706102, -869015]] ![![-82873869, -124972060, 71961511]]
  ![![7, 0, 0]] where
 M := ![![![7, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [7, 8, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1, 9], [0, 9, 2], [0, 1]]
 g := ![![[3], [4, 1, 1], []], ![[8, 4, 1, 9], [5, 2, 8, 3], [0, 4]], ![[0, 10, 7, 2], [4, 7, 5, 2], [7, 4]]]
 h' := ![![[1, 1, 9], [5, 5], [0, 0, 1], [0, 1]], ![[0, 9, 2], [10, 5, 1], [1, 7, 9], [1, 1, 9]], ![[0, 1], [5, 1, 10], [6, 4, 1], [0, 9, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 4], []]
 b := ![[], [3, 1, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [7, 8, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![67804, 215303, 439967]
  a := ![-1, 1, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6164, 19573, 39997]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-881, -1334, 768]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-881, -1334, 768]] 
 ![![13, 0, 0], ![0, 13, 0], ![3, 5, 1]] where
  M :=![![![-881, -1334, 768], ![10752, 16217, -9338], ![-20212, -30480, 17551]]]
  hmulB := by decide  
  f := ![![![179, 338, 172]], ![![2408, 4645, 2366]], ![![1305, 2515, 1281]]]
  g := ![![![-245, -398, 768], ![2982, 4839, -9338], ![-5605, -9095, 17551]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [4, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 12], [0, 1]]
 g := ![![[8, 10], [10], [7, 1]], ![[0, 3], [10], [1, 12]]]
 h' := ![![[7, 12], [3, 7], [11, 6], [0, 1]], ![[0, 1], [0, 6], [1, 7], [7, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [1, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [4, 6, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3714, 2, 146]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![252, -56, 146]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 338, 172]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![179, 338, 172]] 
 ![![13, 0, 0], ![4, 1, 0], ![12, 0, 1]] where
  M :=![![![179, 338, 172], ![2408, 4645, 2366], ![4388, 8456, 4307]]]
  hmulB := by decide  
  f := ![![![-881, -1334, 768]], ![![556, 837, -482]], ![![-2368, -3576, 2059]]]
  g := ![![![-249, 338, 172], ![-3428, 4645, 2366], ![-6240, 8456, 4307]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-881, -1334, 768]] ![![179, 338, 172]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, -54, -30]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![29, -54, -30]] 
 ![![17, 0, 0], ![0, 17, 0], ![3, 12, 1]] where
  M :=![![![29, -54, -30], ![-420, -745, -378], ![-696, -1356, -691]]]
  hmulB := by decide  
  f := ![![![-131, -198, 114]], ![![1596, 2407, -1386]], ![![927, 1398, -805]]]
  g := ![![![7, 18, -30], ![42, 223, -378], ![81, 408, -691]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [14, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 16], [0, 1]]
 g := ![![[2, 4], [9], [2], [1]], ![[9, 13], [9], [2], [1]]]
 h' := ![![[6, 16], [14, 15], [15, 14], [3, 6], [0, 1]], ![[0, 1], [2, 2], [14, 3], [5, 11], [6, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [15, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [14, 11, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![416, 1868, 5233]
  a := ![1, -2, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-899, -3584, 5233]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 198, -114]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![131, 198, -114]] 
 ![![17, 0, 0], ![1, 1, 0], ![7, 0, 1]] where
  M :=![![![131, 198, -114], ![-1596, -2407, 1386], ![3000, 4524, -2605]]]
  hmulB := by decide  
  f := ![![![-29, 54, 30]], ![![23, 47, 24]], ![![29, 102, 53]]]
  g := ![![![43, 198, -114], ![-523, -2407, 1386], ![983, 4524, -2605]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![29, -54, -30]] ![![131, 198, -114]]
  ![![17, 0, 0]] where
 M := ![![![-17, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6669, -12912, -6578]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-6669, -12912, -6578]] 
 ![![19, 0, 0], ![4, 1, 0], ![8, 0, 1]] where
  M :=![![![-6669, -12912, -6578], ![-92092, -177453, -90384], ![-167612, -323044, -164541]]]
  hmulB := by decide  
  f := ![![![285177, 430040, -247626]], ![![-122424, -184613, 106304]], ![![463012, 698212, -402045]]]
  g := ![![![5137, -12912, -6578], ![70568, -177453, -90384], ![128468, -323044, -164541]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![791, 1548, 789]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![791, 1548, 789]] 
 ![![19, 0, 0], ![15, 1, 0], ![1, 0, 1]] where
  M :=![![![791, 1548, 789], ![11046, 21275, 10836], ![20094, 38730, 19727]]]
  hmulB := by decide  
  f := ![![![-13645, -20574, 11847]], ![![-2043, -3079, 1773]], ![![-17125, -25824, 14870]]]
  g := ![![![-1222, 1548, 789], ![-16785, 21275, 10836], ![-30557, 38730, 19727]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1236085, -3883104, -7835001]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-1236085, -3883104, -7835001]] 
 ![![19, 0, 0], ![18, 1, 0], ![0, 0, 1]] where
  M :=![![![-1236085, -3883104, -7835001], ![-109690014, -193159213, -27181728], ![-38693454, -108864498, -189276109]]]
  hmulB := by decide  
  f := ![![![-33601299080649673, -117974634732162, 1407853150290501]], ![![-30795444176190900, -108123238609933, 1290291276952836]], ![![-235123746675330, -825522788994, 9851396122229]]]
  g := ![![![3613673, -3883104, -7835001], ![177219780, -193159213, -27181728], ![101098290, -108864498, -189276109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-6669, -12912, -6578]] ![![791, 1548, 789]]
  ![![-280079463, -539792352, -274940479]] where
 M := ![![![-280079463, -539792352, -274940479]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![-280079463, -539792352, -274940479]] ![![-1236085, -3883104, -7835001]]
  ![![19, 0, 0]] where
 M := ![![![70194429447919749, 135284700805046670, 68906575832944930]]]
 hmul := by decide  
 g := ![![![![3694443655153671, 7120247410791930, 3626661885944470]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2990257, 3206656, 36639056]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-2990257, 3206656, 36639056]] 
 ![![23, 0, 0], ![0, 23, 0], ![18, 18, 1]] where
  M :=![![![-2990257, 3206656, 36639056], ![512946784, 879553743, 22446592], ![-28384928, 150237856, 876347087]]]
  hmulB := by decide  
  f := ![![![-33366175333974343, -117149111943168, 1398001754168272]], ![![19572024558355808, 68717654121017, -820043783602176]], ![![-10988295871159762, -38580061699922, 460396097228431]]]
  g := ![![![-28804055, -28534624, 36639056], ![4735136, 20674569, 22446592], ![-687070978, -679304770, 876347087]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [3, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 22], [0, 1]]
 g := ![![[4, 8], [17, 12], [0, 6], [1]], ![[0, 15], [11, 11], [20, 17], [1]]]
 h' := ![![[11, 22], [18, 13], [0, 14], [20, 11], [0, 1]], ![[0, 1], [0, 10], [16, 9], [3, 12], [11, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [2, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [3, 12, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![393, 1566, 3928]
  a := ![0, -2, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3057, -3006, 3928]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-88721167, -170991722, -87093782]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-88721167, -170991722, -87093782]] 
 ![![23, 0, 0], ![12, 1, 0], ![4, 0, 1]] where
  M :=![![![-88721167, -170991722, -87093782], ![-1219312948, -2349963657, -1196942054], ![-2219696544, -4277988892, -2178971935]]]
  hmulB := by decide  
  f := ![![![45493302127, 68602947474, -39503003786]], ![![-309670760, -466977025, 268895082]], ![![53105238292, 80081587900, -46112643647]]]
  g := ![![![100502375, -170991722, -87093782], ![1381218224, -2349963657, -1196942054], ![2514437300, -4277988892, -2178971935]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-2990257, 3206656, 36639056]] ![![-88721167, -170991722, -87093782]]
  ![![23, 0, 0]] where
 M := ![![![-84972204068534433, -163765690448214390, -83413223376722810]]]
 hmul := by decide  
 g := ![![![![-3694443655153671, -7120247410791930, -3626661885944470]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [18, 0, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 5, 15], [15, 23, 14], [0, 1]]
 g := ![![[12, 3, 28], [22, 13], [2, 8, 4], [1]], ![[2, 27], [25, 25], [16, 11, 3, 14], [21, 14, 4, 11]], ![[23, 5, 17, 15], [15, 25], [15, 13, 3, 8], [17, 13, 17, 18]]]
 h' := ![![[16, 5, 15], [1, 1, 17], [22, 6, 19], [11, 0, 2], [0, 1]], ![[15, 23, 14], [18, 24], [27, 12, 5], [6, 21, 17], [16, 5, 15]], ![[0, 1], [25, 4, 12], [18, 11, 5], [24, 8, 10], [15, 23, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 21], []]
 b := ![[], [25, 10, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [18, 0, 27, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![261669726, 687308816, 1064256471]
  a := ![1, 20, 121]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9023094, 23700304, 36698499]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![779181381, 1173611442, -682661956]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![779181381, 1173611442, -682661956]] 
 ![![31, 0, 0], ![0, 31, 0], ![28, 20, 1]] where
  M :=![![![779181381, 1173611442, -682661956], ![-9557267384, -14431094121, 8215280094], ![17795884100, 26801350696, -15604705563]]]
  hmulB := by decide  
  f := ![![![-161689414354304829, -567693813049370, 6774587816410488]], ![![94844229429746832, 332999426497513, -3973856691345590]], ![![-85545674269068088, -300352068251484, 3584258653939637]]]
  g := ![![![641732779, 478285502, -682661956], ![-7728551936, -5765699871, 8215280094], ![14668633544, 10932111676, -15604705563]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [26, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 30], [0, 1]]
 g := ![![[22, 2], [11, 7], [20, 8], [17, 1]], ![[25, 29], [6, 24], [1, 23], [3, 30]]]
 h' := ![![[17, 30], [24, 23], [7, 10], [23, 15], [0, 1]], ![[0, 1], [12, 8], [22, 21], [30, 16], [17, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [14, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [26, 14, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![387, 1326, 3064]
  a := ![-1, 2, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2755, -1934, 3064]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-161689414354304829, -567693813049370, 6774587816410488]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-161689414354304829, -567693813049370, 6774587816410488]] 
 ![![31, 0, 0], ![15, 1, 0], ![10, 0, 1]] where
  M :=![![![-161689414354304829, -567693813049370, 6774587816410488], ![94844229429746832, 332999426497513, -3973856691345590], ![-21496889015512156, -75475880363904, 900693239546883]]]
  hmulB := by decide  
  f := ![![![779181381, 1173611442, -682661956]], ![![68724301, 102357339, -65311266]], ![![825409610, 1243144036, -723591133]]]
  g := ![![![-7126447913634489, -567693813049370, 6774587816410488], ![4180251772443227, 332999426497513, -3973856691345590], ![-947473651791046, -75475880363904, 900693239546883]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![779181381, 1173611442, -682661956]] ![![-161689414354304829, -567693813049370, 6774587816410488]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)


lemma PB137I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB137I0 : PrimesBelowBoundCertificateInterval O 1 31 137 where
  m := 11
  g := ![3, 1, 3, 3, 1, 2, 2, 3, 2, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB137I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0]
    · exact ![I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1]
    · exact ![I29N0]
    · exact ![I31N0, I31N1]
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
    · exact ![7, 7, 7]
    · exact ![1331]
    · exact ![169, 13]
    · exact ![289, 17]
    · exact ![19, 19, 19]
    · exact ![529, 23]
    · exact ![24389]
    · exact ![961, 31]
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
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N2
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
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I5N0, I7N0, I7N1, I7N2, I13N1, I17N1, I19N0, I19N1, I19N2, I23N1, I31N1]
  Il := ![[I2N0, I2N0, I2N1], [I3N0], [I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [], [I13N1], [I17N1], [I19N0, I19N1, I19N2], [I23N1], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
