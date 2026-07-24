
import IdealArithmetic.Examples.NF3_1_516660_1.RI3_1_516660_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1051941771910417, 238059773018136, 87112782948364]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![1051941771910417, 238059773018136, 87112782948364]] 
 ![![83, 0, 0], ![0, 83, 0], ![13, 60, 1]] where
  M :=![![![1051941771910417, 238059773018136, 87112782948364], ![17248331023776072, 3903385033379473, 1428358638108816], ![44261113220294916, 10016515027840092, 3665325260361337]]]
  hmulB := by decide  
  f := ![![![121387763, 853032, -3217412]], ![![-637047576, 25718435, 5118192]], ![![-438189623, 17754360, 3495549]]]
  g := ![![![-970173571305, -60104906070888, 87112782948364], ![-15907605682392, -985519677748789, 1428358638108816], ![-40820664631355, -2528951814383616, 3665325260361337]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [26, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 82], [0, 1]]
 g := ![![[53, 16], [46, 64], [1], [16], [25, 10], [1]], ![[0, 67], [0, 19], [1], [16], [23, 73], [1]]]
 h' := ![![[33, 82], [49, 79], [68, 8], [29, 1], [14, 79], [57, 33], [0, 1]], ![[0, 1], [0, 4], [0, 75], [62, 82], [48, 4], [67, 50], [33, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [80, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [26, 50, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4745, 5217, 3104]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-429, -2181, 3104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-121387763, -853032, 3217412]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-121387763, -853032, 3217412]] 
 ![![83, 0, 0], ![55, 1, 0], ![40, 0, 1]] where
  M :=![![![-121387763, -853032, 3217412], ![637047576, -25718435, -5118192], ![-275074932, 80583636, -24865403]]]
  hmulB := by decide  
  f := ![![![-1051941771910417, -238059773018136, -87112782948364]], ![![-904881066010229, -204779187341891, -74934478316492]], ![![-1040226314418212, -235408505404404, -86142609377059]]]
  g := ![![![-2447801, -853032, 3217412], ![27184207, -25718435, -5118192], ![-44729624, 80583636, -24865403]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![1051941771910417, 238059773018136, 87112782948364]] ![![-121387763, -853032, 3217412]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![18, -13, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![18, -13, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![18, 76, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![18, -13, 1], ![198, 35, -78], ![-2607, -357, 48]]]
  hmulB := by decide  
  f := ![![![-17, 13, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -76, 89]], ![![0, -1, 1], ![18, 67, -78], ![-39, -45, 48]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [50, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 88], [0, 1]]
 g := ![![[9, 73], [10], [18], [42, 4], [19, 25], [1]], ![[0, 16], [10], [18], [22, 85], [72, 64], [1]]]
 h' := ![![[84, 88], [32, 42], [40, 59], [36, 75], [29, 87], [39, 84], [0, 1]], ![[0, 1], [0, 47], [12, 30], [17, 14], [39, 2], [64, 5], [84, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [28, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [50, 5, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1102, 2596, 1950]
  a := ![-1, 1, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-382, -1636, 1950]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-11, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-11, 1, 0]] 
 ![![89, 0, 0], ![78, 1, 0], ![41, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-11, 1, 0], ![0, -10, 6], ![198, 30, -11]]]
  hmulB := by decide  
  f := ![![![12, 719, -432], ![89, 6408, 0]], ![![12, 629, -378], ![90, 5607, 0]], ![![8, 331, -199], ![61, 2952, 0]]]
  g := ![![![1, 0, 0], ![-78, 89, 0], ![-41, 0, 89]], ![![-1, 1, 0], ![6, -10, 6], ![-19, 30, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![18, -13, 1]] ![![89, 0, 0], ![-11, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-979, 89, 0]], ![![1602, -1157, 89], ![0, 178, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-11, 1, 0]]], ![![![18, -13, 1]], ![![0, 2, -1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-112177570610282949700591773508430, -25386354749190498644435810699135, -9289582960947902960760684588471]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-112177570610282949700591773508430, -25386354749190498644435810699135, -9289582960947902960760684588471]] 
 ![![97, 0, 0], ![0, 97, 0], ![70, 85, 1]] where
  M :=![![![-112177570610282949700591773508430, -25386354749190498644435810699135, -9289582960947902960760684588471], ![-1839337426267684786230615548517258, -416251414187910537167848121861695, -152318128495142991866614864194810], ![-4719942002628437933893187927009187, -1068146880186995757038176912393593, -390865059438720038523412311162560]]]
  hmulB := by decide  
  f := ![![![1329520131605290, -2198270850986399, 825056644484835]], ![![163361215607997330, 23882948615163941, -13189625105918394]], ![![139343146784833369, 18942787798539120, -10693638653845100]]]
  g := ![![![5547352955217219150027382965820, 7878641205478157247631158549700, -9289582960947902960760684588471], ![90958057406106439633323968506386, 129183396988651997644272323038115, -152318128495142991866614864194810], ![233408372763731595492223441797629, 331498795588703170283008964293031, -390865059438720038523412311162560]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [67, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 96], [0, 1]]
 g := ![![[10, 1], [9], [88], [47], [2], [9, 1]], ![[19, 96], [9], [88], [47], [2], [18, 96]]]
 h' := ![![[9, 96], [49, 1], [19, 3], [17, 31], [16, 12], [76, 14], [0, 1]], ![[0, 1], [58, 96], [46, 94], [5, 66], [27, 85], [8, 83], [9, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [29, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [67, 88, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1502, 33, 70]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-66, -61, 70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1329520131605290, -2198270850986399, 825056644484835]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![1329520131605290, -2198270850986399, 825056644484835]] 
 ![![97, 0, 0], ![72, 1, 0], ![94, 0, 1]] where
  M :=![![![1329520131605290, -2198270850986399, 825056644484835], ![163361215607997330, 23882948615163941, -13189625105918394], ![-462484497763306557, -38721256261592415, 26081219466150340]]]
  hmulB := by decide  
  f := ![![![-112177570610282949700591773508430, -25386354749190498644435810699135, -9289582960947902960760684588471]], ![![-102228067115546981079105394238394, -23134731506490994222342541156695, -8465650532818474278777156232626]], ![![-157367357113350878409781594193831, -35613033264029924016650959980539, -13031812966678586771493986211122]]]
  g := ![![![845873163103624, -2198270850986399, 825056644484835], ![-3261714687912138, 23882948615163941, -13189625105918394], ![-1300914193265821, -38721256261592415, 26081219466150340]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-112177570610282949700591773508430, -25386354749190498644435810699135, -9289582960947902960760684588471]] ![![1329520131605290, -2198270850986399, 825056644484835]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![1, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![1, 1, 0]] 
 ![![101, 0, 0], ![1, 1, 0], ![67, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![1, 1, 0], ![0, 2, 6], ![198, 30, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![101, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -1], ![67, 17, 0]]]
  g := ![![![1, 0, 0], ![-1, 101, 0], ![-67, 0, 101]], ![![0, 1, 0], ![-4, 2, 6], ![1, 30, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![48, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![48, 1, 0]] 
 ![![101, 0, 0], ![48, 1, 0], ![12, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![48, 1, 0], ![0, 49, 6], ![198, 30, 48]]]
  hmulB := by decide  
  f := ![![![1345, 28, 0], ![-2828, 0, 0]], ![![624, 13, 0], ![-1312, 0, 0]], ![![156, -5, -1], ![-328, 17, 0]]]
  g := ![![![1, 0, 0], ![-48, 101, 0], ![-12, 0, 101]], ![![0, 1, 0], ![-24, 49, 6], ![-18, 30, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, -3, -1]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![-14, -3, -1]] 
 ![![101, 0, 0], ![51, 1, 0], ![63, 0, 1]] where
  M :=![![![-14, -3, -1], ![-198, -47, -18], ![-561, -123, -44]]]
  hmulB := by decide  
  f := ![![![146, 9, -7]], ![![60, 4, -3]], ![![111, 6, -5]]]
  g := ![![![2, -3, -1], ![33, -47, -18], ![84, -123, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![1, 1, 0]] ![![101, 0, 0], ![48, 1, 0]]
  ![![-146, -9, 7]] where
 M := ![![![10201, 0, 0], ![4848, 101, 0]], ![![101, 101, 0], ![48, 50, 6]]]
 hmul := by decide  
 g := ![![![![1414, 303, 101]], ![![870, 191, 66]]], ![![![212, 50, 19]], ![![138, 32, 12]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-146, -9, 7]] ![![-14, -3, -1]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [99, 34, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 25, 71], [96, 77, 32], [0, 1]]
 g := ![![[13, 72, 63], [44, 9, 58], [83, 76, 26], [54, 63], [0, 68], [1]], ![[75, 46, 94, 89], [33, 91, 95, 99], [71, 99, 49, 85], [24, 49], [57, 29], [81, 17, 53, 89]], ![[2, 42, 41, 100], [63, 96, 9, 55], [72, 99, 5, 50], [20, 29], [32, 30], [33, 38, 68, 14]]]
 h' := ![![[52, 25, 71], [73, 99, 75], [23, 52, 77], [60, 64, 51], [16, 0, 28], [4, 69, 45], [0, 1]], ![[96, 77, 32], [2, 90, 32], [7, 5, 42], [8, 40, 25], [85, 16, 96], [28, 88, 21], [52, 25, 71]], ![[0, 1], [67, 17, 99], [10, 46, 87], [5, 102, 27], [50, 87, 82], [98, 49, 37], [96, 77, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 20], []]
 b := ![[], [13, 9, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [99, 34, 58, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17924781, -4864381, -1824954]
  a := ![1, -2, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-174027, -47227, -17718]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-160287627073, -36273905208, -13273644644]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-160287627073, -36273905208, -13273644644]] 
 ![![107, 0, 0], ![0, 107, 0], ![40, 57, 1]] where
  M :=![![![-160287627073, -36273905208, -13273644644], ![-2628181639512, -594770871601, -217643431248], ![-6744202957932, -1526247429492, -558496966393]]]
  hmulB := by decide  
  f := ![![![-1734011, -91272, 76780]], ![![15202440, 478117, -547632]], ![![7257692, 218667, -257705]]]
  g := ![![![3464094941, 6731998500, -13273644644], ![56799585144, 110382287005, -217643431248], ![145753978484, 283253080887, -558496966393]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [75, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 106], [0, 1]]
 g := ![![[105, 10], [19, 12], [4], [15, 30], [99], [43, 1]], ![[0, 97], [0, 95], [4], [21, 77], [99], [86, 106]]]
 h' := ![![[43, 106], [73, 63], [50, 71], [52, 105], [76, 43], [92, 62], [0, 1]], ![[0, 1], [0, 44], [0, 36], [73, 2], [106, 64], [83, 45], [43, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [47, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [75, 64, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4794, 5189, 2950]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1058, -1523, 2950]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1734011, 91272, -76780]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![1734011, 91272, -76780]] 
 ![![107, 0, 0], ![86, 1, 0], ![37, 0, 1]] where
  M :=![![![1734011, 91272, -76780], ![-15202440, -478117, 547632], ![20605596, 204420, -569389]]]
  hmulB := by decide  
  f := ![![![160287627073, 36273905208, 13273644644]], ![![153391752970, 34713333827, 12702587576]], ![![118456496819, 26807307684, 9809549703]]]
  g := ![![![-30603, 91272, -76780], ![52834, -478117, 547632], ![225167, 204420, -569389]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-160287627073, -36273905208, -13273644644]] ![![1734011, 91272, -76780]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-51, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-51, 1, 0]] 
 ![![109, 0, 0], ![58, 1, 0], ![11, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-51, 1, 0], ![0, -50, 6], ![198, 30, -51]]]
  hmulB := by decide  
  f := ![![![3571, -70, 0], ![7630, 0, 0]], ![![1990, -39, 0], ![4252, 0, 0]], ![![395, 34, -5], ![844, 91, 0]]]
  g := ![![![1, 0, 0], ![-58, 109, 0], ![-11, 0, 109]], ![![-1, 1, 0], ![26, -50, 6], ![-9, 30, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33631062282688258241555397894636433387385, -7610880437645903308190434029393079473032, -2785035737894649573174110082439295019350]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-33631062282688258241555397894636433387385, -7610880437645903308190434029393079473032, -2785035737894649573174110082439295019350]] 
 ![![109, 0, 0], ![101, 1, 0], ![27, 0, 1]] where
  M :=![![![-33631062282688258241555397894636433387385, -7610880437645903308190434029393079473032, -2785035737894649573174110082439295019350], ![-551437076103140615488473796322980413831300, -124793014857173648744969134397208363440917, -45665282625875419849142604176358476838192], ![-1415048147303365419106960305099333000021786, -320232592479900535160458653602289119829510, -117182134419527745436778700367815283967885]]]
  hmulB := by decide  
  f := ![![![3185833928371373695375, -254665742390339441180, 23525102777205105806]], ![![2994744927664177561307, -202608428551624735145, 7780191983079624214]], ![![319425419092588182843, -126051549766986969318, 41529952171303346113]]]
  g := ![![![7433613090300032241847517534861702375333, -7610880437645903308190434029393079473032, -2785035737894649573174110082439295019350], ![121886422526330589391562010005107735489289, -124793014857173648744969134397208363440917, -45665282625875419849142604176358476838192], ![312773957087099428980664115767549364861391, -320232592479900535160458653602289119829510, -117182134419527745436778700367815283967885]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-51, 1, 0]] ![![109, 0, 0], ![-51, 1, 0]]
  ![![3185833928371373695375, -254665742390339441180, 23525102777205105806]] where
 M := ![![![11881, 0, 0], ![-5559, 109, 0]], ![![-5559, 109, 0], ![2601, -101, 6]]]
 hmul := by decide  
 g := ![![![![-3665785788813020148329538370515371239224965, -829585967703403460592757309203845662560488, -303568895430516803475977998985883157109150]], ![![1163747100313960554830851496303477688925335, 263361887462767419972743001101838689683715, 96371540006751708382737010028045569148658]]], ![![![1163747100313960554830851496303477688925335, 263361887462767419972743001101838689683715, 96371540006751708382737010028045569148658]], ![![-369445295363992202170564204824993939850989, -83607349290108799929579708788505410282575, -30594286381355345024615867016690751270452]]]]
 hle2 := by decide  
def MulI109N1 : IdealMulLeCertificate' Table 
  ![![3185833928371373695375, -254665742390339441180, 23525102777205105806]] ![![-33631062282688258241555397894636433387385, -7610880437645903308190434029393079473032, -2785035737894649573174110082439295019350]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![31, 12, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![31, 12, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![31, 12, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![31, 12, 1], ![198, 73, 72], ![2343, 393, 61]]]
  hmulB := by decide  
  f := ![![![-30, -12, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -12, 113]], ![![0, 0, 1], ![-18, -7, 72], ![4, -3, 61]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [2, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 112], [0, 1]]
 g := ![![[25, 57], [32], [111], [98], [59, 31], [63, 1]], ![[0, 56], [32], [111], [98], [91, 82], [13, 112]]]
 h' := ![![[63, 112], [81, 31], [91, 22], [55, 26], [108, 95], [100, 12], [0, 1]], ![[0, 1], [0, 82], [8, 91], [111, 87], [104, 18], [65, 101], [63, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [67, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [2, 50, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![463340, 459273, 313682]
  a := ![1, 20, 101]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-81954, -29247, 313682]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![41, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![41, 1, 0]] 
 ![![113, 0, 0], ![41, 1, 0], ![52, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![41, 1, 0], ![0, 42, 6], ![198, 30, 41]]]
  hmulB := by decide  
  f := ![![![3281, 80, 0], ![-9040, 0, 0]], ![![1189, 29, 0], ![-3276, 0, 0]], ![![1520, 30, -1], ![-4188, 19, 0]]]
  g := ![![![1, 0, 0], ![-41, 113, 0], ![-52, 0, 113]], ![![0, 1, 0], ![-18, 42, 6], ![-28, 30, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![31, 12, 1]] ![![113, 0, 0], ![41, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![4633, 113, 0]], ![![3503, 1356, 113], ![1469, 565, 113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![41, 1, 0]]], ![![![31, 12, 1]], ![![13, 5, 1]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [74, 120, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 114, 50], [92, 12, 77], [0, 1]]
 g := ![![[30, 122, 71], [29, 71, 19], [97, 27, 2], [19, 68, 31], [125, 126, 72], [1]], ![[15, 70, 39, 117], [24, 99, 27, 124], [77, 18, 63, 32], [30, 16, 119, 117], [126, 125, 95, 117], [126, 119, 12, 32]], ![[40, 73, 94, 58], [67, 68, 99, 110], [32, 107, 79, 5], [41, 13, 4, 89], [13, 2, 125, 14], [81, 75, 108, 95]]]
 h' := ![![[66, 114, 50], [13, 67, 84], [61, 32, 107], [118, 114, 16], [21, 75, 44], [53, 7, 31], [0, 1]], ![[92, 12, 77], [7, 120, 40], [16, 104, 90], [122, 7, 50], [39, 40, 87], [42, 119, 87], [66, 114, 50]], ![[0, 1], [49, 67, 3], [13, 118, 57], [71, 6, 61], [16, 12, 123], [26, 1, 9], [92, 12, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 90], []]
 b := ![[], [1, 59, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [74, 120, 96, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7352284, 2256155, 975360]
  a := ![-1, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![57892, 17765, 7680]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [46, 47, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 4, 36], [34, 126, 95], [0, 1]]
 g := ![![[44, 82, 20], [129, 94, 117], [68, 15], [0, 117], [38, 34], [106, 1], []], ![[111, 98, 14, 107], [76, 16, 93, 65], [101, 49], [68, 3], [13, 21], [14, 25], [114, 117]], ![[64, 129, 18, 111], [2, 103, 10, 68], [38, 11], [29, 105], [106, 112], [85, 16], [55, 117]]]
 h' := ![![[72, 4, 36], [92, 25, 85], [60, 11, 36], [100, 28, 43], [10, 74, 95], [102, 81, 54], [0, 0, 1], [0, 1]], ![[34, 126, 95], [67, 105, 82], [2, 23, 85], [60, 76, 7], [31, 55, 93], [74, 96, 26], [71, 54, 126], [72, 4, 36]], ![[0, 1], [87, 1, 95], [95, 97, 10], [3, 27, 81], [114, 2, 74], [55, 85, 51], [67, 77, 4], [34, 126, 95]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102, 3], []]
 b := ![[], [24, 127, 120], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [46, 47, 25, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42986209, 12493470, 5076250]
  a := ![0, 3, 17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![328139, 95370, 38750]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![93953132107, -4371469314, -529419004]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![93953132107, -4371469314, -529419004]] 
 ![![137, 0, 0], ![0, 137, 0], ![19, 45, 1]] where
  M :=![![![93953132107, -4371469314, -529419004], ![-104824962792, 73699092673, -26228815884], ![-848080097040, -148614906552, 78070561987]]]
  hmulB := by decide  
  f := ![![![13545522345568107659, 3065420597512542198, 1121723824949672564]], ![![222101317340035167672, 50262657691570826777, 18392523585075253188]], ![![78991683189427158769, 17876219646876941367, 6541412781726193115]]]
  g := ![![![759212359, 141988218, -529419004], ![2872427292, 9153254069, -26228815884], ![-17017669889, -26728395591, 78070561987]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [123, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 136], [0, 1]]
 g := ![![[85, 88], [77], [135], [58, 72], [50], [68], [1]], ![[0, 49], [77], [135], [113, 65], [50], [68], [1]]]
 h' := ![![[94, 136], [97, 15], [72, 25], [127, 51], [116, 88], [52, 119], [14, 94], [0, 1]], ![[0, 1], [0, 122], [93, 112], [126, 86], [31, 49], [4, 18], [82, 43], [94, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [56, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [123, 43, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![72945, 65580, 41918]
  a := ![2, -8, -38]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5281, -13290, 41918]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13545522345568107659, -3065420597512542198, -1121723824949672564]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-13545522345568107659, -3065420597512542198, -1121723824949672564]] 
 ![![137, 0, 0], ![4, 1, 0], ![88, 0, 1]] where
  M :=![![![-13545522345568107659, -3065420597512542198, -1121723824949672564], ![-222101317340035167672, -50262657691570826777, -18392523585075253188], ![-569936392084144160592, -128979504148715460552, -47197237094058284579]]]
  hmulB := by decide  
  f := ![![![-93953132107, 4371469314, 529419004]], ![![-1978011428, -410315441, 206908700]], ![![-54159091448, 3892731432, -229793355]]]
  g := ![![![711152238248563845, -3065420597512542198, -1121723824949672564], ![11660521086955258540, -50262657691570826777, -18392523585075253188], ![29922178750276253464, -128979504148715460552, -47197237094058284579]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![93953132107, -4371469314, -529419004]] ![![-13545522345568107659, -3065420597512542198, -1121723824949672564]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB204I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB204I2 : PrimesBelowBoundCertificateInterval O 79 137 204 where
  m := 11
  g := ![2, 2, 2, 3, 1, 2, 3, 2, 1, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB204I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![2248091]
    · exact ![18769, 137]
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
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
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
      exact NI137N1
  β := ![I83N1, I89N1, I97N1, I101N0, I101N1, I101N2, I107N1, I109N0, I109N1, I113N1, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N0, I101N1, I101N2], [], [I107N1], [I109N0, I109N0, I109N1], [I113N1], [], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
