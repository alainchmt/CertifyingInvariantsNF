
import IdealArithmetic.Examples.NF3_1_411060_1.RI3_1_411060_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43896491427952765405594915, 953679406132170190930047, 2050578723237907743407523]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![43896491427952765405594915, 953679406132170190930047, 2050578723237907743407523]] 
 ![![139, 0, 0], ![0, 139, 0], ![59, 29, 1]] where
  M :=![![![43896491427952765405594915, 953679406132170190930047, 2050578723237907743407523], ![233765974449121482748457622, 5078715597406085642399407, 10920133200374574184872804], ![342485426748188884514482980, 7440715368475829484149430, 15998848797780659827272211]]]
  hmulB := by decide  
  f := ![![![2582209315663, -108342516993, -257012789907]], ![![-29299458049398, 7425124567975, -1312750954686]], ![![-5316434811475, 1494981408602, -339001141562]]]
  g := ![![![-554587433403480514067978, -420957579624224132143080, 2050578723237907743407523], ![-2953394851604161109057826, -2241763649017673134668431, 10920133200374574184872804], ![-4326954333243669390608471, -3284358991130671262638451, 15998848797780659827272211]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [2, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 138], [0, 1]]
 g := ![![[51, 113], [99, 1], [51], [119, 81], [80], [118], [1]], ![[62, 26], [136, 138], [51], [58, 58], [80], [118], [1]]]
 h' := ![![[37, 138], [80, 35], [108, 138], [40, 32], [10, 9], [46, 48], [137, 37], [0, 1]], ![[0, 1], [124, 104], [71, 1], [112, 107], [65, 130], [15, 91], [116, 102], [37, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [85, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [2, 102, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1826, 1920, -1875]
  a := ![0, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![809, 405, -1875]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2582209315663, -108342516993, -257012789907]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![2582209315663, -108342516993, -257012789907]] 
 ![![139, 0, 0], ![130, 1, 0], ![8, 0, 1]] where
  M :=![![![2582209315663, -108342516993, -257012789907], ![-29299458049398, 7425124567975, -1312750954686], ![-41650504986600, -1133988173010, 6112373613289]]]
  hmulB := by decide  
  f := ![![![43896491427952765405594915, 953679406132170190930047, 2050578723237907743407523]], ![![42736042158870366801984148, 928467902119339643620903, 1996369548354694826099646]], ![![4990340706272021638555700, 108418349766425834615754, 233118550961754832910305]]]
  g := ![![![134696682331, -108342516993, -257012789907], ![-7079594562940, 7425124567975, -1312750954686], ![409129270492, -1133988173010, 6112373613289]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![43896491427952765405594915, 953679406132170190930047, 2050578723237907743407523]] ![![2582209315663, -108342516993, -257012789907]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![23, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![23, 1, 0]] 
 ![![149, 0, 0], ![23, 1, 0], ![112, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![23, 1, 0], ![0, 21, 5], ![114, -18, 26]]]
  hmulB := by decide  
  f := ![![![254, 11, 0], ![-1639, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![190, 4, -1], ![-1226, 30, 0]]]
  g := ![![![1, 0, 0], ![-23, 149, 0], ![-112, 0, 149]], ![![0, 1, 0], ![-7, 21, 5], ![-16, -18, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![24, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![24, 1, 0]] 
 ![![149, 0, 0], ![24, 1, 0], ![103, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![24, 1, 0], ![0, 22, 5], ![114, -18, 27]]]
  hmulB := by decide  
  f := ![![![2497, 104, 0], ![-15496, 0, 0]], ![![360, 15, 0], ![-2234, 0, 0]], ![![1691, 66, -1], ![-10494, 30, 0]]]
  g := ![![![1, 0, 0], ![-24, 149, 0], ![-103, 0, 149]], ![![0, 1, 0], ![-7, 22, 5], ![-15, -18, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1482823391881259093, 1554458273895339280, -870952996917078978]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![-1482823391881259093, 1554458273895339280, -870952996917078978]] 
 ![![149, 0, 0], ![101, 1, 0], ![116, 0, 1]] where
  M :=![![![-1482823391881259093, 1554458273895339280, -870952996917078978], ![-99288641648547003492, 11085414004835483951, 5159432378725459466], ![77919601575521674428, -38431684893121054776, 16244846383560943417]]]
  hmulB := by decide  
  f := ![![![378366527013270415067038774922476310183, 8220255265151523993430207284158579168, 17674996899291325514321382289876106558]], ![![269999791106439751881903045961181097155, 5865918483731727725898284663331582079, 12612758079543996466151508688375221328]], ![![314379703894535926118524691962732927208, 6830100528700303741798771149839288840, 14685919326423817879152946362768045705]]]
  g := ![![![-385587660489458825, 1554458273895339280, -870952996917078978], ![-12197379946772377051, 11085414004835483951, 5159432378725459466], ![13926963726762944768, -38431684893121054776, 16244846383560943417]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![23, 1, 0]] ![![149, 0, 0], ![24, 1, 0]]
  ![![378366527013270415067038774922476310183, 8220255265151523993430207284158579168, 17674996899291325514321382289876106558]] where
 M := ![![![22201, 0, 0], ![3576, 149, 0]], ![![3427, 149, 0], ![552, 45, 5]]]
 hmul := by decide  
 g := ![![![![-220940685390307604857, 231614282810405552720, -129771996540644767722]], ![![-134876403053697221724, 48392412578323626671, -15743439547284436006]]], ![![![-133393579661815962631, 46837954304428287391, -14872486550367357028]], ![![-32865163614935985264, 7817088409008179775, -1123270908307229549]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![378366527013270415067038774922476310183, 8220255265151523993430207284158579168, 17674996899291325514321382289876106558]] ![![-1482823391881259093, 1554458273895339280, -870952996917078978]]
  ![![149, 0, 0]] where
 M := ![![![149, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![11, -15, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![11, -15, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![11, 136, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![11, -15, 1], ![114, 23, -72], ![-1596, 282, -49]]]
  hmulB := by decide  
  f := ![![![-10, 15, -1], ![151, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -136, 151]], ![![0, -1, 1], ![6, 65, -72], ![-7, 46, -49]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [122, 150, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 150], [0, 1]]
 g := ![![[125, 17], [66, 50], [70, 43], [36], [139, 8], [1], [1]], ![[142, 134], [116, 101], [113, 108], [36], [147, 143], [1], [1]]]
 h' := ![![[1, 150], [102, 116], [67, 79], [140, 88], [105, 6], [115, 59], [29, 1], [0, 1]], ![[0, 1], [67, 35], [146, 72], [77, 63], [111, 145], [23, 92], [30, 150], [1, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [111, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [122, 150, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![999, 1644, -19]
  a := ![-1, -4, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, 28, -19]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![72, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![72, 1, 0]] 
 ![![151, 0, 0], ![72, 1, 0], ![49, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![72, 1, 0], ![0, 70, 5], ![114, -18, 75]]]
  hmulB := by decide  
  f := ![![![4897, 68, 0], ![-10268, 0, 0]], ![![2232, 31, 0], ![-4680, 0, 0]], ![![1591, -34, -4], ![-3336, 121, 0]]]
  g := ![![![1, 0, 0], ![-72, 151, 0], ![-49, 0, 151]], ![![0, 1, 0], ![-35, 70, 5], ![-15, -18, 75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![11, -15, 1]] ![![151, 0, 0], ![72, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![10872, 151, 0]], ![![1661, -2265, 151], ![906, -1057, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![72, 1, 0]]], ![![![11, -15, 1]], ![![6, -7, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-7, 41, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-7, 41, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![150, 41, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-7, 41, 1], ![114, -107, 208], ![4788, -726, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-150, -41, 157]], ![![-1, 0, 1], ![-198, -55, 208], ![-66, -31, 101]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [121, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 156], [0, 1]]
 g := ![![[81, 109], [17], [23, 99], [64, 141], [98, 143], [93], [1]], ![[0, 48], [17], [141, 58], [37, 16], [94, 14], [93], [1]]]
 h' := ![![[90, 156], [106, 100], [43, 71], [106, 141], [74, 112], [91, 92], [36, 90], [0, 1]], ![[0, 1], [0, 57], [153, 86], [79, 16], [106, 45], [50, 65], [129, 67], [90, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102]]
 b := ![[], [60, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [121, 67, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-71, 57, 55]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-53, -14, 55]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-51, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-51, 1, 0]] 
 ![![157, 0, 0], ![106, 1, 0], ![56, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-51, 1, 0], ![0, -53, 5], ![114, -18, -48]]]
  hmulB := by decide  
  f := ![![![6682, -131, 0], ![20567, 0, 0]], ![![4540, -89, 0], ![13974, 0, 0]], ![![2360, -25, -2], ![7264, 63, 0]]]
  g := ![![![1, 0, 0], ![-106, 157, 0], ![-56, 0, 157]], ![![-1, 1, 0], ![34, -53, 5], ![30, -18, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-7, 41, 1]] ![![157, 0, 0], ![-51, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-8007, 157, 0]], ![![-1099, 6437, 157], ![471, -2198, 157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-51, 1, 0]]], ![![![-7, 41, 1]], ![![3, -14, 1]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [48, 131, 85, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 121, 45], [63, 41, 118], [0, 1]]
 g := ![![[71, 105, 35], [144, 11, 97], [94, 36], [134, 49], [88, 55], [85, 78, 1], []], ![[48, 118, 155, 63], [132, 76, 27, 20], [128, 10], [105, 26], [35, 69], [95, 88, 48, 13], [135, 69]], ![[58, 121, 80, 133], [85, 12, 160, 55], [52, 21], [35, 155], [31, 60], [59, 34, 18, 1], [62, 69]]]
 h' := ![![[15, 121, 45], [97, 21, 19], [4, 94, 89], [142, 36, 157], [39, 147, 156], [158, 117, 113], [0, 0, 1], [0, 1]], ![[63, 41, 118], [68, 35, 94], [60, 30, 55], [70, 0, 70], [63, 154, 134], [73, 25, 118], [102, 74, 41], [15, 121, 45]], ![[0, 1], [75, 107, 50], [89, 39, 19], [38, 127, 99], [67, 25, 36], [96, 21, 95], [15, 89, 121], [63, 41, 118]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 136], []]
 b := ![[], [132, 11, 131], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [48, 131, 85, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3098141, 1704002, -756483]
  a := ![1, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19007, 10454, -4641]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [141, 99, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [112, 107, 90], [155, 59, 77], [0, 1]]
 g := ![![[30, 122, 18], [164, 54, 2], [13, 91, 29], [75, 88], [22, 88], [48, 100, 1], []], ![[50, 95, 75, 102], [77, 109, 68, 111], [31, 146, 77, 82], [45, 48], [0, 3], [118, 7, 20, 165], [105, 84]], ![[20, 151, 61, 7], [87, 60, 81, 85], [68, 55, 7, 100], [31, 150], [12, 11], [80, 133, 52, 147], [118, 84]]]
 h' := ![![[112, 107, 90], [89, 47, 39], [4, 57, 154], [100, 13, 14], [133, 106, 103], [79, 19, 103], [0, 0, 1], [0, 1]], ![[155, 59, 77], [6, 149, 18], [43, 155, 21], [129, 46, 159], [63, 51, 86], [118, 94, 105], [77, 59, 59], [112, 107, 90]], ![[0, 1], [44, 138, 110], [149, 122, 159], [156, 108, 161], [39, 10, 145], [27, 54, 126], [39, 108, 107], [155, 59, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [116, 141], []]
 b := ![[], [100, 95, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [141, 99, 67, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-745989, 495489, -237474]
  a := ![0, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4467, 2967, -1422]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def PBC167 : ContainsPrimesAboveP 167 ![I167N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![167, 0, 0]]) timesTableT_eq_Table B_one_repr 167 (by decide) 𝕀

instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![30, 14, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![30, 14, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![30, 14, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![30, 14, 1], ![114, -16, 73], ![1710, -240, 57]]]
  hmulB := by decide  
  f := ![![![-29, -14, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -14, 173]], ![![0, 0, 1], ![-12, -6, 73], ![0, -6, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [18, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 172], [0, 1]]
 g := ![![[149, 137], [56], [157, 169], [153, 10], [9], [126, 130], [1]], ![[167, 36], [56], [159, 4], [148, 163], [9], [61, 43], [1]]]
 h' := ![![[86, 172], [107, 134], [115, 103], [14, 160], [26, 23], [154, 170], [155, 86], [0, 1]], ![[0, 1], [40, 39], [150, 70], [107, 13], [101, 150], [69, 3], [112, 87], [86, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [161]]
 b := ![[], [85, 167]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [18, 87, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![141466, 90249, -57749]
  a := ![1, -21, 62]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10832, 5195, -57749]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-73, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-73, 1, 0]] 
 ![![173, 0, 0], ![100, 1, 0], ![116, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-73, 1, 0], ![0, -75, 5], ![114, -18, -70]]]
  hmulB := by decide  
  f := ![![![5695, -78, 0], ![13494, 0, 0]], ![![3432, -47, 0], ![8132, 0, 0]], ![![3876, -8, -3], ![9184, 104, 0]]]
  g := ![![![1, 0, 0], ![-100, 173, 0], ![-116, 0, 173]], ![![-1, 1, 0], ![40, -75, 5], ![58, -18, -70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![30, 14, 1]] ![![173, 0, 0], ![-73, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-12629, 173, 0]], ![![5190, 2422, 173], ![-2076, -1038, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-73, 1, 0]]], ![![![30, 14, 1]], ![![-12, -6, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1022717858859083, 64383588280577, -175027645838011]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![1022717858859083, 64383588280577, -175027645838011]] 
 ![![179, 0, 0], ![0, 179, 0], ![128, 159, 1]] where
  M :=![![![1022717858859083, 64383588280577, -175027645838011], ![-19953151625533254, 4044448307382127, -203164996111148], ![-12613422561547476, -3259236339106518, 3841283311270979]]]
  hmulB := by decide  
  f := ![![![83093346638465000720702006311, 1805256203807759427608786485, 3881618851910484884165458419]], ![![442504549117795276794862259766, 9613694896460753950506181799, 20671137574770251790540307682]], ![![456103214725166753933939776702, 9909134621111951026689580561, 21306385027398006176592927869]]]
  g := ![![![130872941486729, 155831169142594, -175027645838011], ![33809876406110, 203059679827121, -203164996111148], ![-2817305510638172, -3430297669448001, 3841283311270979]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [79, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 178], [0, 1]]
 g := ![![[60, 25], [4, 107], [169], [51], [94, 117], [94, 57], [1]], ![[58, 154], [110, 72], [169], [51], [56, 62], [25, 122], [1]]]
 h' := ![![[93, 178], [42, 5], [63, 110], [139, 166], [92, 87], [92, 98], [100, 93], [0, 1]], ![[0, 1], [149, 174], [90, 69], [4, 13], [128, 92], [77, 81], [157, 86], [93, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [104, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [79, 86, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![906, 250, 77]
  a := ![-1, -1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50, -67, 77]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6065609168120795087766906643, -2807411598301908130359816553, 2693651165159878905867291341]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-6065609168120795087766906643, -2807411598301908130359816553, 2693651165159878905867291341]] 
 ![![179, 0, 0], ![97, 1, 0], ![126, 0, 1]] where
  M :=![![![-6065609168120795087766906643, -2807411598301908130359816553, 2693651165159878905867291341], ![307076232828226195268871212874, -48936506944394799132658517675, -5956104496029903934197208742], ![-12968689378191331592147874168, 82857222751352893216884194046, -54892611440424703066855726417]]]
  hmulB := by decide  
  f := ![![![-3179758937908193093634975824656855861192569114596054470607, -69082300587165025130326012151565453146270669888183575085, -148539115792476049723178709138561406970032039496190858501]], ![![-1817709922778977652240419149907882787319904226918341014067, -39490912901811740703903520751740047958814000240458428216, -84912419453538715631114530584435575210807582676312869975]], ![![-2376862947730231353806181520300772628846492834128053344834, -51638870686723660953929350961071540913059311854067689448, -111032668673935920046361958522300940750306913454401064187]]]
  g := ![![![-408640954988717589844376592, -2807411598301908130359816553, 2693651165159878905867291341], ![32426740630917819032656959379, -48936506944394799132658517675, -5956104496029903934197208742], ![-6333241646736923950872028872, 82857222751352893216884194046, -54892611440424703066855726417]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![1022717858859083, 64383588280577, -175027645838011]] ![![-6065609168120795087766906643, -2807411598301908130359816553, 2693651165159878905867291341]]
  ![![179, 0, 0]] where
 M := ![![![15837142095535842629344403699343808592359777, -20524202532593977022907381518801594578181880, 11979094326835308387723290719369113407332756]]]
 hmul := by decide  
 g := ![![![![88475654165004707426505048599686081521563, -114660349344100430295571963792187679207720, 66922314675057588758230674409883315124764]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4739595560305573, 1424948006185507, -1580084677553557]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![4739595560305573, 1424948006185507, -1580084677553557]] 
 ![![181, 0, 0], ![15, 1, 0], ![142, 0, 1]] where
  M :=![![![4739595560305573, 1424948006185507, -1580084677553557], ![-180129653241105498, 30331223743898585, 2384485998266864], ![-17685580535957700, -44610080241981810, 32715709742165449]]]
  hmulB := by decide  
  f := ![![![-1098679623848629823151111960733505, -23869518886747708440451514850527, -51323670458190413779236989156893]], ![![-123376203259464942088948597651317, -2680427078060345772655888668322, -5763390401553403260931068392689]], ![![-909306796529438568069073966193390, -19755272858867407800921722162144, -42477316733143953030030741039837]]]
  g := ![![![1147720440221702, 1424948006185507, -1580084677553557], ![-5379530503610381, 30331223743898585, 2384485998266864], ![-22067210830352068, -44610080241981810, 32715709742165449]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![29, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![29, 1, 0]] 
 ![![181, 0, 0], ![29, 1, 0], ![133, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![29, 1, 0], ![0, 27, 5], ![114, -18, 32]]]
  hmulB := by decide  
  f := ![![![552, 19, 0], ![-3439, 0, 0]], ![![58, 2, 0], ![-361, 0, 0]], ![![396, -8, -4], ![-2467, 145, 0]]]
  g := ![![![1, 0, 0], ![-29, 181, 0], ![-133, 0, 181]], ![![0, 1, 0], ![-8, 27, 5], ![-20, -18, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-45, 1, 0]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-45, 1, 0]] 
 ![![181, 0, 0], ![136, 1, 0], ![120, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-45, 1, 0], ![0, -47, 5], ![114, -18, -42]]]
  hmulB := by decide  
  f := ![![![8056, -179, 0], ![32399, 0, 0]], ![![6076, -135, 0], ![24436, 0, 0]], ![![5340, -81, -4], ![21476, 145, 0]]]
  g := ![![![1, 0, 0], ![-136, 181, 0], ![-120, 0, 181]], ![![-1, 1, 0], ![32, -47, 5], ![42, -18, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![4739595560305573, 1424948006185507, -1580084677553557]] ![![181, 0, 0], ![29, 1, 0]]
  ![![181, 0, 0], ![87, -64, 1]] where
 M := ![![![857866796415308713, 257915589119576767, -285995326637193817], ![-42681381992243881, 71654715923278288, -43437969650786289]]]
 hmul := by decide  
 g := ![![![![4113795462829543, 1885306698581667, -1587277782122247], ![1301951926932890, 0, 0]], ![![-145548569010139, 329484121498384, -238951309367943], ![-187782655188606, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![87, -64, 1]] ![![181, 0, 0], ![-45, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-8145, 181, 0]], ![![15747, -11584, 181], ![-3801, 3077, -362]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-45, 1, 0]]], ![![![87, -64, 1]], ![![-21, 17, -2]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)


lemma PB182I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 181 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 181 (by omega)

def PB182I3 : PrimesBelowBoundCertificateInterval O 137 181 182 where
  m := 9
  g := ![2, 3, 2, 2, 1, 1, 2, 2, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181]
  hP := PB182I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![149, 149, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![181, 181, 181]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
  β := ![I139N1, I149N0, I149N1, I149N2, I151N1, I157N1, I173N1, I179N1, I181N0, I181N1, I181N2]
  Il := ![[I139N1], [I149N0, I149N1, I149N2], [I151N1], [I157N1], [], [], [I173N1], [I179N1], [I181N0, I181N1, I181N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
