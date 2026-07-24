
import IdealArithmetic.Examples.NF3_1_946067_1.RI3_1_946067_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7296555379855877711416364507542, -2281534623566880186930124698024, -280886745252178042510036503321]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-7296555379855877711416364507542, -2281534623566880186930124698024, -280886745252178042510036503321]] 
 ![![37, 0, 0], ![0, 37, 0], ![9, 7, 1]] where
  M :=![![![-7296555379855877711416364507542, -2281534623566880186930124698024, -280886745252178042510036503321], ![-59267103248209566969617702200731, -18532025189942999411817824640382, -2281534623566880186930124698024], ![-481403805572611719442256311283064, -150528488190884774446822690121691, -18532025189942999411817824640382]]]
  hmulB := by decide  
  f := ![![![6427438420598180, -150921931611639, -78839124751242]], ![![-16635055322512062, 3273873430548500, -150921931611639]], ![![-2444404568709639, -30084215071429, 40753183419077]]]
  g := ![![![-128880396556385819698000972369, -8522362345990105117834302021, -280886745252178042510036503321], ![-1046845719894801223979637295095, -69223860134455083873160858222, -2281534623566880186930124698024], ![-8503123753057424992862051068098, -562278698953615636867511287541, -18532025189942999411817824640382]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [27, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 36], [0, 1]]
 g := ![![[5, 11], [11], [15, 3], [21], [1]], ![[0, 26], [11], [17, 34], [21], [1]]]
 h' := ![![[13, 36], [3, 14], [2, 14], [14, 15], [10, 13], [0, 1]], ![[0, 1], [0, 23], [36, 23], [24, 22], [31, 24], [13, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [36, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [27, 24, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![449, 267, 17]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, 4, 17]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6427438420598180, -150921931611639, -78839124751242]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![6427438420598180, -150921931611639, -78839124751242]] 
 ![![37, 0, 0], ![30, 1, 0], ![25, 0, 1]] where
  M :=![![![6427438420598180, -150921931611639, -78839124751242], ![-16635055322512062, 3273873430548500, -150921931611639], ![-31844527570055829, -22671932586977622, 3273873430548500]]]
  hmulB := by decide  
  f := ![![![-7296555379855877711416364507542, -2281534623566880186930124698024, -280886745252178042510036503321]], ![![-7517939584969889143570503714243, -2350758483701335270803285556246, -289409107598168147627870805342]], ![![-17941018650513747627774741188422, -5609914967028561597839886691143, -690653887060741904718073979011]]]
  g := ![![![349353364533200, -150921931611639, -78839124751242], ![-3002113782396651, 3273873430548500, -150921931611639], ![15309908493934063, -22671932586977622, 3273873430548500]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-7296555379855877711416364507542, -2281534623566880186930124698024, -280886745252178042510036503321]] ![![6427438420598180, -150921931611639, -78839124751242]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [9, 13, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 12, 10], [32, 28, 31], [0, 1]]
 g := ![![[0, 35, 33], [19, 5], [18, 21], [27, 32, 1], []], ![[1, 3, 15, 9], [11, 8], [18, 4], [34, 29, 2, 9], [37, 18]], ![[16, 22, 17, 10], [12, 31], [24, 32], [9, 26, 22, 36], [16, 18]]]
 h' := ![![[0, 12, 10], [32, 26, 19], [11, 7, 28], [3, 17, 29], [0, 0, 1], [0, 1]], ![[32, 28, 31], [19, 26, 13], [35, 38, 34], [22, 7, 39], [36, 13, 28], [0, 12, 10]], ![[0, 1], [36, 30, 9], [29, 37, 20], [32, 17, 14], [19, 28, 12], [32, 28, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 32], []]
 b := ![[], [18, 24, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [9, 13, 9, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![729431, 385154, 35424]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17791, 9394, 864]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1043508008479916165840618574268, 326290904046187906717171824278, 40170676831386613349703162625]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![1043508008479916165840618574268, 326290904046187906717171824278, 40170676831386613349703162625]] 
 ![![43, 0, 0], ![0, 43, 0], ![4, 42, 1]] where
  M :=![![![1043508008479916165840618574268, 326290904046187906717171824278, 40170676831386613349703162625], ![8476012811422575416787367313875, 2650335081735380699828745079268, 326290904046187906717171824278], ![68847380753745648317323254922658, 21527648973270091685474240284995, 2650335081735380699828745079268]]]
  hmulB := by decide  
  f := ![![![-1538629283178902, 211090361754497, -2667242086912]], ![![-562788080338432, -1645318966655382, 211090361754497]], ![![342987205192305, -1404144389829456, 167669936248508]]]
  g := ![![![20530820957078365405623393576, -31648314485396508231868860604, 40170676831386613349703162625], ![166763934772972646277178605041, -257067043911732822844010966056, 326290904046187906717171824278], ![1354559079693119198093215688502, -2088056382781765062961233791727, 2650335081735380699828745079268]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [30, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 42], [0, 1]]
 g := ![![[25, 10], [0, 1], [9], [0, 17], [1]], ![[7, 33], [24, 42], [9], [21, 26], [1]]]
 h' := ![![[24, 42], [0, 28], [31, 1], [0, 3], [13, 24], [0, 1]], ![[0, 1], [27, 15], [12, 42], [29, 40], [30, 19], [24, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [34, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [30, 19, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1216, 1680, 298]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56, -252, 298]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1538629283178902, 211090361754497, -2667242086912]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-1538629283178902, 211090361754497, -2667242086912]] 
 ![![43, 0, 0], ![1, 1, 0], ![42, 0, 1]] where
  M :=![![![-1538629283178902, 211090361754497, -2667242086912], ![-562788080338432, -1645318966655382, 211090361754497], ![44540066330198867, 7880826389841448, -1645318966655382]]]
  hmulB := by decide  
  f := ![![![1043508008479916165840618574268, 326290904046187906717171824278, 40170676831386613349703162625]], ![![221384205114011432154139206701, 69223860134455083873160858222, 8522362345990105117834302021]], ![![2620342258369816913549517093998, 819345742865348459711522253597, 100872174619851592105029718826]]]
  g := ![![![-38085941332165, 211090361754497, -2667242086912], ![-181006146683068, -1645318966655382, 211090361754497], ![2459596198601941, 7880826389841448, -1645318966655382]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![1043508008479916165840618574268, 326290904046187906717171824278, 40170676831386613349703162625]] ![![-1538629283178902, 211090361754497, -2667242086912]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2219, -62, -26]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![2219, -62, -26]] 
 ![![47, 0, 0], ![0, 47, 0], ![43, 6, 1]] where
  M :=![![![2219, -62, -26], ![-5486, 1179, -62], ![-13082, -7966, 1179]]]
  hmulB := by decide  
  f := ![![![-19067, -5962, -734]], ![![-154874, -48427, -5962]], ![![-63981, -20006, -2463]]]
  g := ![![![71, 2, -26], ![-60, 33, -62], ![-1357, -320, 1179]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [36, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 46], [0, 1]]
 g := ![![[35, 17], [45, 42], [28, 4], [34, 34], [1]], ![[0, 30], [0, 5], [17, 43], [11, 13], [1]]]
 h' := ![![[9, 46], [25, 39], [26, 18], [45, 2], [11, 9], [0, 1]], ![[0, 1], [0, 8], [0, 29], [16, 45], [45, 38], [9, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [20, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [36, 38, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![458, 253, 3]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, 5, 3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19067, -5962, -734]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-19067, -5962, -734]] 
 ![![47, 0, 0], ![41, 1, 0], ![11, 0, 1]] where
  M :=![![![-19067, -5962, -734], ![-154874, -48427, -5962], ![-1257982, -393354, -48427]]]
  hmulB := by decide  
  f := ![![![2219, -62, -26]], ![![1819, -29, -24]], ![![241, -184, 19]]]
  g := ![![![4967, -5962, -734], ![40345, -48427, -5962], ![327707, -393354, -48427]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![2219, -62, -26]] ![![-19067, -5962, -734]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [38, 47, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 17, 20], [16, 35, 33], [0, 1]]
 g := ![![[8, 6, 42], [12, 43], [47, 20, 6], [12, 52], [1]], ![[25, 36, 30, 41], [26, 44], [43, 32, 13, 3], [50, 16], [5, 2, 11, 50]], ![[9, 26, 23, 5], [42, 9], [5, 42, 39, 39], [4, 43], [52, 18, 8, 3]]]
 h' := ![![[14, 17, 20], [12, 47, 25], [16, 42, 34], [34, 25, 18], [15, 6, 30], [0, 1]], ![[16, 35, 33], [4, 31, 13], [12, 49, 16], [2, 48, 17], [10, 39, 4], [14, 17, 20]], ![[0, 1], [9, 28, 15], [11, 15, 3], [7, 33, 18], [0, 8, 19], [16, 35, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 39], []]
 b := ![[], [49, 47, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [38, 47, 23, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2181427, 657783, 67469]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![41159, 12411, 1273]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7768093, -10163716, 1369026]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-7768093, -10163716, 1369026]] 
 ![![59, 0, 0], ![3, 1, 0], ![50, 0, 1]] where
  M :=![![![-7768093, -10163716, 1369026], ![288864486, 46992947, -10163716], ![-2144544076, -117684154, 46992947]]]
  hmulB := by decide  
  f := ![![![1012228748788545, 316510300697048, 38966556669034]], ![![190824232263251, 59668168095611, 7345931706850]], ![![1989747642144142, 622167296947466, 76596929644095]]]
  g := ![![![-775055, -10163716, 1369026], ![11119855, 46992947, -10163716], ![-70188796, -117684154, 46992947]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2649746, 423572, -92309]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![2649746, 423572, -92309]] 
 ![![59, 0, 0], ![13, 1, 0], ![8, 0, 1]] where
  M :=![![![2649746, 423572, -92309], ![-19477199, -1042614, 423572], ![89373692, -2534319, -1042614]]]
  hmulB := by decide  
  f := ![![![2160510520464, 675562549779, 83170583458]], ![![773485252130, 241858423829, 29775934487]], ![![2708945460459, 847050771170, 104283025872]]]
  g := ![![![-35902, 423572, -92309], ![-157827, -1042614, 423572], ![2214589, -2534319, -1042614]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-225352627677926380763867950, -70464732437776770326448141, -8675129952036204999948062]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-225352627677926380763867950, -70464732437776770326448141, -8675129952036204999948062]] 
 ![![59, 0, 0], ![43, 1, 0], ![39, 0, 1]] where
  M :=![![![-225352627677926380763867950, -70464732437776770326448141, -8675129952036204999948062], ![-1830452419879639254989041082, -572357825759374580761790430, -70464732437776770326448141], ![-14868058544370898538880557751, -4649041717390710068046966722, -572357825759374580761790430]]]
  hmulB := by decide  
  f := ![![![-299732153821098, -3836937302134, 5015366290779]], ![![-200512547914455, -4476369596300, 3590234122057]], ![![-211849962199544, 12798715940437, 1635284460177]]]
  g := ![![![53270524326709944716464009, -70464732437776770326448141, -8675129952036204999948062], ![432695909370284097635583473, -572357825759374580761790430, -70464732437776770326448141], ![3514621873017715983675404035, -4649041717390710068046966722, -572357825759374580761790430]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-7768093, -10163716, 1369026]] ![![2649746, 423572, -92309]]
  ![![299732153821098, 3836937302134, -5015366290779]] where
 M := ![![![299732153821098, 3836937302134, -5015366290779]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![299732153821098, 3836937302134, -5015366290779]] ![![-225352627677926380763867950, -70464732437776770326448141, -8675129952036204999948062]]
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
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9719102644657219100, -3039032535133567422, -374144643123852337]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-9719102644657219100, -3039032535133567422, -374144643123852337]] 
 ![![61, 0, 0], ![0, 61, 0], ![43, 12, 1]] where
  M :=![![![-9719102644657219100, -3039032535133567422, -374144643123852337], ![-78944519699132843107, -24684888369611312580, -3039032535133567422], ![-641235864913182726042, -200505821104475539987, -24684888369611312580]]]
  hmulB := by decide  
  f := ![![![7748446674, 583932281, -189331584]], ![![-39948964224, 175183314, 583932281]], ![![-376961515, 174092047, -15719466]]]
  g := ![![![104411754256859531, 23782019382830502, -374144643123852337], ![848096382157550099, 193172164786745844, -3039032535133567422], ![6888759589837765818, 1569062939850167393, -24684888369611312580]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [36, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 60], [0, 1]]
 g := ![![[23, 39], [42], [54, 22], [58, 46], [26, 1]], ![[0, 22], [42], [16, 39], [34, 15], [52, 60]]]
 h' := ![![[26, 60], [16, 51], [8, 15], [47, 49], [40, 30], [0, 1]], ![[0, 1], [0, 10], [32, 46], [40, 12], [27, 31], [26, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [20, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [36, 35, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1264, 70, 16]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32, -2, 16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7748446674, 583932281, -189331584]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![7748446674, 583932281, -189331584]] 
 ![![61, 0, 0], ![49, 1, 0], ![39, 0, 1]] where
  M :=![![![7748446674, 583932281, -189331584], ![-39948964224, 175183314, 583932281], ![123209711291, -16591672984, 175183314]]]
  hmulB := by decide  
  f := ![![![-9719102644657219100, -3039032535133567422, -374144643123852337]], ![![-9101320480120271787, -2845860370346821578, -350362623741021835]], ![![-16725915869751053622, -5229968688109584745, -643877531990845143]]]
  g := ![![![-220988579, 583932281, -189331584], ![-1168955829, 175183314, 583932281], ![15235566201, -16591672984, 175183314]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-9719102644657219100, -3039032535133567422, -374144643123852337]] ![![7748446674, 583932281, -189331584]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [53, 2, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 29], [23, 37], [0, 1]]
 g := ![![[5, 10, 9], [39, 20, 56], [], [45, 16], [26, 1], []], ![[49, 47, 65], [0, 6, 62], [], [26, 62], [29, 29], []], ![[38, 10, 60], [40, 41, 16], [], [11, 56], [49, 37], []]]
 h' := ![![[3, 29], [10, 15, 64], [9, 25, 49], [64, 7], [29, 29, 4], [0, 0, 1], [0, 1]], ![[23, 37], [28, 47, 23], [56, 5, 4], [18, 2], [18, 63, 14], [9, 40, 37], [3, 29]], ![[0, 1], [41, 5, 47], [40, 37, 14], [24, 58], [65, 42, 49], [60, 27, 29], [23, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37], []]
 b := ![[], [39, 58, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [53, 2, 41, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![492316, 196712, 22177]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7348, 2936, 331]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [7, 21, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 62, 1], [51, 8, 70], [0, 1]]
 g := ![![[14, 5, 4], [60, 25, 6], [52, 62, 19], [18, 27], [24, 1], []], ![[43, 28, 19, 50], [29, 5, 19, 25], [56, 31, 58, 58], [33, 8], [13, 64], [6, 1]], ![[4, 66, 52, 44], [60, 39, 60, 63], [63, 39, 19, 13], [47, 50], [62, 10], [8, 1]]]
 h' := ![![[44, 62, 1], [6, 66, 2], [62, 5, 52], [53, 19, 27], [45, 57, 58], [0, 0, 1], [0, 1]], ![[51, 8, 70], [24, 41, 11], [9, 64, 66], [55, 59, 22], [12, 10, 24], [48, 69, 8], [44, 62, 1]], ![[0, 1], [13, 35, 58], [29, 2, 24], [15, 64, 22], [42, 4, 60], [60, 2, 62], [51, 8, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 59], []]
 b := ![[], [65, 68, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [7, 21, 47, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1314707, -12638, 25702]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18517, -178, 362]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17617263359919, -2707154515418, 600307975500]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-17617263359919, -2707154515418, 600307975500]] 
 ![![73, 0, 0], ![0, 73, 0], ![45, 42, 1]] where
  M :=![![![-17617263359919, -2707154515418, 600307975500], ![126664982830500, 6395055660081, -2707154515418], ![-571209602753198, 18378802213780, 6395055660081]]]
  hmulB := by decide  
  f := ![![![1241794442418395837794337, 388292402131601475123546, 47803871970342809913688]], ![![10086616985742332891788168, 3153949321232108234341857, 388292402131601475123546]], ![![7691073426846215142560499, 2404895104913383618077364, 296074033553764337474613]]]
  g := ![![![-611385236403, -382466979266, 600307975500], ![3403930630470, 1645144456269, -2707154515418], ![-11766946677491, -3427582678214, 6395055660081]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [11, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 72], [0, 1]]
 g := ![![[54, 67], [18], [18], [46, 18], [27], [1]], ![[41, 6], [18], [18], [12, 55], [27], [1]]]
 h' := ![![[63, 72], [20, 40], [46, 50], [5, 23], [43, 23], [62, 63], [0, 1]], ![[0, 1], [58, 33], [57, 23], [67, 50], [32, 50], [16, 10], [63, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [65, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [11, 10, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-112, 95, 77]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-49, -43, 77]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1241794442418395837794337, 388292402131601475123546, 47803871970342809913688]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![1241794442418395837794337, 388292402131601475123546, 47803871970342809913688]] 
 ![![73, 0, 0], ![31, 1, 0], ![61, 0, 1]] where
  M :=![![![1241794442418395837794337, 388292402131601475123546, 47803871970342809913688], ![10086616985742332891788168, 3153949321232108234341857, 388292402131601475123546], ![81929696849767911251068206, 25618313071006391896730008, 3153949321232108234341857]]]
  hmulB := by decide  
  f := ![![![-17617263359919, -2707154515418, 600307975500]], ![![-5746166867493, -1062010059149, 217840996234]], ![![-22546063941209, -2010378400366, 589230714597]]]
  g := ![![![-187826112518522757476309, 388292402131601475123546, 47803871970342809913688], ![-1525639020581927566511585, 3153949321232108234341857, 388292402131601475123546], ![-12392176944473819723868703, 25618313071006391896730008, 3153949321232108234341857]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-17617263359919, -2707154515418, 600307975500]] ![![1241794442418395837794337, 388292402131601475123546, 47803871970342809913688]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17181850651137681, -5372533355362550, -661429106689300]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-17181850651137681, -5372533355362550, -661429106689300]] 
 ![![79, 0, 0], ![0, 79, 0], ![41, 9, 1]] where
  M :=![![![-17181850651137681, -5372533355362550, -661429106689300], ![-139561541511442300, -43639014918709681, -5372533355362550], ![-1133604537981498050, -354462875725944300, -43639014918709681]]]
  hmulB := by decide  
  f := ![![![273960041, -15900550, -2194800]], ![![-463102800, 186168041, -15900550]], ![![46954689, -956139, -593971]]]
  g := ![![![125781553457261, 7345931706850, -661429106689300], ![1021675013397750, 59668168095611, -5372533355362550], ![8298671818805049, 484661500537251, -43639014918709681]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [30, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 78], [0, 1]]
 g := ![![[54, 10], [73, 13], [45, 18], [29, 5], [20], [1]], ![[49, 69], [27, 66], [36, 61], [66, 74], [20], [1]]]
 h' := ![![[39, 78], [22, 57], [72, 31], [78, 52], [63, 20], [49, 39], [0, 1]], ![[0, 1], [33, 22], [17, 48], [52, 27], [53, 59], [69, 40], [39, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [32, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [30, 40, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1759, 363, 14]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15, 3, 14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![273960041, -15900550, -2194800]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![273960041, -15900550, -2194800]] 
 ![![79, 0, 0], ![70, 1, 0], ![77, 0, 1]] where
  M :=![![![273960041, -15900550, -2194800], ![-463102800, 186168041, -15900550], ![-3355016050, -1099124800, 186168041]]]
  hmulB := by decide  
  f := ![![![-17181850651137681, -5372533355362550, -661429106689300]], ![![-16991026418874430, -5312865187266939, -654083174982450]], ![![-31096291621760753, -9723391697327350, -1197076659921339]]]
  g := ![![![19696179, -15900550, -2194800], ![-155323080, 186168041, -15900550], ![749984567, -1099124800, 186168041]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-17181850651137681, -5372533355362550, -661429106689300]] ![![273960041, -15900550, -2194800]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB276I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB276I1 : PrimesBelowBoundCertificateInterval O 31 79 276 where
  m := 11
  g := ![2, 1, 2, 2, 1, 3, 2, 1, 1, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB276I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
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
    · exact ![1369, 37]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![357911]
    · exact ![5329, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
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
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I43N1, I47N1, I59N0, I59N1, I59N2, I61N1, I73N1, I79N1]
  Il := ![[I37N1], [], [I43N1], [I47N1], [], [I59N0, I59N1, I59N2], [I61N1], [], [], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
