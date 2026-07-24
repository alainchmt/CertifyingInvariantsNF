
import IdealArithmetic.Examples.NF3_1_516660_1.RI3_1_516660_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-490622144936453668076, 5277817811358149563, 9603743531569120761]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-490622144936453668076, 5277817811358149563, 9603743531569120761]] 
 ![![37, 0, 0], ![0, 37, 0], ![21, 28, 1]] where
  M :=![![![-490622144936453668076, 5277817811358149563, 9603743531569120761], ![1901541219250685910678, -197232021178021895683, 31666906868148897378], ![728084390107132628361, 475258070882525472003, -202509838989380045246]]]
  hmulB := by decide  
  f := ![![![-672742480630761295164974976222210080132, -152245044844797128395896194653324504913, -55710754397461286109902184870044165421]], ![![-11030729370697334649760632604268744753358, -2496310157399397006857936716976859547675, -913470269068782770375377167919947029478]], ![![-9494434552889863956014131401644271872721, -2148638826740107896806478543334677690388, -786247526725059579926501273144675117351]]]
  g := ![![![-18710831327010951461, -7125054083042627885, 9603743531569120761], ![33419896622150245020, -29294740905032189791, 31666906868148897378], ![134615973213084150771, 166095501691490992943, -202509838989380045246]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [19, 24, 1] where
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
 g := ![![[11, 10], [11], [11, 1], [21], [1]], ![[30, 27], [11], [24, 36], [21], [1]]]
 h' := ![![[13, 36], [34, 26], [13, 14], [36, 1], [18, 13], [0, 1]], ![[0, 1], [2, 11], [10, 23], [12, 36], [2, 24], [13, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [26, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [19, 24, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4738, 5269, 3390]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1796, -2423, 3390]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-672742480630761295164974976222210080132, -152245044844797128395896194653324504913, -55710754397461286109902184870044165421]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-672742480630761295164974976222210080132, -152245044844797128395896194653324504913, -55710754397461286109902184870044165421]] 
 ![![37, 0, 0], ![17, 1, 0], ![23, 0, 1]] where
  M :=![![![-672742480630761295164974976222210080132, -152245044844797128395896194653324504913, -55710754397461286109902184870044165421], ![-11030729370697334649760632604268744753358, -2496310157399397006857936716976859547675, -913470269068782770375377167919947029478], ![-28306063984153608980760674440646794513881, -6405806240460136293503657940311192606283, -2344065112554599878462040522323535042762]]]
  hmulB := by decide  
  f := ![![![-490622144936453668076, 5277817811358149563, 9603743531569120761]], ![![-174027979585649363422, -2905651848241441976, 5268393159589836495]], ![![-285303376849494641551, 16125618393074673296, 496655736127290061]]]
  g := ![![![86399206293848634272784069862035738056, -152245044844797128395896194653324504913, -55710754397461286109902184870044165421], ![1416658364693903194201566660716125655003, -2496310157399397006857936716976859547675, -913470269068782770375377167919947029478], ![3635301072768229870633201150218507723688, -6405806240460136293503657940311192606283, -2344065112554599878462040522323535042762]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-490622144936453668076, 5277817811358149563, 9603743531569120761]] ![![-672742480630761295164974976222210080132, -152245044844797128395896194653324504913, -55710754397461286109902184870044165421]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![165284, 6915, -6623]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![165284, 6915, -6623]] 
 ![![41, 0, 0], ![0, 41, 0], ![5, 23, 1]] where
  M :=![![![165284, 6915, -6623], ![-1311354, -26491, 41490], ![1587729, -11109, -33406]]]
  hmulB := by decide  
  f := ![![![-32826116, -7428717, -2718377]], ![![-538238646, -121806143, -44572302]], ![![-339629243, -76859825, -28125177]]]
  g := ![![![4839, 3884, -6623], ![-37044, -23921, 41490], ![42799, 18469, -33406]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [6, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 40], [0, 1]]
 g := ![![[24, 31], [25], [21], [11, 31], [1]], ![[29, 10], [25], [21], [16, 10], [1]]]
 h' := ![![[20, 40], [22, 20], [7, 36], [16, 29], [35, 20], [0, 1]], ![[0, 1], [12, 21], [30, 5], [22, 12], [25, 21], [20, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [38, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [6, 21, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1042, 2612, 2078]
  a := ![-1, 1, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-228, -1102, 2078]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32826116, 7428717, 2718377]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![32826116, 7428717, 2718377]] 
 ![![41, 0, 0], ![26, 1, 0], ![6, 0, 1]] where
  M :=![![![32826116, 7428717, 2718377], ![538238646, 121806143, 44572302], ![1381179525, 312567951, 114377426]]]
  hmulB := by decide  
  f := ![![![-165284, -6915, 6623]], ![![-72830, -3739, 3188]], ![![-62913, -741, 1784]]]
  g := ![![![-4308068, 7428717, 2718377], ![-70637924, 121806143, 44572302], ![-181264677, 312567951, 114377426]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![165284, 6915, -6623]] ![![32826116, 7428717, 2718377]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-24, 4, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-24, 4, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![19, 4, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-24, 4, 1], ![198, 10, 24], ![759, 153, 6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -4, 43]], ![![-1, 0, 1], ![-6, -2, 24], ![15, 3, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [34, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 42], [0, 1]]
 g := ![![[18, 38], [14, 38], [14], [24, 14], [1]], ![[25, 5], [21, 5], [14], [13, 29], [1]]]
 h' := ![![[33, 42], [40, 34], [41, 9], [1, 10], [9, 33], [0, 1]], ![[0, 1], [1, 9], [37, 34], [30, 33], [23, 10], [33, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [17, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [34, 10, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3457, 33, 148]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15, -13, 148]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![19, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![19, 1, 0]] 
 ![![43, 0, 0], ![19, 1, 0], ![37, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![19, 1, 0], ![0, 20, 6], ![198, 30, 19]]]
  hmulB := by decide  
  f := ![![![305, 16, 0], ![-688, 0, 0]], ![![133, 7, 0], ![-300, 0, 0]], ![![243, 16, 1], ![-548, -7, 0]]]
  g := ![![![1, 0, 0], ![-19, 43, 0], ![-37, 0, 43]], ![![0, 1, 0], ![-14, 20, 6], ![-25, 30, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-24, 4, 1]] ![![43, 0, 0], ![19, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![817, 43, 0]], ![![-1032, 172, 43], ![-258, 86, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![19, 1, 0]]], ![![![-24, 4, 1]], ![![-6, 2, 1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![393870111957450452, 48205105158981147, -28146287873344557]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![393870111957450452, 48205105158981147, -28146287873344557]] 
 ![![47, 0, 0], ![0, 47, 0], ![31, 42, 1]] where
  M :=![![![393870111957450452, 48205105158981147, -28146287873344557], ![-5572964998922222286, -402313419083905111, 289230630953886882], ![10473438321298637487, 517325654949064029, -450518524242886258]]]
  hmulB := by decide  
  f := ![![![-672834516154046822814315723333980, -152265872951796974701977636505059, -55718375989052758756466778984741]], ![![-11032238445832446233780422238978718, -2496651668777426560210296729381269, -913595237710781848211865819030354]], ![![-10904719599203303261235099782594995, -2467793505241495149459925578028050, -903035222028491547486322417886767]]]
  g := ![![![26944788000662377, 26177642464669203, -28146287873344557], ![-309342862946653524, -267021274875471365, 289230630953886882], ![519989629209108755, 413597950492559295, -450518524242886258]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [14, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 46], [0, 1]]
 g := ![![[0, 37], [0, 9], [0, 17], [], [1]], ![[0, 10], [0, 38], [0, 30], [], [1]]]
 h' := ![![[0, 46], [0, 15], [0, 44], [0, 8], [33], [0, 1]], ![[0, 1], [0, 32], [0, 3], [0, 39], [33], [0, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [0, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [14, 0, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4734, 7137, 5068]
  a := ![1, -2, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3242, -4377, 5068]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-672834516154046822814315723333980, -152265872951796974701977636505059, -55718375989052758756466778984741]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-672834516154046822814315723333980, -152265872951796974701977636505059, -55718375989052758756466778984741]] 
 ![![47, 0, 0], ![30, 1, 0], ![33, 0, 1]] where
  M :=![![![-672834516154046822814315723333980, -152265872951796974701977636505059, -55718375989052758756466778984741], ![-11032238445832446233780422238978718, -2496651668777426560210296729381269, -913595237710781848211865819030354], ![-28309936436817059952028168321505229, -6406682596192650280022732801648223, -2344385795825629585508319092876210]]]
  hmulB := by decide  
  f := ![![![393870111957450452, 48205105158981147, -28146287873344557]], ![![132832731059601942, 22209356078415517, -11811872452052124]], ![![499386213104138349, 44853066493520040, -29347787746026737]]]
  g := ![![![121996767660395818238476959113069, -152265872951796974701977636505059, -55718375989052758756466778984741], ![2000339456637152160925958546180022, -2496651668777426560210296729381269, -913595237710781848211865819030354], ![5133090908749111165328262676443753, -6406682596192650280022732801648223, -2344385795825629585508319092876210]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![393870111957450452, 48205105158981147, -28146287873344557]] ![![-672834516154046822814315723333980, -152265872951796974701977636505059, -55718375989052758756466778984741]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [40, 19, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 5, 17], [39, 47, 36], [0, 1]]
 g := ![![[48, 26, 25], [15, 11], [52, 28, 38], [1, 40], [1]], ![[8, 0, 5, 9], [19, 52], [24, 40, 36, 29], [14, 11], [36, 43, 34, 37]], ![[33, 28, 6, 49], [22, 13], [13, 30, 38, 24], [18, 43], [26, 32, 0, 16]]]
 h' := ![![[41, 5, 17], [46, 49, 48], [40, 11, 45], [23, 7, 12], [13, 34, 27], [0, 1]], ![[39, 47, 36], [52, 39, 15], [21, 1, 23], [8, 10, 47], [12, 21, 45], [41, 5, 17]], ![[0, 1], [28, 18, 43], [22, 41, 38], [39, 36, 47], [32, 51, 34], [39, 47, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 39], []]
 b := ![[], [35, 52, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [40, 19, 26, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11578274, -3182120, -1226738]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-218458, -60040, -23146]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [43, 6, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 52, 4], [22, 6, 55], [0, 1]]
 g := ![![[58, 57, 25], [23, 51, 20], [5, 9], [50, 26, 36], [1]], ![[9, 41, 34, 28], [24, 19, 2, 53], [55, 25], [42, 40, 52, 45], [9, 19, 48, 5]], ![[2, 40, 41, 42], [12, 52, 50, 11], [3, 5], [8, 43, 42, 2], [18, 19, 22, 54]]]
 h' := ![![[43, 52, 4], [14, 32, 5], [48, 4, 43], [33, 18, 56], [16, 53, 6], [0, 1]], ![[22, 6, 55], [29, 32, 40], [44, 26, 38], [7, 39, 54], [1, 7, 12], [43, 52, 4]], ![[0, 1], [16, 54, 14], [46, 29, 37], [36, 2, 8], [21, 58, 41], [22, 6, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 24], []]
 b := ![[], [29, 58, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [43, 6, 53, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9383073319, 2645594928, 1053606542]
  a := ![1, 20, 101]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![159035141, 44840592, 17857738]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-32, -22, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-32, -22, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![29, 39, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-32, -22, 1], ![198, -24, -132], ![-4389, -627, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -39, 61]], ![![-1, -1, 1], ![66, 84, -132], ![-71, -9, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [30, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 60], [0, 1]]
 g := ![![[58, 42], [12], [44, 4], [36, 19], [29, 1]], ![[56, 19], [12], [38, 57], [38, 42], [58, 60]]]
 h' := ![![[29, 60], [2, 15], [22, 16], [18, 59], [45, 18], [0, 1]], ![[0, 1], [10, 46], [59, 45], [21, 2], [18, 43], [29, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [14, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [30, 32, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4454, 3817, 2724]
  a := ![-1, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1222, -1679, 2724]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![10, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![10, 1, 0]] 
 ![![61, 0, 0], ![10, 1, 0], ![2, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![10, 1, 0], ![0, 11, 6], ![198, 30, 10]]]
  hmulB := by decide  
  f := ![![![391, 39, 0], ![-2379, 0, 0]], ![![50, 5, 0], ![-304, 0, 0]], ![![2, -9, -5], ![-12, 51, 0]]]
  g := ![![![1, 0, 0], ![-10, 61, 0], ![-2, 0, 61]], ![![0, 1, 0], ![-2, 11, 6], ![-2, 30, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-32, -22, 1]] ![![61, 0, 0], ![10, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![610, 61, 0]], ![![-1952, -1342, 61], ![-122, -244, -122]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![10, 1, 0]]], ![![![-32, -22, 1]], ![![-2, -4, -2]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![5, 20, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![5, 20, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![5, 20, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![5, 20, 1], ![198, 55, 120], ![3927, 633, 35]]]
  hmulB := by decide  
  f := ![![![-4, -20, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -20, 67]], ![![0, 0, 1], ![-6, -35, 120], ![56, -1, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [46, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 66], [0, 1]]
 g := ![![[16, 14], [28, 64], [6], [40], [1], [1]], ![[30, 53], [25, 3], [6], [40], [1], [1]]]
 h' := ![![[1, 66], [52, 58], [48, 8], [18, 41], [60, 43], [21, 1], [0, 1]], ![[0, 1], [43, 9], [56, 59], [59, 26], [36, 24], [22, 66], [1, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [41, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [46, 66, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10705, 12804, 9846]
  a := ![0, 3, 17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-575, -2748, 9846]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![14, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![14, 1, 0]] 
 ![![67, 0, 0], ![14, 1, 0], ![32, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![14, 1, 0], ![0, 15, 6], ![198, 30, 14]]]
  hmulB := by decide  
  f := ![![![309, 22, 0], ![-1474, 0, 0]], ![![42, 3, 0], ![-200, 0, 0]], ![![148, -2, -5], ![-706, 56, 0]]]
  g := ![![![1, 0, 0], ![-14, 67, 0], ![-32, 0, 67]], ![![0, 1, 0], ![-6, 15, 6], ![-10, 30, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![5, 20, 1]] ![![67, 0, 0], ![14, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![938, 67, 0]], ![![335, 1340, 67], ![268, 335, 134]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![14, 1, 0]]], ![![![5, 20, 1]], ![![4, 5, 2]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-3, -11, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-3, -11, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![68, 60, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-3, -11, 1], ![198, 16, -66], ![-2211, -297, 27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -60, 71]], ![![-1, -1, 1], ![66, 56, -66], ![-57, -27, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [1, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 70], [0, 1]]
 g := ![![[12, 1], [59, 1], [], [], [2], [1]], ![[0, 70], [47, 70], [], [], [2], [1]]]
 h' := ![![[59, 70], [12, 1], [0, 1], [1], [70], [70, 59], [0, 1]], ![[0, 1], [0, 70], [59, 70], [1], [70], [1, 12], [59, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [6, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [1, 12, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![293, 33, 68]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-61, -57, 68]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-5, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-5, 1, 0]] 
 ![![71, 0, 0], ![66, 1, 0], ![44, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-5, 1, 0], ![0, -4, 6], ![198, 30, -5]]]
  hmulB := by decide  
  f := ![![![296, -59, 0], ![4189, 0, 0]], ![![276, -55, 0], ![3906, 0, 0]], ![![184, -36, -1], ![2604, 12, 0]]]
  g := ![![![1, 0, 0], ![-66, 71, 0], ![-44, 0, 71]], ![![-1, 1, 0], ![0, -4, 6], ![-22, 30, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-3, -11, 1]] ![![71, 0, 0], ![-5, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-355, 71, 0]], ![![-213, -781, 71], ![213, 71, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-5, 1, 0]]], ![![![-3, -11, 1]], ![![3, 1, -1]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![814148770119007145376782, 35217813019794029422029, -33073854004767830345195]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![814148770119007145376782, 35217813019794029422029, -33073854004767830345195]] 
 ![![73, 0, 0], ![0, 73, 0], ![48, 60, 1]] where
  M :=![![![814148770119007145376782, 35217813019794029422029, -33073854004767830345195], ![-6548623092944030408348610, -142849037004233735557039, 211306878118764176532174], ![8064564160076556226953177, -34902791563517518730565, -178066850024027764979068]]]
  hmulB := by decide  
  f := ![![![-449477780427760382506525034449418450513900794, -101719107694527897698492105157299309773568139, -37221889435388208187263298864404337613161417]], ![![-7369934108206865221078133175152058847405960566, -1667853571183934525822916105538847888682311443, -610314646167167386190952630943795858641408834]], ![![-6612096451028672938344149864675555296752836121, -1496351055103795321096397799960624145541251071, -547557040087918956062605756198639839764726320]]]
  g := ![![![32899914552710452081454, 27666425387751559590873, -33073854004767830345195], ![-228648674556776861395794, -175633722248357319554623, 211306878118764176532174], ![227558533715477930766417, 145878194655865046301555, -178066850024027764979068]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [60, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 72], [0, 1]]
 g := ![![[17, 2], [71], [1], [67, 23], [4], [1]], ![[21, 71], [71], [1], [40, 50], [4], [1]]]
 h' := ![![[2, 72], [31, 32], [38, 12], [68, 72], [2, 60], [13, 2], [0, 1]], ![[0, 1], [22, 41], [62, 61], [66, 1], [49, 13], [17, 71], [2, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [60, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [60, 71, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29304, 29768, 18532]
  a := ![1, -5, -26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11784, -14824, 18532]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![704729035612664117977624, 40998411832464924376569, -32725975100653073817713]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![704729035612664117977624, 40998411832464924376569, -32725975100653073817713]] 
 ![![73, 0, 0], ![5, 1, 0], ![68, 0, 1]] where
  M :=![![![704729035612664117977624, 40998411832464924376569, -32725975100653073817713], ![-6479743069929308615907174, -236051805574463172177197, 245990470994789546259414], ![9197642721149606462545191, 149995176652396295312541, -277050217406928096553766]]]
  hmulB := by decide  
  f := ![![![28500819902033318407368023677264800782196162928, 6449880495178800193744000580172302577542270121, 2360193125012317287698514197279481952983980105]], ![![8353730661131581027412957937639197679476833910, 1890491734568159427408047302420316093657112148, 691784227344306679465158554348372948358541387]], ![![42975968743263857802305298033121910398551194789, 9725680296615464239465246922837103521200189251, 3558900632236170035641402945351425098282550866]]]
  g := ![![![37330181962941760489031, 40998411832464924376569, -32725975100653073817713], ![-301737480406886053433717, -236051805574463172177197, 245990470994789546259414], ![373795638651489528104638, 149995176652396295312541, -277050217406928096553766]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![814148770119007145376782, 35217813019794029422029, -33073854004767830345195]] ![![704729035612664117977624, 40998411832464924376569, -32725975100653073817713]]
  ![![73, 0, 0]] where
 M := ![![![41350405210810343469501112256607127652773182677, 20104659644506934872518635749214700558031557750, -8817447524490459399269300492766334923593054190]]]
 hmul := by decide  
 g := ![![![![566443906997401965335631674748042844558536749, 275406296500094998253679941770064391205911750, -120786952390280265743415075243374451008124030]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![21, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![21, 1, 0]] 
 ![![79, 0, 0], ![21, 1, 0], ![2, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![21, 1, 0], ![0, 22, 6], ![198, 30, 21]]]
  hmulB := by decide  
  f := ![![![1177, 56, 0], ![-4424, 0, 0]], ![![315, 15, 0], ![-1184, 0, 0]], ![![8, -18, -5], ![-30, 66, 0]]]
  g := ![![![1, 0, 0], ![-21, 79, 0], ![-2, 0, 79]], ![![0, 1, 0], ![-6, 22, 6], ![-6, 30, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5603, 1268, 464]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![5603, 1268, 464]] 
 ![![79, 0, 0], ![36, 1, 0], ![15, 0, 1]] where
  M :=![![![5603, 1268, 464], ![91872, 20791, 7608], ![235752, 53352, 19523]]]
  hmulB := by decide  
  f := ![![![677, 164, -80]], ![![108, 55, -24]], ![![573, 60, -37]]]
  g := ![![![-595, 1268, 464], ![-9756, 20791, 7608], ![-25035, 53352, 19523]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![21, 1, 0]] ![![79, 0, 0], ![21, 1, 0]]
  ![![-677, -164, 80]] where
 M := ![![![6241, 0, 0], ![1659, 79, 0]], ![![1659, 79, 0], ![441, 43, 6]]]
 hmul := by decide  
 g := ![![![![-442637, -100172, -36656]], ![![-209535, -47419, -17352]]], ![![![-209535, -47419, -17352]], ![![-99189, -22447, -8214]]]]
 hle2 := by decide  
def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-677, -164, 80]] ![![5603, 1268, 464]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB204I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB204I1 : PrimesBelowBoundCertificateInterval O 31 79 204 where
  m := 11
  g := ![2, 2, 2, 2, 1, 1, 2, 2, 2, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB204I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N0, I79N1]
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
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![79, 79, 79]
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N1, I43N1, I47N1, I61N1, I67N1, I71N1, I73N1, I79N0, I79N1]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N1], [], [], [I61N1], [I67N1], [I71N1], [I73N1], [I79N0, I79N0, I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
