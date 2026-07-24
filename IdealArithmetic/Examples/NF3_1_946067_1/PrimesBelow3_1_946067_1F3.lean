
import IdealArithmetic.Examples.NF3_1_946067_1.RI3_1_946067_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![2, 1, 0]] 
 ![![139, 0, 0], ![2, 1, 0], ![135, 0, 1]] where
  M :=![![![2, 1, 0], ![0, 2, 1], ![211, 40, 2]]]
  hmulB := by decide  
  f := ![![![-36, -2, 1]], ![![1, 0, 0]], ![![-38, -1, 1]]]
  g := ![![![0, 1, 0], ![-1, 2, 1], ![-1, 40, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-80424474864, -96745682801, 13129638638]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-80424474864, -96745682801, 13129638638]] 
 ![![139, 0, 0], ![67, 1, 0], ![98, 0, 1]] where
  M :=![![![-80424474864, -96745682801, 13129638638], ![2770353752618, 444761070656, -96745682801], ![-20413339071011, -1099473559422, 444761070656]]]
  hmulB := by decide  
  f := ![![![-91443089743144187369314, -28593022936672044840220, -3520175002668441599073]], ![![-49420459988156127562219, -15453112421632437810266, -1902480202269479366749]], ![![-107874464996157782902728, -33730892739739448671617, -4152713957635893007492]]]
  g := ![![![36797350261, -96745682801, 13129638638], ![-126241446524, 444761070656, -96745682801], ![69530967525, -1099473559422, 444761070656]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9033545019845527778290, 2824667896474573051085, 347753553096934273994]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![9033545019845527778290, 2824667896474573051085, 347753553096934273994]] 
 ![![139, 0, 0], ![70, 1, 0], ![104, 0, 1]] where
  M :=![![![9033545019845527778290, 2824667896474573051085, 347753553096934273994], ![73375999703453131812734, 22943687143722898738050, 2824667896474573051085], ![596004926156134913778935, 186362715562436053856134, 22943687143722898738050]]]
  hmulB := by decide  
  f := ![![![-2609504802890, -251269705054, 70486405525]], ![![-1207141759975, -125028258530, 33689055264]], ![![-2333859045086, -153310834259, 54248471890]]]
  g := ![![![-1617694800398962232324, 2824667896474573051085, 347753553096934273994], ![-13139910515039607029954, 22943687143722898738050, 2824667896474573051085], ![-106730421770946549100055, 186362715562436053856134, 22943687143722898738050]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![2, 1, 0]] ![![-80424474864, -96745682801, 13129638638]]
  ![![2609504802890, 251269705054, -70486405525]] where
 M := ![![![2609504802890, 251269705054, -70486405525]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![2609504802890, 251269705054, -70486405525]] ![![9033545019845527778290, 2824667896474573051085, 347753553096934273994]]
  ![![139, 0, 0]] where
 M := ![![![-139, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-87915466, -22847421, 4145336]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-87915466, -22847421, 4145336]] 
 ![![149, 0, 0], ![0, 149, 0], ![28, 98, 1]] where
  M :=![![![-87915466, -22847421, 4145336], ![874665896, 77897974, -22847421], ![-4820805831, -39230944, 77897974]]]
  hmulB := by decide  
  f := ![![![34709855432948, 10853304446630, 1336183693973]], ![![281934759428303, 88157203191868, 10853304446630]], ![![207325702109632, 64827955534243, 7981169009348]]]
  g := ![![![-1369026, -2879801, 4145336], ![10163716, 15549968, -22847421], ![-46992947, -51498204, 77897974]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [5, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 148], [0, 1]]
 g := ![![[102, 30], [130], [32, 102], [133], [58, 81], [95], [1]], ![[0, 119], [130], [13, 47], [133], [21, 68], [95], [1]]]
 h' := ![![[86, 148], [67, 46], [138, 32], [144, 129], [8, 122], [146, 9], [144, 86], [0, 1]], ![[0, 1], [0, 103], [59, 117], [63, 20], [70, 27], [26, 140], [90, 63], [86, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [141]]
 b := ![[], [23, 145]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [5, 63, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![427, 228, -22]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, 16, -22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34709855432948, -10853304446630, -1336183693973]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-34709855432948, -10853304446630, -1336183693973]] 
 ![![149, 0, 0], ![51, 1, 0], ![81, 0, 1]] where
  M :=![![![-34709855432948, -10853304446630, -1336183693973], ![-281934759428303, -88157203191868, -10853304446630], ![-2290047238238930, -716066937293503, -88157203191868]]]
  hmulB := by decide  
  f := ![![![87915466, 22847421, -4145336]], ![![24221630, 7297453, -1265535]], ![![80147373, 12683705, -2776310]]]
  g := ![![![4208319131255, -10853304446630, -1336183693973], ![34182552104255, -88157203191868, -10853304446630], ![277651678001819, -716066937293503, -88157203191868]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-87915466, -22847421, 4145336]] ![![-34709855432948, -10853304446630, -1336183693973]]
  ![![149, 0, 0]] where
 M := ![![![-149, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [38, 45, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [98, 54, 109], [139, 96, 42], [0, 1]]
 g := ![![[61, 36, 25], [142, 130, 138], [69, 13, 44], [92, 62], [39, 116, 39], [86, 1], []], ![[134, 148, 38, 35], [7, 40, 111, 70], [97, 47, 147, 7], [8, 58], [98, 135, 59, 14], [55, 5], [94, 103]], ![[34, 22, 121, 124], [112, 100, 62, 58], [96, 107, 127, 36], [41, 17], [65, 133, 85, 32], [91, 47], [10, 103]]]
 h' := ![![[98, 54, 109], [40, 0, 146], [96, 61, 134], [6, 120, 73], [28, 75, 106], [54, 18, 103], [0, 0, 1], [0, 1]], ![[139, 96, 42], [80, 31, 124], [19, 17, 34], [8, 78, 5], [37, 101, 80], [88, 122, 72], [143, 24, 96], [98, 54, 109]], ![[0, 1], [12, 120, 32], [54, 73, 134], [62, 104, 73], [84, 126, 116], [143, 11, 127], [66, 127, 54], [139, 96, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104, 45], []]
 b := ![[], [66, 84, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [38, 45, 65, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![587692, 464778, 55568]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3892, 3078, 368]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀

instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-180976867903264, -15413086551285, 4640588016292]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-180976867903264, -15413086551285, 4640588016292]] 
 ![![157, 0, 0], ![0, 157, 0], ![152, 52, 1]] where
  M :=![![![-180976867903264, -15413086551285, 4640588016292], ![979164071437612, 4646652748416, -15413086551285], ![-3252161262321135, 362640609386212, 4646652748416]]]
  hmulB := by decide  
  f := ![![![35738869307291611989174468, 11175063230086533203583952, 1375796407498299106687629]], ![![290293041982141111511089719, 90770725607223576256679628, 11175063230086533203583952]], ![![145767418212279753674442028, 45579509004677588865901587, 5611433551028438006748820]]]
  g := ![![![-5645517492864, -1635182569417, 4640588016292], ![21158937753076, 5134567856148, -15413086551285], ![-25213073121531, 770794053940, 4646652748416]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [16, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 156], [0, 1]]
 g := ![![[122, 108], [47], [150, 16], [86, 75], [40, 132], [71], [1]], ![[0, 49], [47], [4, 141], [10, 82], [13, 25], [71], [1]]]
 h' := ![![[89, 156], [17, 118], [112, 19], [37, 4], [145, 111], [62, 17], [141, 89], [0, 1]], ![[0, 1], [0, 39], [76, 138], [79, 153], [133, 46], [5, 140], [55, 68], [89, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134]]
 b := ![[], [80, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [16, 68, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-662, 71, 101]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-102, -33, 101]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35738869307291611989174468, 11175063230086533203583952, 1375796407498299106687629]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![35738869307291611989174468, 11175063230086533203583952, 1375796407498299106687629]] 
 ![![157, 0, 0], ![105, 1, 0], ![122, 0, 1]] where
  M :=![![![35738869307291611989174468, 11175063230086533203583952, 1375796407498299106687629], ![290293041982141111511089719, 90770725607223576256679628, 11175063230086533203583952], ![2357938341548258505956213872, 737295571185602439654447799, 90770725607223576256679628]]]
  hmulB := by decide  
  f := ![![![-180976867903264, -15413086551285, 4640588016292]], ![![-114798771072644, -10278518695137, 3005405446875]], ![![-161346109213499, -9667235349494, 3635658539720]]]
  g := ![![![-8315222494054693410210390, 11175063230086533203583952, 1375796407498299106687629], ![-67541343062719053797945945, 90770725607223576256679628, 11175063230086533203583952], ![-548612262146632318223412227, 737295571185602439654447799, 90770725607223576256679628]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-180976867903264, -15413086551285, 4640588016292]] ![![35738869307291611989174468, 11175063230086533203583952, 1375796407498299106687629]]
  ![![157, 0, 0]] where
 M := ![![![157, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![985, 308, 38]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![985, 308, 38]] 
 ![![163, 0, 0], ![0, 163, 0], ![116, 51, 1]] where
  M :=![![![985, 308, 38], ![8018, 2505, 308], ![64988, 20338, 2505]]]
  hmulB := by decide  
  f := ![![![67, 8, -2]], ![![-422, -13, 8]], ![![-74, 1, 1]]]
  g := ![![![-21, -10, 38], ![-170, -81, 308], ![-1384, -659, 2505]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [107, 147, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 162], [0, 1]]
 g := ![![[140, 104], [145, 84], [111], [62], [136], [20, 93], [1]], ![[11, 59], [22, 79], [111], [62], [136], [41, 70], [1]]]
 h' := ![![[16, 162], [133, 58], [80, 128], [59, 33], [70, 148], [142, 25], [56, 16], [0, 1]], ![[0, 1], [83, 105], [9, 35], [98, 130], [156, 15], [53, 138], [149, 147], [16, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [125, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [107, 147, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1011, 1808, -86]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![55, 38, -86]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 8, -2]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![67, 8, -2]] 
 ![![163, 0, 0], ![112, 1, 0], ![7, 0, 1]] where
  M :=![![![67, 8, -2], ![-422, -13, 8], ![1688, -102, -13]]]
  hmulB := by decide  
  f := ![![![985, 308, 38]], ![![726, 227, 28]], ![![441, 138, 17]]]
  g := ![![![-5, 8, -2], ![6, -13, 8], ![81, -102, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![985, 308, 38]] ![![67, 8, -2]]
  ![![163, 0, 0]] where
 M := ![![![163, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1862387084781338, -1257668961179904, 183063377682129]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-1862387084781338, -1257668961179904, 183063377682129]] 
 ![![167, 0, 0], ![0, 167, 0], ![130, 62, 1]] where
  M :=![![![-1862387084781338, -1257668961179904, 183063377682129], ![38626372690929219, 5460148022503822, -1257668961179904], ![-265368150808959744, -11680385756266941, 5460148022503822]]]
  hmulB := by decide  
  f := ![![![90557831181961717560001532060, 28316214504062478530856888597, 3486096265098155169954789534]], ![![735566311935710740860460591674, 230001681785887924358193113420, 28316214504062478530856888597]], ![![379355393137881869378200954165, 118619323642822655097689249612, 14603589793416297996200256562]]]
  g := ![![![-153656444212324, -75494601062706, 183063377682129], ![1210319387091717, 499614512668610, -1257668961179904], ![-5839445471463812, -2097063252404215, 5460148022503822]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [119, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [152, 166], [0, 1]]
 g := ![![[31, 72], [64, 141], [96, 154], [48], [64], [28, 58], [1]], ![[120, 95], [120, 26], [124, 13], [48], [64], [160, 109], [1]]]
 h' := ![![[152, 166], [66, 78], [99, 108], [166, 133], [130, 81], [8, 159], [48, 152], [0, 1]], ![[0, 1], [65, 89], [149, 59], [8, 34], [84, 86], [128, 8], [106, 15], [152, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [30, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [119, 15, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![541, 276, 26]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17, -8, 26]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![90557831181961717560001532060, 28316214504062478530856888597, 3486096265098155169954789534]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![90557831181961717560001532060, 28316214504062478530856888597, 3486096265098155169954789534]] 
 ![![167, 0, 0], ![105, 1, 0], ![164, 0, 1]] where
  M :=![![![90557831181961717560001532060, 28316214504062478530856888597, 3486096265098155169954789534], ![735566311935710740860460591674, 230001681785887924358193113420, 28316214504062478530856888597], ![5974721260357182970010803493967, 1868214892098209882094736135554, 230001681785887924358193113420]]]
  hmulB := by decide  
  f := ![![![-1862387084781338, -1257668961179904, 183063377682129]], ![![-939666294677313, -758054448511294, 107568776619423]], ![![-3417961872533528, -1305018535268091, 212470311151934]]]
  g := ![![![-20684817240842490874566211103, 28316214504062478530856888597, 3486096265098155169954789534], ![-168014787151190226322217641002, 230001681785887924358193113420, 28316214504062478530856888597], ![-1364719270795451941584911145749, 1868214892098209882094736135554, 230001681785887924358193113420]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-1862387084781338, -1257668961179904, 183063377682129]] ![![90557831181961717560001532060, 28316214504062478530856888597, 3486096265098155169954789534]]
  ![![167, 0, 0]] where
 M := ![![![167, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19336439567720, -2308228798179, -8905969590]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![19336439567720, -2308228798179, -8905969590]] 
 ![![173, 0, 0], ![0, 173, 0], ![166, 44, 1]] where
  M :=![![![19336439567720, -2308228798179, -8905969590], ![-1879159583490, 18980200784120, -2308228798179], ![-487036276415769, -94208311510650, 18980200784120]]]
  hmulB := by decide  
  f := ![![![-825397018201207869277850, -258090534118870039822260, -31774319512938367564317]], ![![-6704381417229995556070887, -2096369798718742571850530, -258090534118870039822260]], ![![-2811940983113305717744156, -879256084331456051565779, -108247921035241579998304]]]
  g := ![![![120316939420, -11077260903, -8905969590], ![2203970063088, 696776115052, -2308228798179], ![-21027454373293, -5371891017410, 18980200784120]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [164, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 172], [0, 1]]
 g := ![![[124, 96], [16], [101, 34], [98, 64], [106], [33, 29], [1]], ![[0, 77], [16], [158, 139], [73, 109], [106], [46, 144], [1]]]
 h' := ![![[78, 172], [4, 31], [44, 169], [17, 42], [68, 165], [124, 148], [9, 78], [0, 1]], ![[0, 1], [0, 142], [78, 4], [6, 131], [136, 8], [77, 25], [38, 95], [78, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [141]]
 b := ![[], [105, 157]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [164, 95, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8278, 3574, 498]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-430, -106, 498]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-825397018201207869277850, -258090534118870039822260, -31774319512938367564317]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-825397018201207869277850, -258090534118870039822260, -31774319512938367564317]] 
 ![![173, 0, 0], ![129, 1, 0], ![140, 0, 1]] where
  M :=![![![-825397018201207869277850, -258090534118870039822260, -31774319512938367564317], ![-6704381417229995556070887, -2096369798718742571850530, -258090534118870039822260], ![-54457102699081578402496860, -17028002781984797148961287, -2096369798718742571850530]]]
  hmulB := by decide  
  f := ![![![19336439567720, -2308228798179, -8905969590]], ![![14407638986430, -1611452683127, -19983230493]], ![![12832747185347, -2412487533270, 102505000240]]]
  g := ![![![213391252109505194952590, -258090534118870039822260, -31774319512938367564317], ![1733294782625026599929271, -2096369798718742571850530, -258090534118870039822260], ![14078884554899313374986031, -17028002781984797148961287, -2096369798718742571850530]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![19336439567720, -2308228798179, -8905969590]] ![![-825397018201207869277850, -258090534118870039822260, -31774319512938367564317]]
  ![![173, 0, 0]] where
 M := ![![![173, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-169, -28, 6]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-169, -28, 6]] 
 ![![179, 0, 0], ![0, 179, 0], ![121, 55, 1]] where
  M :=![![![-169, -28, 6], ![1266, 71, -28], ![-5908, 146, 71]]]
  hmulB := by decide  
  f := ![![![-51, -16, -2]], ![![-422, -131, -16]], ![![-183, -57, -7]]]
  g := ![![![-5, -2, 6], ![26, 9, -28], ![-81, -21, 71]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [159, 86, 1] where
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
 g := ![![[121, 25], [57, 173], [25], [74], [111, 47], [71, 57], [1]], ![[119, 154], [36, 6], [25], [74], [7, 132], [2, 122], [1]]]
 h' := ![![[93, 178], [66, 5], [33, 50], [41, 5], [72, 130], [167, 88], [20, 93], [0, 1]], ![[0, 1], [173, 174], [29, 129], [148, 174], [169, 49], [117, 91], [77, 86], [93, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [145]]
 b := ![[], [164, 162]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [159, 86, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1192, 223, -35]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17, 12, -35]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, 16, 2]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![51, 16, 2]] 
 ![![179, 0, 0], ![124, 1, 0], ![18, 0, 1]] where
  M :=![![![51, 16, 2], ![422, 131, 16], ![3376, 1062, 131]]]
  hmulB := by decide  
  f := ![![![169, 28, -6]], ![![110, 19, -4]], ![![50, 2, -1]]]
  g := ![![![-11, 16, 2], ![-90, 131, 16], ![-730, 1062, 131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-169, -28, 6]] ![![51, 16, 2]]
  ![![179, 0, 0]] where
 M := ![![![-179, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1497838, 67186, 14431]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-1497838, 67186, 14431]] 
 ![![181, 0, 0], ![113, 1, 0], ![82, 0, 1]] where
  M :=![![![-1497838, 67186, 14431], ![3044941, -920598, 67186], ![14176246, 5732381, -920598]]]
  hmulB := by decide  
  f := ![![![-462364927738, -144575287439, -17799108334]], ![![-309408003828, -96747716805, -11910909001]], ![![-378007236045, -118197773072, -14551691406]]]
  g := ![![![-56758, 67186, 14431], ![561123, -920598, 67186], ![-3083391, 5732381, -920598]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![86966028371, 10697932012, -2635184576]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![86966028371, 10697932012, -2635184576]] 
 ![![181, 0, 0], ![117, 1, 0], ![67, 0, 1]] where
  M :=![![![86966028371, 10697932012, -2635184576], ![-556023945536, -18441354669, 10697932012], ![2257263654532, -128106665056, -18441354669]]]
  hmulB := by decide  
  f := ![![![-1710559955080992272233, -534869066296510140284, -65849375949079982800]], ![![-1182484713092441835481, -369747048341082198881, -45520696421761702364]], ![![-1256712099331437137235, -392956952591063322548, -48378139125041715093]]]
  g := ![![![-5459307461, 10697932012, -2635184576], ![4888691193, -18441354669, 10697932012], ![102106708447, -128106665056, -18441354669]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9980473645411395, -2911360280927870, 509698856122596]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-9980473645411395, -2911360280927870, 509698856122596]] 
 ![![181, 0, 0], ![132, 1, 0], ![133, 0, 1]] where
  M :=![![![-9980473645411395, -2911360280927870, 509698856122596], ![107546458641867756, 10407480599492445, -2911360280927870], ![-614297019275780570, -8907952595247044, 10407480599492445]]]
  hmulB := by decide  
  f := ![![![82381393058621039704827417361745, 25759552393697952836387084335926, 3171337728684997238149846949680]], ![![63776221792765257780590258553220, 19941965846266025986927715070117, 2455116754586285018078270064606]], ![![90563485258932963144860338696091, 28317982457802653358809852466838, 3486313923321135701131220661085]]]
  g := ![![![1693531135761117, -2911360280927870, 509698856122596], ![-4856519685788554, 10407480599492445, -2911360280927870], ![-4544984510694287, -8907952595247044, 10407480599492445]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-1497838, 67186, 14431]] ![![86966028371, 10697932012, -2635184576]]
  ![![-135043475009392302, -19111477227204626, 4399703665876581]] where
 M := ![![![-135043475009392302, -19111477227204626, 4399703665876581]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![-135043475009392302, -19111477227204626, 4399703665876581]] ![![-9980473645411395, -2911360280927870, 509698856122596]]
  ![![181, 0, 0]] where
 M := ![![![-3410298699529256076225845765189136, 155065529182283129575217130129606, 32598721516159721654298277601173]]]
 hmul := by decide  
 g := ![![![![-18841429279167160642131744559056, 856715630841343257321641602926, 180103433790937688697780539233]]]]
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
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [171, 128, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [108, 109, 75], [52, 81, 116], [0, 1]]
 g := ![![[120, 41, 149], [171, 97, 10], [80, 78, 135], [65, 158, 15], [106, 90, 92], [69, 160, 1], []], ![[86, 0, 118, 72], [57, 135, 15, 147], [99, 77, 42, 144], [132, 132, 128, 50], [48, 184, 145, 50], [146, 67, 54, 59], [123, 86]], ![[44, 60, 116, 119], [113, 58, 94, 176], [163, 136, 61, 14], [50, 81, 79, 28], [132, 77, 159, 112], [123, 149, 41, 131], [82, 86]]]
 h' := ![![[108, 109, 75], [173, 134, 63], [72, 138, 34], [154, 167, 138], [19, 13, 46], [43, 98, 130], [0, 0, 1], [0, 1]], ![[52, 81, 116], [72, 110, 64], [120, 79, 116], [2, 120, 19], [8, 37, 117], [159, 97, 117], [181, 161, 81], [108, 109, 75]], ![[0, 1], [43, 138, 64], [43, 165, 41], [166, 95, 34], [160, 141, 28], [106, 187, 135], [142, 30, 109], [52, 81, 116]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 168], []]
 b := ![[], [119, 32, 120], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [171, 128, 31, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![483994, 186798, 20819]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2534, 978, 109]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def PBC191 : ContainsPrimesAboveP 191 ![I191N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![191, 0, 0]]) timesTableT_eq_Table B_one_repr 191 (by decide) 𝕀

instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1665, -520, -64]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-1665, -520, -64]] 
 ![![193, 0, 0], ![0, 193, 0], ![23, 177, 1]] where
  M :=![![![-1665, -520, -64], ![-13504, -4225, -520], ![-109720, -34304, -4225]]]
  hmulB := by decide  
  f := ![![![-65, 8, 0]], ![![0, -65, 8]], ![![1, -57, 7]]]
  g := ![![![-1, 56, -64], ![-8, 455, -520], ![-65, 3697, -4225]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [89, 122, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 192], [0, 1]]
 g := ![![[151, 191], [100], [165], [62], [2], [110], [71, 1]], ![[9, 2], [100], [165], [62], [2], [110], [142, 192]]]
 h' := ![![[71, 192], [78, 159], [183, 183], [134, 101], [21, 86], [44, 52], [50, 127], [0, 1]], ![[0, 1], [173, 34], [52, 10], [164, 92], [144, 107], [69, 141], [189, 66], [71, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [182]]
 b := ![[], [147, 91]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [89, 122, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8103, -2016, 512]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-103, -480, 512]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65, -8, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![65, -8, 0]] 
 ![![193, 0, 0], ![16, 1, 0], ![130, 0, 1]] where
  M :=![![![65, -8, 0], ![0, 65, -8], ![-1688, -320, 65]]]
  hmulB := by decide  
  f := ![![![1665, 520, 64]], ![![208, 65, 8]], ![![1690, 528, 65]]]
  g := ![![![1, -8, 0], ![0, 65, -8], ![-26, -320, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-1665, -520, -64]] ![![65, -8, 0]]
  ![![193, 0, 0]] where
 M := ![![![-193, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)


lemma PB276I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB276I3 : PrimesBelowBoundCertificateInterval O 137 193 276 where
  m := 11
  g := ![3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB276I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0]
    · exact ![I193N0, I193N1]
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
    · exact PBC191
    · exact PBC193
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![139, 139, 139]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![181, 181, 181]
    · exact ![6967871]
    · exact ![37249, 193]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N0, I139N1, I139N2, I149N1, I157N1, I163N1, I167N1, I173N1, I179N1, I181N0, I181N1, I181N2, I193N1]
  Il := ![[I139N0, I139N1, I139N2], [I149N1], [], [I157N1], [I163N1], [I167N1], [I173N1], [I179N1], [I181N0, I181N1, I181N2], [], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
