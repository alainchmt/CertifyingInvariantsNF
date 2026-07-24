
import IdealArithmetic.Examples.NF3_1_946979_1.RI3_1_946979_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-313759879995, 183570805918, -148766123088]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-313759879995, 183570805918, -148766123088]] 
 ![![197, 0, 0], ![53, 1, 0], ![67, 0, 1]] where
  M :=![![![-313759879995, 183570805918, -148766123088], ![-27819265017456, 281304612357, 2019278865098], ![34327740706666, -3263307316168, 281304612357]]]
  hmulB := by decide  
  f := ![![![6668659778791041343399913, 433830263472194548958058, 412529245226347849848380]], ![![2185695112351534208740317, 142190592700060715932911, 135209050229393787210674]], ![![2679829768773097211487061, 174336567348203908790762, 165776661056096222760649]]]
  g := ![![![-384174349, 183570805918, -148766123088], ![-903655296619, 281304612357, 2019278865098], ![956525986983, -3263307316168, 281304612357]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101003, -39826, 29568]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![101003, -39826, 29568]] 
 ![![197, 0, 0], ![91, 1, 0], ![71, 0, 1]] where
  M :=![![![101003, -39826, 29568], ![5529216, -17269, -438086], ![-7447462, 661960, -17269]]]
  hmulB := by decide  
  f := ![![![-290293626921, -18885078086, -17957822828]], ![![-151141283851, -9832509855, -9349734702]], ![![-122550036109, -7972503654, -7581054601]]]
  g := ![![![8253, -39826, 29568], ![193933, -17269, -438086], ![-337359, 661960, -17269]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-313759879995, 183570805918, -148766123088]] ![![-313759879995, 183570805918, -148766123088]]
  ![![-10115164536307167715009191, 479511738234427576205100, 375508892979512953076108]] where
 M := ![![![-10115164536307167715009191, 479511738234427576205100, 375508892979512953076108]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI197N1 : IdealMulLeCertificate' Table 
  ![![-10115164536307167715009191, 479511738234427576205100, 375508892979512953076108]] ![![101003, -39826, 29568]]
  ![![197, 0, 0]] where
 M := ![![![-1166926199554013652066712554869, 643137721412117326022730620546, -515637227438560983333450507140]]]
 hmul := by decide  
 g := ![![![![-5923483246467074375973160177, 3264658484325468660013861018, -2617447855018076057530205620]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-301290978066098640, -19600511756787654, -18638128784199053]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-301290978066098640, -19600511756787654, -18638128784199053]] 
 ![![199, 0, 0], ![74, 1, 0], ![63, 0, 1]] where
  M :=![![![-301290978066098640, -19600511756787654, -18638128784199053], ![-3485330082645222911, -226738462929302428, -215605629324664194], ![-3665295698519291298, -238446142304233285, -226738462929302428]]]
  hmulB := by decide  
  f := ![![![-7424197894, 354544807, 273139808]], ![![-2504087940, 89043008, 121167531]], ![![-2017208987, 128449851, 43673622]]]
  g := ![![![11675120629852905, -19600511756787654, -18638128784199053], ![135057642319482417, -226738462929302428, -215605629324664194], ![142031366816784044, -238446142304233285, -226738462929302428]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N0)

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := prime_ideal_of_norm_prime hp199.out _ NI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-268968879, -349192, 22441558]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-268968879, -349192, 22441558]] 
 ![![199, 0, 0], ![137, 1, 0], ![139, 0, 1]] where
  M :=![![![-268968879, -349192, 22441558], ![4196571346, -358735111, -3841112], ![-65298904, 382903254, -358735111]]]
  hmulB := by decide  
  f := ![![![-130161654147960769, -8467678152149420, -8051916085724442]], ![![-97175150383422593, -6321738174118259, -6011341524713026]], ![![-98873998698585369, -6432256904509986, -6116433797591761]]]
  g := ![![![-16786463, -349192, 22441558], ![270739679, -358735111, -3841112], ![-13361127, 382903254, -358735111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12, 1, 0]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![-12, 1, 0]] 
 ![![199, 0, 0], ![187, 1, 0], ![5, 0, 1]] where
  M :=![![![-12, 1, 0], ![0, -12, 11], ![187, -4, -12]]]
  hmulB := by decide  
  f := ![![![-188, -12, -11]], ![![-187, -12, -11]], ![![-16, -1, -1]]]
  g := ![![![-1, 1, 0], ![11, -12, 11], ![5, -4, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-301290978066098640, -19600511756787654, -18638128784199053]] ![![-268968879, -349192, 22441558]]
  ![![188, 12, 11]] where
 M := ![![![188, 12, 11]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![188, 12, 11]] ![![-12, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![-199, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1, I199N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
    exact isPrimeI199N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0 ⊙ MulI199N1)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6570, -266, 793]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-6570, -266, 793]] 
 ![![211, 0, 0], ![0, 211, 0], ![104, 59, 1]] where
  M :=![![![-6570, -266, 793], ![148291, -9742, -2926], ![-49742, 14545, -9742]]]
  hmulB := by decide  
  f := ![![![-651494, -42383, -40302]], ![![-7536474, -490286, -466213]], ![![-2466033, -160428, -152551]]]
  g := ![![![-422, -223, 793], ![2145, 772, -2926], ![4566, 2793, -9742]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [168, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [124, 210], [0, 1]]
 g := ![![[155, 93], [198, 121], [144], [52], [161, 150], [45], [124, 1]], ![[82, 118], [10, 90], [144], [52], [193, 61], [45], [37, 210]]]
 h' := ![![[124, 210], [74, 127], [40, 200], [38, 12], [171, 91], [120, 19], [57, 16], [0, 1]], ![[0, 1], [208, 84], [153, 11], [49, 199], [61, 120], [155, 192], [142, 195], [124, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [126, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [168, 87, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![542, -78, -80]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![42, 22, -80]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![651494, 42383, 40302]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![651494, 42383, 40302]] 
 ![![211, 0, 0], ![195, 1, 0], ![111, 0, 1]] where
  M :=![![![651494, 42383, 40302], ![7536474, 490286, 466213], ![7925621, 515602, 490286]]]
  hmulB := by decide  
  f := ![![![6570, 266, -793]], ![![5369, 292, -719]], ![![3692, 71, -371]]]
  g := ![![![-57283, 42383, 40302], ![-662649, 490286, 466213], ![-696865, 515602, 490286]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-6570, -266, 793]] ![![651494, 42383, 40302]]
  ![![211, 0, 0]] where
 M := ![![![-211, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1124012016240300770856442, 73122703110795768707153, 69532386426380039309532]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![1124012016240300770856442, 73122703110795768707153, 69532386426380039309532]] 
 ![![223, 0, 0], ![0, 223, 0], ![151, 71, 1]] where
  M :=![![![1124012016240300770856442, 73122703110795768707153, 69532386426380039309532], ![13002556261733067350882484, 845882470534780613618314, 804349734218753455778683], ![13673945481718808748237611, 889559756805277593433432, 845882470534780613618314]]]
  hmulB := by decide  
  f := ![![![-383496901020, -43240800566, 72641511437]], ![![13583962638719, -674062946768, -475648806226]], ![![4029001280669, -237578301387, -105274708349]]]
  g := ![![![-42042055310058677869430, -21810209565749717588653, 69532386426380039309532], ![-486341944418379840680263, -252300218201778989895373, 804349734218753455778683], ![-511454294031538403175461, -265327783189076887773394, 845882470534780613618314]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [29, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [203, 222], [0, 1]]
 g := ![![[216, 100], [70, 115], [27, 124], [151, 41], [15, 89], [50], [203, 1]], ![[0, 123], [0, 108], [0, 99], [0, 182], [19, 134], [50], [183, 222]]]
 h' := ![![[203, 222], [200, 10], [109, 195], [81, 149], [11, 34], [4, 85], [134, 148], [0, 1]], ![[0, 1], [0, 213], [0, 28], [0, 74], [0, 189], [88, 138], [73, 75], [203, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [201]]
 b := ![[], [113, 212]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [29, 20, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2234, 165, 62]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-52, -19, 62]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![383496901020, 43240800566, -72641511437]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![383496901020, 43240800566, -72641511437]] 
 ![![223, 0, 0], ![111, 1, 0], ![76, 0, 1]] where
  M :=![![![383496901020, 43240800566, -72641511437], ![-13583962638719, 674062946768, 475648806226], ![8086029705842, -1407868896693, 674062946768]]]
  hmulB := by decide  
  f := ![![![-1124012016240300770856442, -73122703110795768707153, -69532386426380039309532]], ![![-617793228988369744017702, -40190594241404084933239, -38217240482273263762945]], ![![-444389500968527656203261, -28909799072761237736220, -27490331116321361440102]]]
  g := ![![![4953017522, 43240800566, -72641511437], ![-558539278041, 674062946768, 475648806226], ![507312525939, -1407868896693, 674062946768]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![1124012016240300770856442, 73122703110795768707153, 69532386426380039309532]] ![![383496901020, 43240800566, -72641511437]]
  ![![223, 0, 0]] where
 M := ![![![-223, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1442264108, 255272477, -124183072]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-1442264108, 255272477, -124183072]] 
 ![![227, 0, 0], ![12, 1, 0], ![152, 0, 1]] where
  M :=![![![-1442264108, 255272477, -124183072], ![-23222234464, -945531820, 2807997247], ![47735953199, -3132202132, -945531820]]]
  hmulB := by decide  
  f := ![![![-9689245386336043004, -630334732650427644, -599385366569519779]], ![![-1005973604337148523, -65443703576489408, -62230424925061416]], ![![-7007215390875367868, -455855029356586465, -433472597526982248]]]
  g := ![![![63305256, 255272477, -124183072], ![-1932561384, -945531820, 2807997247], ![1009000949, -3132202132, -945531820]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N0 : Nat.card (O ⧸ I227N0) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N0)

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := prime_ideal_of_norm_prime hp227.out _ NI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6423735270903804308181870567, -417896677517569543102219110, -397377996590527683864959386]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![-6423735270903804308181870567, -417896677517569543102219110, -397377996590527683864959386]] 
 ![![227, 0, 0], ![17, 1, 0], ![15, 0, 1]] where
  M :=![![![-6423735270903804308181870567, -417896677517569543102219110, -397377996590527683864959386], ![-74309685362428676882747405182, -4834223284541693572722033023, -4596863452693264974124410210], ![-78146678695785504560114973570, -5083839231968692453295433122, -4834223284541693572722033023]]]
  hmulB := by decide  
  f := ![![![-1019143553542909, 17146192486438, 67470304690778]], ![![-20742261819621, -4394447136725, 5883714965172]], ![![-53219450696827, 5883714965172, -1220133048213]]]
  g := ![![![29256291611245784945067159, -417896677517569543102219110, -397377996590527683864959386], ![338436397643960742138296517, -4834223284541693572722033023, -4596863452693264974124410210], ![355911619012368593553911387, -5083839231968692453295433122, -4834223284541693572722033023]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1

def I227N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![36886, -17738, 13835]] i)))

def SI227N2: IdealEqSpanCertificate' Table ![![36886, -17738, 13835]] 
 ![![227, 0, 0], ![198, 1, 0], ![68, 0, 1]] where
  M :=![![![36886, -17738, 13835], ![2587145, -18454, -195118], ![-3317006, 306147, -18454]]]
  hmulB := by decide  
  f := ![![![-60075340462, -3908206693, -3716314174]], ![![-55461974282, -3608083740, -3430927225]], ![![-21215673141, -1380187530, -1312420474]]]
  g := ![![![11490, -17738, 13835], ![85943, -18454, -195118], ![-276120, 306147, -18454]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N2 : Nat.card (O ⧸ I227N2) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N2)

lemma isPrimeI227N2 : Ideal.IsPrime I227N2 := prime_ideal_of_norm_prime hp227.out _ NI227N2
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-1442264108, 255272477, -124183072]] ![![-6423735270903804308181870567, -417896677517569543102219110, -397377996590527683864959386]]
  ![![60075340462, 3908206693, 3716314174]] where
 M := ![![![60075340462, 3908206693, 3716314174]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI227N1 : IdealMulLeCertificate' Table 
  ![![60075340462, 3908206693, 3716314174]] ![![36886, -17738, 13835]]
  ![![227, 0, 0]] where
 M := ![![![-227, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1, I227N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
    exact isPrimeI227N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0 ⊙ MulI227N1)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0]] 
 ![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [190, 206, 184, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 32, 29], [225, 196, 200], [0, 1]]
 g := ![![[13, 183, 148], [20, 99], [53, 227, 169], [37, 43], [43, 108], [103, 221, 193], [1]], ![[41, 157, 223, 13], [143, 186], [28, 164, 60, 182], [150, 172], [82, 172], [215, 48, 191, 52], [158, 117, 36, 115]], ![[179, 168, 16, 208], [127, 17], [190, 88, 205, 216], [38, 43], [197, 19], [102, 4, 67, 89], [214, 182, 189, 114]]]
 h' := ![![[49, 32, 29], [129, 221, 47], [6, 40, 102], [68, 90, 216], [107, 132, 57], [124, 143, 32], [39, 23, 45], [0, 1]], ![[225, 196, 200], [0, 163, 49], [47, 26, 84], [64, 211, 62], [175, 196, 115], [99, 101, 114], [151, 75, 98], [49, 32, 29]], ![[0, 1], [139, 74, 133], [37, 163, 43], [99, 157, 180], [137, 130, 57], [34, 214, 83], [38, 131, 86], [225, 196, 200]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [208, 33], []]
 b := ![[], [2, 146, 141], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [190, 206, 184, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![478152, -11679, 11679]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2088, -51, 51]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 12008989 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def PBC229 : ContainsPrimesAboveP 229 ![I229N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![229, 0, 0]]) timesTableT_eq_Table B_one_repr 229 (by decide) 𝕀

instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16509925382227118004761929042122, 1074054685059424430270500549261, 1021318718093039022278765869658]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![16509925382227118004761929042122, 1074054685059424430270500549261, 1021318718093039022278765869658]] 
 ![![233, 0, 0], ![0, 233, 0], ![202, 22, 1]] where
  M :=![![![16509925382227118004761929042122, 1074054685059424430270500549261, 1021318718093039022278765869658], ![190986600283398297166129217626046, 12424650509854961915646865563490, 11814601535653668732975506041871], ![200848226106112368460583602711807, 13066199467343965657657017587142, 12424650509854961915646865563490]]]
  hmulB := by decide  
  f := ![![![3132470849689946, -327239617336238, 53679946354167]], ![![10038149968229229, 2917751064273278, -3599635790698618]], ![![3400878122302728, 1328919611407, -280819258229848]]]
  g := ![![![-814577062972389547191196466218, -91823850270332335020868448855, 1021318718093039022278765869658], ![-9423016780766707239892373402712, -1062217095598822962273880975784, 11814601535653668732975506041871], ![-9909575866457467547210657687181, -1117064857293842045006755471286, 12424650509854961915646865563490]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [159, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [145, 232], [0, 1]]
 g := ![![[24, 85], [220], [33], [192, 196], [214], [64, 98], [145, 1]], ![[0, 148], [220], [33], [186, 37], [214], [61, 135], [57, 232]]]
 h' := ![![[145, 232], [99, 205], [137, 176], [228, 158], [176, 219], [76, 133], [12, 129], [0, 1]], ![[0, 1], [0, 28], [27, 57], [71, 75], [10, 14], [22, 100], [77, 104], [145, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [19, 154]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [159, 88, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-874, 267, -295]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![252, 29, -295]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3132470849689946, 327239617336238, -53679946354167]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-3132470849689946, 327239617336238, -53679946354167]] 
 ![![233, 0, 0], ![224, 1, 0], ![35, 0, 1]] where
  M :=![![![-3132470849689946, 327239617336238, -53679946354167], ![-10038149968229229, -2917751064273278, 3599635790698618], ![61193808441876506, -2221517557365791, -2917751064273278]]]
  hmulB := by decide  
  f := ![![![-16509925382227118004761929042122, -1074054685059424430270500549261, -1021318718093039022278765869658]], ![![-16691887922327350773531336150478, -1085892274520025898267120122738, -1032575083212422359327978801911]], ![![-3342041263880092268786485490069, -217416795898814681189375694469, -206741655120649475087569403440]]]
  g := ![![![-319980030088461, 327239617336238, -53679946354167], ![2221248222122461, -2917751064273278, 3599635790698618], ![2836631023782740, -2221517557365791, -2917751064273278]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![16509925382227118004761929042122, 1074054685059424430270500549261, 1021318718093039022278765869658]] ![![-3132470849689946, 327239617336238, -53679946354167]]
  ![![233, 0, 0]] where
 M := ![![![-233, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17014, -1353, -112]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![17014, -1353, -112]] 
 ![![239, 0, 0], ![0, 239, 0], ![6, 202, 1]] where
  M :=![![![17014, -1353, -112], ![-20944, 17462, -14883], ![-253011, 3508, 17462]]]
  hmulB := by decide  
  f := ![![![-1494272, -97210, -92437]], ![![-17285719, -1124524, -1069310]], ![![-14723260, -957823, -910794]]]
  g := ![![![74, 89, -112], ![286, 12652, -14883], ![-1497, -14744, 17462]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [154, 158, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 238], [0, 1]]
 g := ![![[60, 162], [185, 3], [222, 66], [228, 180], [68], [202, 204], [81, 1]], ![[37, 77], [189, 236], [71, 173], [229, 59], [68], [235, 35], [162, 238]]]
 h' := ![![[81, 238], [190, 65], [228, 133], [21, 117], [54, 53], [201, 207], [193, 193], [0, 1]], ![[0, 1], [197, 174], [7, 106], [177, 122], [45, 186], [238, 32], [52, 46], [81, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [69, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [154, 158, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![528, -149, -151]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, 127, -151]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1494272, -97210, -92437]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-1494272, -97210, -92437]] 
 ![![239, 0, 0], ![168, 1, 0], ![237, 0, 1]] where
  M :=![![![-1494272, -97210, -92437], ![-17285719, -1124524, -1069310], ![-18178270, -1182589, -1124524]]]
  hmulB := by decide  
  f := ![![![17014, -1353, -112]], ![![11872, -878, -141]], ![![15813, -1327, -38]]]
  g := ![![![153743, -97210, -92437], ![1778497, -1124524, -1069310], ![1870330, -1182589, -1124524]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![17014, -1353, -112]] ![![-1494272, -97210, -92437]]
  ![![239, 0, 0]] where
 M := ![![![239, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14034, 379, -1514]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![14034, 379, -1514]] 
 ![![241, 0, 0], ![41, 1, 0], ![132, 0, 1]] where
  M :=![![![14034, 379, -1514], ![-283118, 20090, 4169], ![70873, -27254, 20090]]]
  hmulB := by decide  
  f := ![![![-517230026, -33648446, -31996311]], ![![-112820503, -7339548, -6979177]], ![![-309405074, -20128375, -19140074]]]
  g := ![![![823, 379, -1514], ![-6876, 20090, 4169], ![-6073, -27254, 20090]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N0 : Nat.card (O ⧸ I241N0) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N0)

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := prime_ideal_of_norm_prime hp241.out _ NI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3803895640, -247462774, -235312379]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![-3803895640, -247462774, -235312379]] 
 ![![241, 0, 0], ![91, 1, 0], ![14, 0, 1]] where
  M :=![![![-3803895640, -247462774, -235312379], ![-44003414873, -2862646124, -2722090514], ![-46275538738, -3010459347, -2862646124]]]
  hmulB := by decide  
  f := ![![![-889018, 31463, 43160]], ![![-302198, 7475, 17733]], ![![-27231, 4350, -1898]]]
  g := ![![![91326100, -247462774, -235312379], ![1056459127, -2862646124, -2722090514], ![1111009575, -3010459347, -2862646124]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, 2, 0]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![-23, 2, 0]] 
 ![![241, 0, 0], ![109, 1, 0], ![103, 0, 1]] where
  M :=![![![-23, 2, 0], ![0, -23, 22], ![374, -8, -23]]]
  hmulB := by decide  
  f := ![![![705, 46, 44]], ![![353, 23, 22]], ![![337, 22, 21]]]
  g := ![![![-1, 2, 0], ![1, -23, 22], ![15, -8, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![14034, 379, -1514]] ![![-3803895640, -247462774, -235312379]]
  ![![705, 46, 44]] where
 M := ![![![705, 46, 44]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![705, 46, 44]] ![![-23, 2, 0]]
  ![![241, 0, 0]] where
 M := ![![![241, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1, I241N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
    exact isPrimeI241N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0 ⊙ MulI241N1)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1139828197986, -74151626241, -70510789544]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![-1139828197986, -74151626241, -70510789544]] 
 ![![251, 0, 0], ![0, 251, 0], ![130, 199, 1]] where
  M :=![![![-1139828197986, -74151626241, -70510789544], ![-13185517644728, -857785039810, -815667888651], ![-13866354107067, -902076917284, -857785039810]]]
  hmulB := by decide  
  f := ![![![-938216, 22214, 55999]], ![![10471813, -1162212, 244354]], ![![7832975, -906491, 218104]]]
  g := ![![![31978384234, 55607551765, -70510789544], ![369925529402, 643267429489, -815667888651], ![389026697483, 676482653406, -857785039810]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [160, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [194, 250], [0, 1]]
 g := ![![[209, 204], [126, 179], [64], [199, 100], [249, 60], [28, 156], [194, 1]], ![[127, 47], [214, 72], [64], [21, 151], [92, 191], [172, 95], [137, 250]]]
 h' := ![![[194, 250], [171, 188], [165, 207], [37, 8], [69, 241], [38, 78], [84, 77], [0, 1]], ![[0, 1], [248, 63], [163, 44], [83, 243], [137, 10], [110, 173], [213, 174], [194, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [218]]
 b := ![[], [220, 109]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [160, 57, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7324, 986, 4026]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2056, -3188, 4026]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-938216, 22214, 55999]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![-938216, 22214, 55999]] 
 ![![251, 0, 0], ![70, 1, 0], ![125, 0, 1]] where
  M :=![![![-938216, 22214, 55999], ![10471813, -1162212, 244354], ![4154018, 863127, -1162212]]]
  hmulB := by decide  
  f := ![![![-1139828197986, -74151626241, -70510789544]], ![![-370412316748, -24097206680, -22914036481]], ![![-622887963567, -40522032659, -38532405310]]]
  g := ![![![-37821, 22214, 55999], ![244153, -1162212, 244354], ![354628, 863127, -1162212]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![-1139828197986, -74151626241, -70510789544]] ![![-938216, 22214, 55999]]
  ![![251, 0, 0]] where
 M := ![![![251, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0)
instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2669659989976, 64273750263, 158330809272]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![-2669659989976, 64273750263, 158330809272]] 
 ![![257, 0, 0], ![0, 257, 0], ![36, 79, 1]] where
  M :=![![![-2669659989976, 64273750263, 158330809272], ![29607861333864, -3302983227064, 707011252893], ![12019191299181, 2434528756572, -3302983227064]]]
  hmulB := by decide  
  f := ![![![-35752758645440109938900, -2325898938845097304488, -2211697556632142687931]], ![![-413587443090210682643097, -26905968418911539187176, -25584888327296070349368]], ![![-133834437419947552850367, -8706611399221016090371, -8279117736630576784252]]]
  g := ![![![-32566416824, -48419689425, 158330809272], ![16169090388, -230182382123, 707011252893], ![509441974605, 1024786784804, -3302983227064]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [22, 256, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 256], [0, 1]]
 g := ![![[35, 222], [227], [73], [62], [22], [50], [1], [1]], ![[0, 35], [227], [73], [62], [22], [50], [1], [1]]]
 h' := ![![[1, 256], [42, 215], [47, 235], [25, 178], [19, 233], [62, 153], [205, 214], [235, 1], [0, 1]], ![[0, 1], [0, 42], [25, 22], [203, 79], [252, 24], [215, 104], [162, 43], [236, 256], [1, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [192, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [22, 256, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1355, 803, -159]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17, 52, -159]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35752758645440109938900, -2325898938845097304488, -2211697556632142687931]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![-35752758645440109938900, -2325898938845097304488, -2211697556632142687931]] 
 ![![257, 0, 0], ![159, 1, 0], ![225, 0, 1]] where
  M :=![![![-35752758645440109938900, -2325898938845097304488, -2211697556632142687931], ![-413587443090210682643097, -26905968418911539187176, -25584888327296070349368], ![-434943101564033195939256, -28295262707366036476875, -26905968418911539187176]]]
  hmulB := by decide  
  f := ![![![-2669659989976, 64273750263, 158330809272]], ![![-1536451661760, 26912618929, 100706653413]], ![![-2290483682667, 65743667571, 125764392448]]]
  g := ![![![3236175575381955121631, -2325898938845097304488, -2211697556632142687931], ![37436036611511050103991, -26905968418911539187176, -25584888327296070349368], ![39369052774950439381317, -28295262707366036476875, -26905968418911539187176]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![-2669659989976, 64273750263, 158330809272]] ![![-35752758645440109938900, -2325898938845097304488, -2211697556632142687931]]
  ![![257, 0, 0]] where
 M := ![![![257, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0)


lemma PB276I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB276I4 : PrimesBelowBoundCertificateInterval O 193 257 276 where
  m := 11
  g := ![3, 3, 2, 2, 3, 1, 2, 2, 3, 2, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB276I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N0, I197N1]
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1, I227N2]
    · exact ![I229N0]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1, I241N2]
    · exact ![I251N0, I251N1]
    · exact ![I257N0, I257N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
    · exact PBC257
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![197, 197, 197]
    · exact ![199, 199, 199]
    · exact ![44521, 211]
    · exact ![49729, 223]
    · exact ![227, 227, 227]
    · exact ![12008989]
    · exact ![54289, 233]
    · exact ![57121, 239]
    · exact ![241, 241, 241]
    · exact ![63001, 251]
    · exact ![66049, 257]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N0
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
      exact NI199N2
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
      exact NI227N2
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
      exact NI241N2
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
  β := ![I197N0, I197N1, I199N0, I199N1, I199N2, I211N1, I223N1, I227N0, I227N1, I227N2, I233N1, I239N1, I241N0, I241N1, I241N2, I251N1, I257N1]
  Il := ![[I197N0, I197N0, I197N1], [I199N0, I199N1, I199N2], [I211N1], [I223N1], [I227N0, I227N1, I227N2], [], [I233N1], [I239N1], [I241N0, I241N1, I241N2], [I251N1], [I257N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
