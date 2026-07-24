
import IdealArithmetic.Examples.NF3_1_981215_1.RI3_1_981215_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13260449287207, 856662285579, 744443374314]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![13260449287207, 856662285579, 744443374314]] 
 ![![37, 0, 0], ![16, 1, 0], ![16, 0, 1]] where
  M :=![![![13260449287207, 856662285579, 744443374314], ![141332022208395, 9130445775118, 7934398392741], ![99600366354585, 6434463541755, 5591577721537]]]
  hmulB := by decide  
  f := ![![![-15084089, 666147, 1062987]], ![![-1053542, -324167, 600255]], ![![-5554817, 671886, -213851]]]
  g := ![![![-333979493813, 856662285579, 744443374314], ![-3559607688577, 9130445775118, 7934398392741], ![-2508548482651, 6434463541755, 5591577721537]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, -21, 29]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![6, -21, 29]] 
 ![![37, 0, 0], ![27, 1, 0], ![7, 0, 1]] where
  M :=![![![6, -21, 29], ![5560, -318, -289], ![-6505, 740, -184]]]
  hmulB := by decide  
  f := ![![![272372, 17596, 15291]], ![![277217, 17909, 15563]], ![![106822, 6901, 5997]]]
  g := ![![![10, -21, 29], ![437, -318, -289], ![-681, 740, -184]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18761, -2126, 519]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![18761, -2126, 519]] 
 ![![37, 0, 0], ![30, 1, 0], ![31, 0, 1]] where
  M :=![![![18761, -2126, 519], ![101255, 7712, -24424], ![-450700, 28995, 18861]]]
  hmulB := by decide  
  f := ![![![853629912, 55146891, 47922896]], ![![938027665, 60599223, 52660997]], ![![888492281, 57399098, 49880074]]]
  g := ![![![1796, -2126, 519], ![16947, 7712, -24424], ![-51493, 28995, 18861]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![13260449287207, 856662285579, 744443374314]] ![![6, -21, 29]]
  ![![853629912, 55146891, 47922896]] where
 M := ![![![853629912, 55146891, 47922896]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![853629912, 55146891, 47922896]] ![![18761, -2126, 519]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4933405, 517726, -77832]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-4933405, 517726, -77832]] 
 ![![41, 0, 0], ![0, 41, 0], ![35, 25, 1]] where
  M :=![![![-4933405, 517726, -77832], ![-15383638, -2679739, 5850650], ![105579218, -6138342, -5346201]]]
  hmulB := by decide  
  f := ![![![1225358876679, 79161626670, 68791809172]], ![![13060073925182, 843717474141, 733194275026]], ![![9233980095573, 596541061493, 518396862113]]]
  g := ![![![-53885, 60086, -77832], ![-5369668, -3632829, 5850650], ![7138933, 3110163, -5346201]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [28, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 40], [0, 1]]
 g := ![![[22, 36], [25], [16], [14, 1], [1]], ![[27, 5], [25], [16], [13, 40], [1]]]
 h' := ![![[40, 40], [39, 6], [40, 5], [18, 4], [13, 40], [0, 1]], ![[0, 1], [33, 35], [35, 36], [14, 37], [14, 1], [40, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [17, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [28, 1, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6416, 1543, -1001]
  a := ![1, -4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1011, 648, -1001]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1225358876679, -79161626670, -68791809172]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-1225358876679, -79161626670, -68791809172]] 
 ![![41, 0, 0], ![14, 1, 0], ![23, 0, 1]] where
  M :=![![![-1225358876679, -79161626670, -68791809172], ![-13060073925182, -843717474141, -733194275026], ![-9203775105178, -594589734238, -516701149963]]]
  hmulB := by decide  
  f := ![![![4933405, -517726, 77832]], ![![2059788, -111425, -116122]], ![![192417, -140716, 174057]]]
  g := ![![![35734524577, -79161626670, -68791809172], ![380864366790, -843717474141, -733194275026], ![268405063983, -594589734238, -516701149963]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-4933405, 517726, -77832]] ![![-1225358876679, -79161626670, -68791809172]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2928, 757, -1464]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![2928, 757, -1464]] 
 ![![43, 0, 0], ![0, 43, 0], ![41, 30, 1]] where
  M :=![![![2928, 757, -1464], ![-280381, 18375, 11255], ![270491, -34629, 13126]]]
  hmulB := by decide  
  f := ![![![-14673015, -947918, -823745]], ![![-156387377, -10103064, -8779608]], ![![-125661051, -8118057, -7054628]]]
  g := ![![![1464, 1039, -1464], ![-17252, -7425, 11255], ![-6225, -9963, 13126]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [15, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 42], [0, 1]]
 g := ![![[21, 23], [34, 25], [11], [41, 24], [1]], ![[0, 20], [28, 18], [11], [6, 19], [1]]]
 h' := ![![[29, 42], [6, 25], [4, 5], [30, 22], [28, 29], [0, 1]], ![[0, 1], [0, 18], [20, 38], [23, 21], [9, 14], [29, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [41, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [15, 14, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14774, 16156, -8308]
  a := ![-3, 6, 32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7578, 6172, -8308]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14673015, 947918, 823745]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![14673015, 947918, 823745]] 
 ![![43, 0, 0], ![16, 1, 0], ![27, 0, 1]] where
  M :=![![![14673015, 947918, 823745], ![156387377, 10103064, 8779608], ![110210268, 7119893, 6187219]]]
  hmulB := by decide  
  f := ![![![-2928, -757, 1464]], ![![5431, -709, 283]], ![![-8129, 330, 614]]]
  g := ![![![-528716, 947918, 823745], ![-5635141, 10103064, 8779608], ![-3971231, 7119893, 6187219]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![2928, 757, -1464]] ![![14673015, 947918, 823745]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-495706, -32024, -27829]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-495706, -32024, -27829]] 
 ![![47, 0, 0], ![7, 1, 0], ![32, 0, 1]] where
  M :=![![![-495706, -32024, -27829], ![-5283315, -341317, -296606], ![-3723290, -240535, -209026]]]
  hmulB := by decide  
  f := ![![![-3032, 109, 249]], ![![558, -89, 52]], ![![-2077, 154, 58]]]
  g := ![![![13170, -32024, -27829], ![140368, -341317, -296606], ![98921, -240535, -209026]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-734417317924644378, -47445422437465541, -41230285224039808]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-734417317924644378, -47445422437465541, -41230285224039808]] 
 ![![47, 0, 0], ![13, 1, 0], ![28, 0, 1]] where
  M :=![![![-734417317924644378, -47445422437465541, -41230285224039808], ![-7827539055354137787, -505681018220682729, -439439076364041335], ![-5516271156288494843, -356366617319566483, -309684191257394832]]]
  hmulB := by decide  
  f := ![![![3136318277, -63071152, -328061203]], ![![-464350660, 108079376, -91541615]], ![![2212416706, -158117335, -70186457]]]
  g := ![![![22060024681606857, -47445422437465541, -41230285224039808], ![235119325951231810, -505681018220682729, -439439076364041335], ![165694728171764356, -356366617319566483, -309684191257394832]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48502836199867, -3133419510614, -2722955630113]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-48502836199867, -3133419510614, -2722955630113]] 
 ![![47, 0, 0], ![26, 1, 0], ![4, 0, 1]] where
  M :=![![![-48502836199867, -3133419510614, -2722955630113], ![-516951105840969, -33396494060692, -29021703356528], ![-364308942337556, -23535381376621, -20452352137735]]]
  hmulB := by decide  
  f := ![![![-26480732, 631117, 2630004]], ![![-3974455, -677625, 1490689]], ![![-4501275, 996053, -814106]]]
  g := ![![![933146672267, -3133419510614, -2722955630113], ![9945628790705, -33396494060692, -29021703356528], ![7008944297990, -23535381376621, -20452352137735]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-495706, -32024, -27829]] ![![-734417317924644378, -47445422437465541, -41230285224039808]]
  ![![768236491716167197517603, 49630236095671652835849, 43128898107251977556216]] where
 M := ![![![768236491716167197517603, 49630236095671652835849, 43128898107251977556216]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![768236491716167197517603, 49630236095671652835849, 43128898107251977556216]] ![![-48502836199867, -3133419510614, -2722955630113]]
  ![![47, 0, 0]] where
 M := ![![![-78630297406912764489824858084652904578, -5079738162216531842898765052725311886, -4414315281261837643382727028118362171]]]
 hmul := by decide  
 g := ![![![![-1672985051210909882762231023077721374, -108079535366309188146782235164368338, -93921601728975269008143128257837493]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![99, -10, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![99, -10, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![46, 43, 1]] where
  M :=![![![99, -10, 1], ![201, 60, -112], ![-1996, 109, 111]]]
  hmulB := by decide  
  f := ![![![-356, -23, -20]], ![![-3797, -245, -213]], ![![-3440, -222, -193]]]
  g := ![![![1, -1, 1], ![101, 92, -112], ![-134, -88, 111]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [35, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 52], [0, 1]]
 g := ![![[19, 15], [10], [49, 36], [15], [24, 1]], ![[8, 38], [10], [12, 17], [15], [48, 52]]]
 h' := ![![[24, 52], [11, 11], [34, 13], [16, 6], [8, 11], [0, 1]], ![[0, 1], [10, 42], [28, 40], [1, 47], [7, 42], [24, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [2, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [35, 29, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1402859, 28797, -19209]
  a := ![1, -66, -75]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![43141, 16128, -19209]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-356, -23, -20]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-356, -23, -20]] 
 ![![53, 0, 0], ![6, 1, 0], ![48, 0, 1]] where
  M :=![![![-356, -23, -20], ![-3797, -245, -213], ![-2673, -173, -150]]]
  hmulB := by decide  
  f := ![![![99, -10, 1]], ![![15, 0, -2]], ![![52, -7, 3]]]
  g := ![![![14, -23, -20], ![149, -245, -213], ![105, -173, -150]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![99, -10, 1]] ![![-356, -23, -20]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![180826, -17195, 325]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![180826, -17195, 325]] 
 ![![59, 0, 0], ![0, 59, 0], ![41, 7, 1]] where
  M :=![![![180826, -17195, 325], ![79270, 126316, -189795], ![-3312195, 160930, 212616]]]
  hmulB := by decide  
  f := ![![![972890034, 62851430, 54618175]], ![![10369219995, 669880749, 582129380]], ![![2030177821, 131155192, 113974451]]]
  g := ![![![2839, -330, 325], ![133235, 24659, -189795], ![-203889, -22498, 212616]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [38, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 58], [0, 1]]
 g := ![![[18, 9], [49, 16], [45], [31, 49], [24, 1]], ![[57, 50], [20, 43], [45], [27, 10], [48, 58]]]
 h' := ![![[24, 58], [26, 3], [5, 55], [2, 24], [32, 7], [0, 1]], ![[0, 1], [39, 56], [27, 4], [47, 35], [23, 52], [24, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [29, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [38, 35, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2393, 15284, -9861]
  a := ![3, -7, -32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6812, 1429, -9861]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![972890034, 62851430, 54618175]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![972890034, 62851430, 54618175]] 
 ![![59, 0, 0], ![43, 1, 0], ![40, 0, 1]] where
  M :=![![![972890034, 62851430, 54618175], ![10369219995, 669880749, 582129380], ![7307460080, 472082455, 410241774]]]
  hmulB := by decide  
  f := ![![![180826, -17195, 325]], ![![133132, -10391, -2980]], ![![66455, -8930, 3824]]]
  g := ![![![-66346584, 62851430, 54618175], ![-707132668, 669880749, 582129380], ![-498334855, 472082455, 410241774]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![180826, -17195, 325]] ![![972890034, 62851430, 54618175]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2421490396, -300266555, 103686655]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![2421490396, -300266555, 103686655]] 
 ![![61, 0, 0], ![0, 61, 0], ![43, 2, 1]] where
  M :=![![![2421490396, -300266555, 103686655], ![20104417660, 587510836, -3510305415], ![-66267964335, 4672445440, 2192530266]]]
  hmulB := by decide  
  f := ![![![289997472440279016, 18734651607355030, 16280496403259045]], ![![3090840161415122565, 199676959633012701, 173520174874387240]], ![![341471596788307798, 22060024681606857, 19170260542432951]]]
  g := ![![![-33394029, -8321965, 103686655], ![2804058205, 124723306, -3510305415], ![-2631914193, 4711228, 2192530266]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [21, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 60], [0, 1]]
 g := ![![[6, 14], [13], [56, 19], [36, 25], [57, 1]], ![[11, 47], [13], [41, 42], [58, 36], [53, 60]]]
 h' := ![![[57, 60], [16, 21], [44, 14], [37, 43], [23, 56], [0, 1]], ![[0, 1], [54, 40], [49, 47], [48, 18], [43, 5], [57, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [18, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [21, 4, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6412, 1531, -1034]
  a := ![1, -4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![834, 59, -1034]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![289997472440279016, 18734651607355030, 16280496403259045]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![289997472440279016, 18734651607355030, 16280496403259045]] 
 ![![61, 0, 0], ![41, 1, 0], ![30, 0, 1]] where
  M :=![![![289997472440279016, 18734651607355030, 16280496403259045], ![3090840161415122565, 199676959633012701, 173520174874387240], ![2178195766324532860, 140717567195726585, 122284197999496596]]]
  hmulB := by decide  
  f := ![![![2421490396, -300266555, 103686655]], ![![1957139736, -192187179, 12145040]], ![![104536845, -71074610, 86936556]]]
  g := ![![![-15844887468181124, 18734651607355030, 16280496403259045], ![-168877384094590416, 199676959633012701, 173520174874387240], ![-119012302109592705, 140717567195726585, 122284197999496596]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![2421490396, -300266555, 103686655]] ![![289997472440279016, 18734651607355030, 16280496403259045]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![558, -89, 52]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![558, -89, 52]] 
 ![![67, 0, 0], ![7, 1, 0], ![24, 0, 1]] where
  M :=![![![558, -89, 52], ![10021, -177, -1083], ![-21471, 1789, 320]]]
  hmulB := by decide  
  f := ![![![-1880847, -121508, -105591]], ![![-495706, -32024, -27829]], ![![-884590, -57147, -49661]]]
  g := ![![![-1, -89, 52], ![556, -177, -1083], ![-622, 1789, 320]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![944, 61, 53]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![944, 61, 53]] 
 ![![67, 0, 0], ![63, 1, 0], ![30, 0, 1]] where
  M :=![![![944, 61, 53], ![10062, 650, 565], ![7093, 458, 398]]]
  hmulB := by decide  
  f := ![![![-70, -4, 15]], ![![-23, -7, 13]], ![![-62, 3, 4]]]
  g := ![![![-67, 61, 53], ![-714, 650, 565], ![-503, 458, 398]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![558, -89, 52]] ![![944, 61, 53]]
  ![![70, 4, -15]] where
 M := ![![![70, 4, -15]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![70, 4, -15]] ![![944, 61, 53]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [57, 23, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 41, 54], [5, 29, 17], [0, 1]]
 g := ![![[22, 17, 37], [46, 30, 4], [24, 22, 27], [41, 20], [29, 1], []], ![[61, 9, 39, 12], [49, 10, 5, 18], [51, 52, 63, 3], [64, 24], [34, 60], [29, 5]], ![[48, 39, 65, 63], [10, 57, 1, 22], [63, 29, 34, 69], [3, 1], [14, 48], [66, 5]]]
 h' := ![![[24, 41, 54], [5, 7, 26], [52, 14, 2], [51, 39, 13], [51, 57, 37], [0, 0, 1], [0, 1]], ![[5, 29, 17], [3, 7, 67], [9, 50, 33], [50, 39, 69], [52, 27, 33], [59, 22, 29], [24, 41, 54]], ![[0, 1], [6, 57, 49], [32, 7, 36], [16, 64, 60], [20, 58, 1], [26, 49, 41], [5, 29, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 14], []]
 b := ![[], [2, 20, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [57, 23, 42, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14120054, 2201426, 594838]
  a := ![-1, 23, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![198874, 31006, 8378]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![307591068558691, 19871247354295, 17268203212963]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![307591068558691, 19871247354295, 17268203212963]] 
 ![![73, 0, 0], ![0, 73, 0], ![70, 33, 1]] where
  M :=![![![307591068558691, 19871247354295, 17268203212963], ![3278355566321638, 211790981704909, 184047314471319], ![2310342768355527, 149254634857642, 129702948146397]]]
  hmulB := by decide  
  f := ![![![4501275, -996053, 814106]], ![![156490299, -5813838, -12584795]], ![![71493286, -3248601, -4908634]]]
  g := ![![![-12344974744503, -7533965187308, 17268203212963], ![-131574745844804, -80298224600666, 184047314471319], ![-92724158930031, -56588255533883, 129702948146397]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [25, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 72], [0, 1]]
 g := ![![[26, 38], [6], [49], [56, 49], [49], [1]], ![[0, 35], [6], [49], [34, 24], [49], [1]]]
 h' := ![![[7, 72], [57, 44], [39, 15], [60, 7], [57, 66], [48, 7], [0, 1]], ![[0, 1], [0, 29], [71, 58], [36, 66], [8, 7], [24, 66], [7, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [70, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [25, 66, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7709, 2455, -2005]
  a := ![1, -1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1817, 940, -2005]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4501275, -996053, 814106]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![4501275, -996053, 814106]] 
 ![![73, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![4501275, -996053, 814106], ![156490299, -5813838, -12584795], ![-260259239, 24432491, -19467]]]
  hmulB := by decide  
  f := ![![![307591068558691, 19871247354295, 17268203212963]], ![![61763285487074, 3990081796193, 3467399004427]], ![![48502836199867, 3133419510614, 2722955630113]]]
  g := ![![![71631, -996053, 814106], ![3151847, -5813838, -12584795], ![-4902895, 24432491, -19467]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![307591068558691, 19871247354295, 17268203212963]] ![![4501275, -996053, 814106]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [4, 78, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 0, 29], [78, 78, 50], [0, 1]]
 g := ![![[14, 45, 42], [44, 56, 36], [0, 29, 73], [57, 56, 42], [22, 1], []], ![[71, 70, 54, 7], [0, 41, 65, 17], [9, 28, 38, 17], [44, 14, 53, 43], [3, 1], [16, 51]], ![[78, 74, 18, 62], [18, 46, 33, 11], [60, 30, 32, 51], [31, 70, 70, 18], [], [74, 51]]]
 h' := ![![[23, 0, 29], [61, 57, 11], [0, 44, 6], [9, 72, 28], [70, 18, 11], [0, 0, 1], [0, 1]], ![[78, 78, 50], [9, 65, 62], [10, 57, 6], [70, 29, 6], [69, 65, 37], [70, 49, 78], [23, 0, 29]], ![[0, 1], [77, 36, 6], [3, 57, 67], [51, 57, 45], [46, 75, 31], [21, 30], [78, 78, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 41], []]
 b := ![[], [37, 11, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [4, 78, 57, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30632013, -2110722, 1140128]
  a := ![-2, 7, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![387747, -26718, 14432]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB281I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB281I1 : PrimesBelowBoundCertificateInterval O 31 79 281 where
  m := 11
  g := ![3, 2, 2, 3, 2, 2, 2, 3, 1, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB281I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
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
    · exact ![37, 37, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![357911]
    · exact ![5329, 73]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
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
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N1
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
  β := ![I37N0, I37N1, I37N2, I41N1, I43N1, I47N0, I47N1, I47N2, I53N1, I59N1, I61N1, I67N0, I67N1, I73N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [I43N1], [I47N0, I47N1, I47N2], [I53N1], [I59N1], [I61N1], [I67N0, I67N1, I67N1], [], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
