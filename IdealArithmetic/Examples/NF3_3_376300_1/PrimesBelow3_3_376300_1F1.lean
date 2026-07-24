
import IdealArithmetic.Examples.NF3_3_376300_1.RI3_3_376300_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4424995, -6672800, 3842337]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-4424995, -6672800, 3842337]] 
 ![![37, 0, 0], ![3, 1, 0], ![30, 0, 1]] where
  M :=![![![-4424995, -6672800, 3842337], ![53792718, 81118293, -46709600], ![-101103874, -152462526, 87791093]]]
  hmulB := by decide  
  f := ![![![-314649, -607138, -309259]], ![![-142529, -274741, -139939]], ![![-468132, -902810, -459855]]]
  g := ![![![-2693965, -6672800, 3842337], ![32749347, 81118293, -46709600], ![-61552678, -152462526, 87791093]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17125, 25824, -14870]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![17125, 25824, -14870]] 
 ![![37, 0, 0], ![5, 1, 0], ![1, 0, 1]] where
  M :=![![![17125, 25824, -14870], ![-208180, -313931, 180768], ![391276, 590036, -339755]]]
  hmulB := by decide  
  f := ![![![-743, -2200, -1138]], ![![-531, -1115, -570]], ![![-791, -1548, -789]]]
  g := ![![![-2625, 25824, -14870], ![31911, -313931, 180768], ![-59977, 590036, -339755]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![506162447, 975511802, 496871811]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![506162447, 975511802, 496871811]] 
 ![![37, 0, 0], ![28, 1, 0], ![32, 0, 1]] where
  M :=![![![506162447, 975511802, 496871811], ![6956205354, 13406597713, 6828582614], ![12663421606, 24406026870, 12431085911]]]
  hmulB := by decide  
  f := ![![![2816779716637, 4247644860052, -2445882242185]], ![![1206148126358, 1818846130965, -1047329425968]], ![![4175560633986, 6296658045366, -3625746644479]]]
  g := ![![![-1154272053, 975511802, 496871811], ![-15863329034, 13406597713, 6828582614], ![-28878380538, 24406026870, 12431085911]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-4424995, -6672800, 3842337]] ![![17125, 25824, -14870]]
  ![![2816779716637, 4247644860052, -2445882242185]] where
 M := ![![![2816779716637, 4247644860052, -2445882242185]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![2816779716637, 4247644860052, -2445882242185]] ![![506162447, 975511802, 496871811]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [26, 28, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 24, 25], [9, 16, 16], [0, 1]]
 g := ![![[26, 1, 5], [12, 32], [33, 9], [11, 30, 1], []], ![[0, 2, 23, 5], [11, 10], [22, 2], [28, 18, 29, 4], [24, 10]], ![[19, 39, 17, 25], [9, 39], [4, 32], [36, 2, 24, 32], [33, 10]]]
 h' := ![![[21, 24, 25], [32, 40, 13], [4, 28, 27], [1, 19, 38], [0, 0, 1], [0, 1]], ![[9, 16, 16], [10, 21, 19], [38, 18, 25], [6, 23, 17], [22, 35, 16], [21, 24, 25]], ![[0, 1], [8, 21, 9], [23, 36, 30], [2, 40, 27], [2, 6, 24], [9, 16, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 6], []]
 b := ![[], [15, 37, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [26, 28, 11, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-293232, -784822, -1256978]
  a := ![0, -2, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7152, -19142, -30658]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-403652733437808093799605653, -1417230437182353959682806, 16912553619721608311695771]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-403652733437808093799605653, -1417230437182353959682806, 16912553619721608311695771]] 
 ![![43, 0, 0], ![0, 43, 0], ![7, 31, 1]] where
  M :=![![![-403652733437808093799605653, -1417230437182353959682806, 16912553619721608311695771], ![236775750676102516363740794, 831322998328151721410045, -9920613060276477717779642], ![-53666333359996172058950826, -188423252933278408995802, 2248553435510505681092851]]]
  hmulB := by decide  
  f := ![![![-485431626744777, -935565478001548, -476526226530599]], ![![-6671367171428386, -12857626541480701, -6548958346010836]], ![![-5171052742801253, -9966093140860719, -5076173334314634]]]
  g := ![![![-12140479273857194232127350, -12225730061594237479587249, 16912553619721608311695771], ![7121396327861345590423216, 7171402973648813045873929, -9920613060276477717779642], ![-1614097846710923530851181, -1625432087296719872624981, 2248553435510505681092851]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [13, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 42], [0, 1]]
 g := ![![[5, 10], [32, 21], [14], [29, 11], [1]], ![[0, 33], [0, 22], [14], [2, 32], [1]]]
 h' := ![![[21, 42], [14, 28], [4, 8], [10, 33], [30, 21], [0, 1]], ![[0, 1], [0, 15], [0, 35], [15, 10], [41, 22], [21, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [32, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [13, 22, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![82, 615, 2131]
  a := ![-1, 1, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-345, -1522, 2131]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9073570341049, 17486975059650, 8905400214178]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![9073570341049, 17486975059650, 8905400214178]] 
 ![![43, 0, 0], ![41, 1, 0], ![12, 0, 1]] where
  M :=![![![9073570341049, 17486975059650, 8905400214178], ![124675602998492, 240290150540971, 122408825417550], ![227006850406744, 437498201859956, 222803175481321]]]
  hmulB := by decide  
  f := ![![![-16232434554400766868925109, -56992306540671074141482, 680119065320841442770662]], ![![-15256003484091620033189307, -53564043288575752473755, 639207803078367479874576]], ![![-4580170815698146054665660, -16081044298197111245396, 191903530166268024902761]]]
  g := ![![![-18947842085459, 17486975059650, 8905400214178], ![-260375034283533, 240290150540971, 122408825417550], ![-474047849572728, 437498201859956, 222803175481321]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-403652733437808093799605653, -1417230437182353959682806, 16912553619721608311695771]] ![![9073570341049, 17486975059650, 8905400214178]]
  ![![43, 0, 0]] where
 M := ![![![1075, 0, -43]]]
 hmul := by decide  
 g := ![![![![25, 0, -1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33034956193327, 63711067153824, 32619806043848]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![33034956193327, 63711067153824, 32619806043848]] 
 ![![47, 0, 0], ![6, 1, 0], ![41, 0, 1]] where
  M :=![![![33034956193327, 63711067153824, 32619806043848], ![456677284613872, 879621368399503, 445977470076768], ![826715328065840, 1594305223779472, 815910301245679]]]
  hmulB := by decide  
  f := ![![![6667925441630495232481991041, 23411180219834466405961760, -279377884062456569454646712]], ![![768005580274650626011210474, 2696478418518698519408559, -32178490273104215997577616]], ![![5835562880809636174475625335, 20488743535411216542089808, -244502915370833654937660537]]]
  g := ![![![-35886031798455, 63711067153824, 32619806043848], ![-491619727636822, 879621368399503, 445977470076768], ![-897690177993273, 1594305223779472, 815910301245679]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67013, -101054, 58189]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-67013, -101054, 58189]] 
 ![![47, 0, 0], ![17, 1, 0], ![10, 0, 1]] where
  M :=![![![-67013, -101054, 58189], ![814646, 1228469, -707378], ![-1531134, -2308918, 1329523]]]
  hmulB := by decide  
  f := ![![![-6717, -12260, -6229]], ![![-4285, -8019, -4079]], ![![-4816, -9134, -4649]]]
  g := ![![![22745, -101054, 58189], ![-276501, 1228469, -707378], ![519686, -2308918, 1329523]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![429955296221, 828673470908, 422185589091]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![429955296221, 828673470908, 422185589091]] 
 ![![47, 0, 0], ![23, 1, 0], ![42, 0, 1]] where
  M :=![![![429955296221, 828673470908, 422185589091], ![5910598247274, 11391082905313, 5800714296356], ![10757057414530, 20732534479974, 10562409434405]]]
  hmulB := by decide  
  f := ![![![53772389488658716319021, 188795617496030573894, -2252997057005222329235]], ![![25643042541299518355919, 90033083839108812571, -1074411978481870203301]], ![![48204031729417467193444, 169245034909097302522, -2019689707950765051287]]]
  g := ![![![-773645303755, 828673470908, 422185589091], ![-10632219340891, 11391082905313, 5800714296356], ![-19355583656806, 20732534479974, 10562409434405]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![33034956193327, 63711067153824, 32619806043848]] ![![-67013, -101054, 58189]]
  ![![-257099613930479579, -387700838918887666, 223246195630715835]] where
 M := ![![![-257099613930479579, -387700838918887666, 223246195630715835]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-257099613930479579, -387700838918887666, 223246195630715835]] ![![429955296221, 828673470908, 422185589091]]
  ![![47, 0, 0]] where
 M := ![![![-613095671414266504603010893, -924579592490642179413968900, 532171936582666787969485390]]]
 hmul := by decide  
 g := ![![![![-13044588753495032012830019, -19671906223205152753488700, 11322807161333335914244370]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![153483, 295672, 150596]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![153483, 295672, 150596]] 
 ![![53, 0, 0], ![32, 1, 0], ![46, 0, 1]] where
  M :=![![![153483, 295672, 150596], ![2108344, 4063459, 2069704], ![3838216, 7397320, 3767787]]]
  hmulB := by decide  
  f := ![![![14798047, 22315144, -12849524]], ![![5540456, 8354891, -4810920]], ![![19223042, 28987944, -16691861]]]
  g := ![![![-306329, 295672, 150596], ![-4209976, 4063459, 2069704], ![-7664042, 7397320, 3767787]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1348303312443, 2597908682912, 1320668966485]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![1348303312443, 2597908682912, 1320668966485]] 
 ![![53, 0, 0], ![41, 1, 0], ![19, 0, 1]] where
  M :=![![![1348303312443, 2597908682912, 1320668966485], ![18489365530790, 35642267190995, 18185360780384], ![33729383627798, 64991146322858, 33044358508083]]]
  hmulB := by decide  
  f := ![![![-4111588311776493484904887, -14435844521564844563566, 172270498933347176795633]], ![![-3135157241467346649169085, -11007581269469522895839, 131359236690873213899547]], ![![-1484279636696641101710831, -5211326727558376653624, 62189493252027077685044]]]
  g := ![![![-2457710623588, 2597908682912, 1320668966485], ![-33742744228817, 35642267190995, 18185360780384], ![-61485857118169, 64991146322858, 33044358508083]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![153483, 295672, 150596]] ![![153483, 295672, 150596]]
  ![![1224955295193, 2360838477744, 1202481098008]] where
 M := ![![![1224955295193, 2360838477744, 1202481098008]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI53N1 : IdealMulLeCertificate' Table 
  ![![1224955295193, 2360838477744, 1202481098008]] ![![1348303312443, 2597908682912, 1320668966485]]
  ![![53, 0, 0]] where
 M := ![![![85860963116153560367950643, 165478582807203357008224160, 84285676407449712437578965]]]
 hmul := by decide  
 g := ![![![![1620018172002897365433031, 3122237411456667113362720, 1590295781272636083727905]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [43, 12, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 38, 56], [53, 20, 3], [0, 1]]
 g := ![![[37, 31, 5], [31, 17, 36], [8, 16], [50, 32, 16], [1]], ![[35, 55, 46, 2], [11, 42, 39, 10], [49, 36], [34, 4, 32, 33], [51, 15, 13, 32]], ![[44, 47, 43, 36], [7, 48, 35, 19], [32, 4], [2, 5, 56, 9], [28, 29, 19, 27]]]
 h' := ![![[2, 38, 56], [24, 30, 51], [37, 38, 6], [33, 50, 55], [16, 47, 55], [0, 1]], ![[53, 20, 3], [37, 37, 45], [45, 44, 6], [21, 21, 6], [57, 25, 15], [2, 38, 56]], ![[0, 1], [14, 51, 22], [6, 36, 47], [54, 47, 57], [55, 46, 48], [53, 20, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 50], []]
 b := ![[], [57, 48, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [43, 12, 4, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-246089, -472, -16874]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4171, -8, -286]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [1, 29, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 41, 36], [34, 19, 25], [0, 1]]
 g := ![![[21, 46, 41], [18, 48], [47, 50, 22], [33, 40, 47], [1]], ![[17, 12, 56, 20], [38, 42], [26, 0, 36, 27], [30, 34, 44, 27], [55, 15, 20, 52]], ![[60, 19, 56, 46], [43, 45], [21, 3, 57, 14], [16, 27, 5, 12], [10, 49, 57, 9]]]
 h' := ![![[40, 41, 36], [56, 57, 38], [14, 42, 32], [28, 41, 12], [60, 32, 13], [0, 1]], ![[34, 19, 25], [36, 54, 29], [14, 21, 46], [1, 29, 57], [17, 51, 57], [40, 41, 36]], ![[0, 1], [33, 11, 55], [25, 59, 44], [29, 52, 53], [10, 39, 52], [34, 19, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 7], []]
 b := ![[], [41, 43, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [1, 29, 48, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-366915, -1013454, -1711538]
  a := ![1, -2, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6015, -16614, -28058]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![928061519475933919, 3258437077279562, -38884637487424204]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![928061519475933919, 3258437077279562, -38884637487424204]] 
 ![![67, 0, 0], ![0, 67, 0], ![15, 18, 1]] where
  M :=![![![928061519475933919, 3258437077279562, -38884637487424204], ![-544384924823938856, -1911343144967415, 22809059540956934], ![123387394056762276, 433214879861080, -5169780222246977]]]
  hmulB := by decide  
  f := ![![![12426336205, 18738638862, -10790178056]], ![![-151062492784, -227799298277, 131170472034]], ![![-33564306371, -50614340440, 29144446099]]]
  g := ![![![22557180325183537, 10495252415685302, -38884637487424204], ![-13231653999078998, -6156334550480481, 22809059540956934], ![2999016378962193, 1395362072840398, -5169780222246977]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [40, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 66], [0, 1]]
 g := ![![[62, 62], [64, 64], [60], [10], [1], [1]], ![[0, 5], [0, 3], [60], [10], [1], [1]]]
 h' := ![![[66, 66], [53, 53], [59, 59], [28, 44], [19, 12], [27, 66], [0, 1]], ![[0, 1], [0, 14], [0, 8], [51, 23], [7, 55], [28, 1], [66, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [59, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [40, 1, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![430, 1588, 4071]
  a := ![0, -2, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-905, -1070, 4071]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16798837369655, 32376041436388, 16490131461871]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![16798837369655, 32376041436388, 16490131461871]] 
 ![![67, 0, 0], ![8, 1, 0], ![28, 0, 1]] where
  M :=![![![16798837369655, 32376041436388, 16490131461871], ![230861840466194, 444938033890947, 226632290054716], ![420284317185690, 810005257397054, 412561992454559]]]
  hmulB := by decide  
  f := ![![![8824659390842103538229291, 30983503517870870364858, -369742386858856450823971]], ![![976431070309146835735802, 3428263252095321667727, -40911262242473962896086]], ![![3705428608455922450107106, 13009812077784662049622, -155252906355498983651003]]]
  g := ![![![-10506465299311, 32376041436388, 16490131461871], ![-144393232122290, 444938033890947, 226632290054716], ![-262858112398782, 810005257397054, 412561992454559]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![928061519475933919, 3258437077279562, -38884637487424204]] ![![16798837369655, 32376041436388, 16490131461871]]
  ![![67, 0, 0]] where
 M := ![![![-564485787, -1087925230, -554129195]]]
 hmul := by decide  
 g := ![![![![-8425161, -16237690, -8270585]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![204972175, 309093750, -177982609]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![204972175, 309093750, -177982609]] 
 ![![71, 0, 0], ![39, 1, 0], ![51, 0, 1]] where
  M :=![![![204972175, 309093750, -177982609], ![-2491756526, -3757516691, 2163656250], ![4683277718, 7062284782, -4066610441]]]
  hmulB := by decide  
  f := ![![![-1816769, -3512488, -1789319]], ![![-1350767, -2609295, -1329167]], ![![-1947203, -3760778, -1915714]]]
  g := ![![![-39050296, 309093750, -177982609], ![474717263, -3757516691, 2163656250], ![-892235159, 7062284782, -4066610441]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9301745734145, 18068809593770, 9756225761599]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![9301745734145, 18068809593770, 9756225761599]] 
 ![![71, 0, 0], ![63, 1, 0], ![63, 0, 1]] where
  M :=![![![9301745734145, 18068809593770, 9756225761599], ![136587160662386, 261519973606291, 126481667156390], ![233450882789582, 453163881773678, 243451164012521]]]
  hmulB := by decide  
  f := ![![![-6350418725179303630436867191, -22296409662647627297796952, 266074742718983243092929009]], ![![-5582413144904653004425656717, -19599931244128928778388393, 233896252445879027095351393]], ![![-5646770125450861436420811949, -19825889510033480122851786, 236592730864397725614759952]]]
  g := ![![![-24558809600762, 18068809593770, 9756225761599], ![-342359383202627, 261519973606291, 126481667156390], ![-614835169038605, 453163881773678, 243451164012521]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![204972175, 309093750, -177982609]] ![![204972175, 309093750, -177982609]]
  ![![-1561714763105288137, -2355033177493731238, 1356077077620353494]] where
 M := ![![![-1561714763105288137, -2355033177493731238, 1356077077620353494]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-1561714763105288137, -2355033177493731238, 1356077077620353494]] ![![9301745734145, 18068809593770, 9756225761599]]
  ![![71, 0, 0]] where
 M := ![![![-19616577714063521643181903652225, -29581388635684659181204085593816, 17033578735277910013565922936491]]]
 hmul := by decide  
 g := ![![![![-276289826958641149903970473975, -416639276558938861707099797096, 239909559651801549486843985021]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9768702803, -14716896858, 8544636063]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-9768702803, -14716896858, 8544636063]] 
 ![![73, 0, 0], ![0, 73, 0], ![29, 63, 1]] where
  M :=![![![-9768702803, -14716896858, 8544636063], ![119624904882, 180585665851, -103018278006], ![-223125828138, -336116252466, 195302562709]]]
  hmulB := by decide  
  f := ![![![8804462881290086131, 30912593288134068, -368896177921236705]], ![![-5164546490897313870, -18132795531460721, 216388153016938476]], ![![-943375845304683913, -3312205891142373, 39526288925091298]]]
  g := ![![![-3528262310, -7575739299, 8544636063], ![42563766672, 91379961373, -103018278006], ![-80642467763, -173153119221, 195302562709]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [36, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 72], [0, 1]]
 g := ![![[28, 71], [6], [50], [2, 37], [50], [1]], ![[0, 2], [6], [50], [9, 36], [50], [1]]]
 h' := ![![[14, 72], [22, 61], [26, 15], [1, 59], [7, 57], [37, 14], [0, 1]], ![[0, 1], [0, 12], [17, 58], [24, 14], [2, 16], [14, 59], [14, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [48, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [36, 59, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38574, 147062, 361565]
  a := ![1, 20, 121]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-143107, -310021, 361565]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-135386567773523678265927, -475344147926727504648, 5672530859282731048210]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-135386567773523678265927, -475344147926727504648, 5672530859282731048210]] 
 ![![73, 0, 0], ![70, 1, 0], ![20, 0, 1]] where
  M :=![![![-135386567773523678265927, -475344147926727504648, 5672530859282731048210], ![79415432029958234674940, 278828701335139386465, -3327409035487092532536], ![-17999879789539647161492, -63197831675998015132, 754172849261866891113]]]
  hmulB := by decide  
  f := ![![![5152650650793, 9930215879504, 5056294749678]], ![![5910598247274, 11391082905313, 5800714296356]], ![![3177581449720, 6123864221884, 3118213967625]]]
  g := ![![![-2952919104168594163079, -475344147926727504648, 5672530859282731048210], ![1732131556797812716070, 278828701335139386465, -3327409035487092532536], ![-392595733663796218144, -63197831675998015132, 754172849261866891113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-9768702803, -14716896858, 8544636063]] ![![-135386567773523678265927, -475344147926727504648, 5672530859282731048210]]
  ![![73, 0, 0]] where
 M := ![![![-1131135, -3942, 47377]]]
 hmul := by decide  
 g := ![![![![-15495, -54, 649]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [34, 31, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 50, 20], [35, 28, 59], [0, 1]]
 g := ![![[32, 45, 76], [55, 16, 62], [46, 13, 76], [69, 36, 11], [53, 1], []], ![[4, 72, 58, 16], [29, 22, 1, 23], [78, 64, 9, 2], [39, 26, 59, 4], [60, 73], [53, 5]], ![[72, 36, 23, 14], [57, 38, 20, 78], [10, 77, 69, 30], [2, 72, 13, 66], [53, 51], [14, 5]]]
 h' := ![![[18, 50, 20], [26, 61, 47], [16, 51, 33], [24, 22, 47], [15, 61, 13], [0, 0, 1], [0, 1]], ![[35, 28, 59], [72, 69, 8], [34, 67, 48], [0, 15, 18], [69, 37, 4], [23, 66, 28], [18, 50, 20]], ![[0, 1], [76, 28, 24], [53, 40, 77], [52, 42, 14], [37, 60, 62], [38, 13, 50], [35, 28, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 36], []]
 b := ![[], [33, 4, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [34, 31, 26, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![226730, 582230, 863628]
  a := ![-1, 2, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2870, 7370, 10932]
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



lemma PB137I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB137I1 : PrimesBelowBoundCertificateInterval O 31 79 137 where
  m := 11
  g := ![3, 1, 2, 3, 3, 1, 1, 2, 3, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB137I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N0, I71N1]
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
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![53, 53, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![71, 71, 71]
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
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N0, I37N1, I37N2, I43N1, I47N0, I47N1, I47N2, I53N0, I53N1, I67N1, I71N0, I71N1, I73N1]
  Il := ![[I37N0, I37N1, I37N2], [], [I43N1], [I47N0, I47N1, I47N2], [I53N0, I53N0, I53N1], [], [], [I67N1], [I71N0, I71N0, I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
