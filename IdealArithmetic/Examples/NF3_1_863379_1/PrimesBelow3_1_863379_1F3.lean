
import IdealArithmetic.Examples.NF3_1_863379_1.RI3_1_863379_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0]] 
 ![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [3, 50, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 60, 14], [134, 78, 125], [0, 1]]
 g := ![![[55, 58, 124], [114, 114, 91], [31, 100], [77, 119, 107], [90, 91], [108, 1], []], ![[7, 83, 107, 88], [116, 83, 13, 114], [110, 121], [95, 36, 61, 60], [63, 9], [91, 107], [52, 57]], ![[91, 98, 38, 64], [112, 7, 129, 89], [11, 24], [112, 24, 13, 80], [138, 6], [122, 125], [80, 57]]]
 h' := ![![[113, 60, 14], [75, 62, 92], [31, 36, 62], [47, 94, 10], [39, 104, 78], [93, 18, 77], [0, 0, 1], [0, 1]], ![[134, 78, 125], [16, 95, 121], [60, 125, 58], [23, 106, 11], [87, 21, 34], [50, 57, 3], [103, 86, 78], [113, 60, 14]], ![[0, 1], [1, 121, 65], [4, 117, 19], [68, 78, 118], [124, 14, 27], [128, 64, 59], [63, 53, 60], [134, 78, 125]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 31], []]
 b := ![[], [126, 61, 107], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [3, 50, 31, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12093, 556, -4726]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![87, 4, -34]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2213635463716650236, 64055841223146032, 39047294426636261]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![2213635463716650236, 64055841223146032, 39047294426636261]] 
 ![![149, 0, 0], ![54, 1, 0], ![64, 0, 1]] where
  M :=![![![2213635463716650236, 64055841223146032, 39047294426636261], ![3631398381677172273, 105081564678292142, 64055841223146032], ![5957193233752580976, 172382955627286545, 105081564678292142]]]
  hmulB := by decide  
  f := ![![![-2544791276, 1110327701, 268783962]], ![![-754508862, 287909870, 104863501]], ![![-400041379, 242283124, 960056]]]
  g := ![![![-25130247017704404, 64055841223146032, 39047294426636261], ![-41225368786791607, 105081564678292142, 64055841223146032], ![-67628902748534158, 172382955627286545, 105081564678292142]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44213440675941125344568620099521737, -1279401772463467042026537941372666, -779900423527490732728462976004734]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-44213440675941125344568620099521737, -1279401772463467042026537941372666, -779900423527490732728462976004734]] 
 ![![149, 0, 0], ![101, 1, 0], ![80, 0, 1]] where
  M :=![![![-44213440675941125344568620099521737, -1279401772463467042026537941372666, -779900423527490732728462976004734], ![-72530739388056638143747056768440262, -2098817805456625777231619395266101, -1279401772463467042026537941372666], ![-118984364839102434908468028547657938, -3443043675029417874314007934316298, -2098817805456625777231619395266101]]]
  hmulB := by decide  
  f := ![![![-350457816264231733, 266661250376440534, -32325186526225422]], ![![-257734777111586371, 190120057343439161, -20122030797129712]], ![![-21725698094829322, 26355370220459662, -7992702456014045]]]
  g := ![![![989249478020592647774421141338901, -1279401772463467042026537941372666, -779900423527490732728462976004734], ![1622832219866710930998453271565431, -2098817805456625777231619395266101, -1279401772463467042026537941372666], ![2662204501848314312589102848587760, -3443043675029417874314007934316298, -2098817805456625777231619395266101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-134690273676959970145223114, -3897524649549884524541105, -2375861273851398446126090]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![-134690273676959970145223114, -3897524649549884524541105, -2375861273851398446126090]] 
 ![![149, 0, 0], ![143, 1, 0], ![113, 0, 1]] where
  M :=![![![-134690273676959970145223114, -3897524649549884524541105, -2375861273851398446126090], ![-220955098468180055489726370, -6393764888984454054414254, -3897524649549884524541105], ![-362469792408139260782322765, -10488767392486291164506700, -6393764888984454054414254]]]
  hmulB := by decide  
  f := ![![![29338159526984, -18801928892330, 559542665835]], ![![28506001881083, -18050691114304, 410823304175]], ![![10514313017198, -7095814340435, 418464273901]]]
  g := ![![![4638443457408600948163779, -3897524649549884524541105, -2375861273851398446126090], ![7609218564132441782313133, -6393764888984454054414254, -3897524649549884524541105], ![12482680383709018012690913, -10488767392486291164506700, -6393764888984454054414254]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![2213635463716650236, 64055841223146032, 39047294426636261]] ![![-44213440675941125344568620099521737, -1279401772463467042026537941372666, -779900423527490732728462976004734]]
  ![![-107164475305273018666453086120826243299436171577810134, -3101012216072353935059305776671399483754495245192186, -1890321549283151767972620114705671833061866440066897]] where
 M := ![![![-107164475305273018666453086120826243299436171577810134, -3101012216072353935059305776671399483754495245192186, -1890321549283151767972620114705671833061866440066897]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![-107164475305273018666453086120826243299436171577810134, -3101012216072353935059305776671399483754495245192186, -1890321549283151767972620114705671833061866440066897]] ![![-134690273676959970145223114, -3897524649549884524541105, -2375861273851398446126090]]
  ![![149, 0, 0]] where
 M := ![![![15804381426421633647418361581355361160197900305110807226942784775294381808392301, 457330470113252056290857816479117475799964796109709979514530143613881061087214, 278780469911797309611012972474838521008194765543842992777292014884790935951428]]]
 hmul := by decide  
 g := ![![![![106069674002829756022942024035942021209381881242354410919079092451640146365049, 3069332014182899706650052459591392455033320779259798520231745930294503765686, 1871009865179847715510154177683480006766407822441899280384510167012019704372]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21658, -9946, -1985]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![21658, -9946, -1985]] 
 ![![151, 0, 0], ![22, 1, 0], ![120, 0, 1]] where
  M :=![![![21658, -9946, -1985], ![-184605, 128848, -9946], ![-924978, 352479, 128848]]]
  hmulB := by decide  
  f := ![![![20107563238, 581851393, 354686196]], ![![3148027864, 91094300, 55529455]], ![![16337879259, 472768266, 288191074]]]
  g := ![![![3170, -9946, -1985], ![-12091, 128848, -9946], ![-159876, 352479, 128848]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5440121245169736757187527143215466302787472915, 157420473437021697076467752472552336640707386, 95960703312951721450821350594267483866754954]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![5440121245169736757187527143215466302787472915, 157420473437021697076467752472552336640707386, 95960703312951721450821350594267483866754954]] 
 ![![151, 0, 0], ![134, 1, 0], ![13, 0, 1]] where
  M :=![![![5440121245169736757187527143215466302787472915, 157420473437021697076467752472552336640707386, 95960703312951721450821350594267483866754954], ![8924345408104510094926385605266875999608210722, 258243266270343798843174211125022173982705399, 157420473437021697076467752472552336640707386], ![14640104029643017828111500979947367307585786898, 423639842505338452797126971749049821010011878, 258243266270343798843174211125022173982705399]]]
  hmulB := by decide  
  f := ![![![-158570370405642958581707, 78569510645703453966598, 11028650412814569156350]], ![![-133925596993141731909988, 64729781018719424758275, 10307342158694408747798]], ![![34738739568060018260473, -14540963232331699874768, -4044669121397617841007]]]
  g := ![![![-111931863168606245231257147323390888061822061, 157420473437021697076467752472552336640707386, 95960703312951721450821350594267483866754954], ![-183620651833131397430814830911452156890089462, 258243266270343798843174211125022173982705399, 157420473437021697076467752472552336640707386], ![-301223823361502014779236940258613224963781291, 423639842505338452797126971749049821010011878, 258243266270343798843174211125022173982705399]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![392050577832185181563774213839687591179724, 11344744867294753568400870776218607451443, 6915553438524840389398660617950706252804]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![392050577832185181563774213839687591179724, 11344744867294753568400870776218607451443, 6915553438524840389398660617950706252804]] 
 ![![151, 0, 0], ![146, 1, 0], ![126, 0, 1]] where
  M :=![![![392050577832185181563774213839687591179724, 11344744867294753568400870776218607451443, 6915553438524840389398660617950706252804], ![643146469782810156214075437469415681510772, 18610692151843800536246540470349453528308, 11344744867294753568400870776218607451443], ![1055061272658412081861280982188330492984199, 30530246948893463520428415553610879132850, 18610692151843800536246540470349453528308]]]
  hmulB := by decide  
  f := ![![![1340203015861836140314, -662430069195734937044, -94200980431615593383]], ![![1237807610170118054975, -597932014194756441228, -95468696769613321662]], ![![710328367969456983672, -373878517630683216237, -36041507120625738962]]]
  g := ![![![-14143323881105819393953537465894159500558, 11344744867294753568400870776218607451443, 6915553438524840389398660617950706252804], ![-23201671772619362064214762841093702466914, 18610692151843800536246540470349453528308, 11344744867294753568400870776218607451443], ![-38061602602730810991313455549025754999859, 30530246948893463520428415553610879132850, 18610692151843800536246540470349453528308]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![21658, -9946, -1985]] ![![5440121245169736757187527143215466302787472915, 157420473437021697076467752472552336640707386, 95960703312951721450821350594267483866754954]]
  ![![37310894228302192580696388110037559528, 1079663185630840279204069827579089704, 658143355639735995470610002032915561]] where
 M := ![![![37310894228302192580696388110037559528, 1079663185630840279204069827579089704, 658143355639735995470610002032915561]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![37310894228302192580696388110037559528, 1079663185630840279204069827579089704, 658143355639735995470610002032915561]] ![![392050577832185181563774213839687591179724, 11344744867294753568400870776218607451443, 6915553438524840389398660617950706252804]]
  ![![151, 0, 0]] where
 M := ![![![16016520774427293159464245629427245202616664067595516048780942960197662101122399, 463469134141617855704157921398300260710031437668229576554993635474470068618586, 282522489642157005042033280830205481021727581188726791338061035218814975360172]]]
 hmul := by decide  
 g := ![![![![106069674002829756022942024035942021209381881242354410919079092451640146365049, 3069332014182899706650052459591392455033320779259798520231745930294503765686, 1871009865179847715510154177683480006766407822441899280384510167012019704372]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1219396054, -35285593, -21509466]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-1219396054, -35285593, -21509466]] 
 ![![157, 0, 0], ![23, 1, 0], ![99, 0, 1]] where
  M :=![![![-1219396054, -35285593, -21509466], ![-2000380338, -57884890, -35285593], ![-3281560149, -94958316, -57884890]]]
  hmulB := by decide  
  f := ![![![29288, -29486, 7091]], ![![8491, -6572, 851]], ![![1002, -4251, 2219]]]
  g := ![![![10965667, -35285593, -21509466], ![17988827, -57884890, -35285593], ![29510097, -94958316, -57884890]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5872568, 3084724, 301797]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-5872568, 3084724, 301797]] 
 ![![157, 0, 0], ![141, 1, 0], ![58, 0, 1]] where
  M :=![![![-5872568, 3084724, 301797], ![28067121, -22169606, 3084724], ![286879332, -138507975, -22169606]]]
  hmulB := by decide  
  f := ![![![918750304869136, 26585824367669, 16206242738158]], ![![834719576822910, 24154232056369, 14723987582471]], ![![355159231519765, 10277222115410, 6264810674024]]]
  g := ![![![-2919254, 3084724, 301797], ![18949475, -22169606, 3084724], ![134409815, -138507975, -22169606]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-688117, -19912, -12138]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![-688117, -19912, -12138]] 
 ![![157, 0, 0], ![150, 1, 0], ![108, 0, 1]] where
  M :=![![![-688117, -19912, -12138], ![-1128834, -32665, -19912], ![-1851816, -53586, -32665]]]
  hmulB := by decide  
  f := ![![![2207, -1388, 26]], ![![2124, -1321, 16]], ![![696, -462, 23]]]
  g := ![![![22991, -19912, -12138], ![37716, -32665, -19912], ![61872, -53586, -32665]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-1219396054, -35285593, -21509466]] ![![-5872568, 3084724, 301797]]
  ![![2207, -1388, 26]] where
 M := ![![![2207, -1388, 26]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![2207, -1388, 26]] ![![-688117, -19912, -12138]]
  ![![157, 0, 0]] where
 M := ![![![157, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![132735549475102810844, -86415113649577546560, 3353858681689198127]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![132735549475102810844, -86415113649577546560, 3353858681689198127]] 
 ![![163, 0, 0], ![0, 163, 0], ![147, 147, 1]] where
  M :=![![![132735549475102810844, -86415113649577546560, 3353858681689198127], ![311908857397095425811, -48372819336113888014, -86415113649577546560], ![-8036605569410711830080, 4978324994474282940051, -48372819336113888014]]]
  hmulB := by decide  
  f := ![![![-2653634661549398683416915267634845853612, -76788072530718645480902252281015285599, -46808634767838112116845928708717204806]], ![![-4353203033408944426866671369910700046958, -125968384086140629107235117364116794088, -76788072530718645480902252281015285599]], ![![-6362861545424743995346080645284231097819, -184121756070113195922418055733560063427, -112237327343398674821939986029784005421]]]
  g := ![![![-2210317035173063275, -3554799631029997983, 3353858681689198127], ![79846199778435550737, 77635882743262487462, -86415113649577546560], ![-5679761515349510994, 74166438263086039743, -48372819336113888014]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [11, 148, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 162], [0, 1]]
 g := ![![[132, 53], [70, 62], [144], [119], [65], [111, 62], [1]], ![[112, 110], [22, 101], [144], [119], [65], [63, 101], [1]]]
 h' := ![![[15, 162], [45, 85], [80, 15], [69, 151], [143, 49], [83, 126], [152, 15], [0, 1]], ![[0, 1], [16, 78], [142, 148], [52, 12], [63, 114], [17, 37], [51, 148], [15, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [28, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [11, 148, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1252, 1193, -44]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![32, 47, -44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7698668060407883000, 6568913871141995823, -1143541646516134852]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-7698668060407883000, 6568913871141995823, -1143541646516134852]] 
 ![![163, 0, 0], ![16, 1, 0], ![70, 0, 1]] where
  M :=![![![-7698668060407883000, 6568913871141995823, -1143541646516134852], ![-106349373126000541236, 54052580851463399008, 6568913871141995823], ![610908990016205611539, -461070722167668315678, 54052580851463399008]]]
  hmulB := by decide  
  f := ![![![5950415359128641412133424506270336797058, 172186824661796629544273905221035466072, 104962006751810678932028867078160474145]], ![![643976149533599114937505992261314802751, 18634700546746078665719313911572016260, 11359379955158082775808194959948484984]], ![![2653634661549398683416915267634845853612, 76788072530718645480902252281015285599, 46808634767838112116845928708717204806]]]
  g := ![![![-200940949340799856, 6568913871141995823, -1143541646516134852], ![-8779230906315059098, 54052580851463399008, 6568913871141995823], ![25793618926972151729, -461070722167668315678, 54052580851463399008]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![132735549475102810844, -86415113649577546560, 3353858681689198127]] ![![-7698668060407883000, 6568913871141995823, -1143541646516134852]]
  ![![163, 0, 0]] where
 M := ![![![10217208649907831385791670714056075083613, -5345397569606273774674526242336093042974, -538157349970617081786595679016492695952]]]
 hmul := by decide  
 g := ![![![![62682261655876266170501047325497393151, -32793850120283888188187277560344129098, -3301578834175564918936169809917133104]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [17, 43, 84, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 108, 73], [80, 58, 94], [0, 1]]
 g := ![![[157, 51, 76], [162, 142, 144], [76, 31, 54], [100, 49], [85, 25], [166, 83, 1], []], ![[7, 47, 133, 67], [72, 27, 71, 156], [28, 55, 68, 161], [5, 42], [31, 94], [103, 45, 104, 82], [161, 152]], ![[28, 91, 64, 112], [75, 70, 149, 99], [133, 125, 15, 81], [4, 84], [118, 33], [28, 85, 156, 61], [140, 152]]]
 h' := ![![[3, 108, 73], [85, 71, 110], [44, 162, 12], [139, 111, 80], [13, 9, 160], [17, 135, 5], [0, 0, 1], [0, 1]], ![[80, 58, 94], [150, 108, 40], [25, 32, 164], [0, 159, 51], [98, 26, 84], [142, 11, 125], [111, 159, 58], [3, 108, 73]], ![[0, 1], [71, 155, 17], [122, 140, 158], [126, 64, 36], [148, 132, 90], [22, 21, 37], [12, 8, 108], [80, 58, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [153, 26], []]
 b := ![[], [24, 88, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [17, 43, 84, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![75651, -1670, 1670]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![453, -10, 10]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [55, 106, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [101, 59, 46], [53, 113, 127], [0, 1]]
 g := ![![[146, 155, 78], [52, 40], [8, 95, 113], [125, 79, 116], [90, 84], [82, 154, 1], []], ![[31, 21, 171, 63], [140, 126], [15, 159, 122, 129], [50, 163, 7, 19], [47, 31], [105, 79, 112, 39], [170, 40]], ![[30, 122, 146, 32], [22, 21], [92, 52, 121, 65], [22, 39, 133, 79], [134, 121], [112, 36, 97, 72], [89, 40]]]
 h' := ![![[101, 59, 46], [94, 70, 50], [79, 104, 127], [45, 111, 74], [38, 1, 17], [161, 138, 55], [0, 0, 1], [0, 1]], ![[53, 113, 127], [63, 78, 47], [155, 162, 105], [13, 123, 147], [74, 93, 64], [8, 121, 107], [159, 2, 113], [101, 59, 46]], ![[0, 1], [17, 25, 76], [169, 80, 114], [171, 112, 125], [94, 79, 92], [5, 87, 11], [163, 171, 59], [53, 113, 127]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [145, 164], []]
 b := ![[], [154, 112, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [55, 106, 19, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-381119, 374718, -86846]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2203, 2166, -502]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀

instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [160, 6, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 90, 31], [27, 88, 148], [0, 1]]
 g := ![![[155, 120, 4], [98, 170, 177], [11, 60], [123, 57], [33, 39, 108], [23, 108, 1], []], ![[129, 81, 161, 46], [44, 115, 119, 14], [150, 15], [54, 29], [155, 168, 134, 145], [162, 56, 178, 25], [178, 66]], ![[174, 130, 47, 30], [7, 99, 68, 162], [124, 15], [17, 126], [77, 130, 100, 163], [95, 69, 123, 37], [61, 66]]]
 h' := ![![[81, 90, 31], [72, 101, 2], [12, 170, 78], [55, 148, 113], [90, 161, 93], [79, 124, 65], [0, 0, 1], [0, 1]], ![[27, 88, 148], [36, 137, 85], [125, 147, 141], [26, 173, 33], [49, 120, 108], [25, 54, 77], [98, 88, 88], [81, 90, 31]], ![[0, 1], [131, 120, 92], [74, 41, 139], [89, 37, 33], [126, 77, 157], [131, 1, 37], [98, 91, 90], [27, 88, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [140, 89], []]
 b := ![[], [66, 75, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [160, 6, 71, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19690, 0, -6802]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![110, 0, -38]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def PBC179 : ContainsPrimesAboveP 179 ![I179N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![179, 0, 0]]) timesTableT_eq_Table B_one_repr 179 (by decide) 𝕀

instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [158, 63, 105, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 19, 144], [51, 161, 37], [0, 1]]
 g := ![![[127, 82, 180], [68, 178], [2, 171, 75], [103, 126], [125, 47, 136], [102, 76, 1], []], ![[21, 168, 164, 3], [164, 176], [64, 29, 132, 34], [142, 81], [145, 43, 34, 168], [91, 82, 149, 42], [11, 102]], ![[20, 38, 150, 166], [95, 20], [164, 150, 30, 122], [43, 139], [65, 128, 140, 9], [13, 137, 106, 144], [118, 102]]]
 h' := ![![[25, 19, 144], [60, 53, 162], [46, 162, 97], [95, 54, 165], [160, 133, 44], [174, 28, 91], [0, 0, 1], [0, 1]], ![[51, 161, 37], [88, 58, 48], [29, 178, 30], [67, 103, 132], [125, 133, 172], [46, 114, 40], [154, 69, 161], [25, 19, 144]], ![[0, 1], [61, 70, 152], [49, 22, 54], [164, 24, 65], [73, 96, 146], [6, 39, 50], [66, 112, 19], [51, 161, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [173, 175], []]
 b := ![[], [123, 165, 83], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [158, 63, 105, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![742281, -319827, -16833]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4101, -1767, -93]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def PBC181 : ContainsPrimesAboveP 181 ![I181N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![181, 0, 0]]) timesTableT_eq_Table B_one_repr 181 (by decide) 𝕀

instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-192288884344, 81970387874, 21485010603]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-192288884344, 81970387874, 21485010603]] 
 ![![191, 0, 0], ![0, 191, 0], ![182, 117, 1]] where
  M :=![![![-192288884344, 81970387874, 21485010603], ![1998105986079, -1352479456906, 81970387874], ![7623246072282, -2428294959117, -1352479456906]]]
  hmulB := by decide  
  f := ![![![-10619104507979309809634, -307284412200845504923, -187315078325545014734]], ![![-17420302284275686370262, -504090278399879013998, -307284412200845504923]], ![![-20939423235849048809591, -605922877585181966692, -369359742204963328647]]]
  g := ![![![-21479375990, -12731810747, 21485010603], ![-67646620979, -57293271404, 81970387874], ![1328662341514, 815768594235, -1352479456906]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [13, 117, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 190], [0, 1]]
 g := ![![[9, 147], [175, 96], [185, 109], [116, 156], [19, 78], [99, 128], [1]], ![[0, 44], [21, 95], [38, 82], [9, 35], [61, 113], [21, 63], [1]]]
 h' := ![![[74, 190], [17, 23], [78, 67], [20, 142], [135, 27], [50, 101], [178, 74], [0, 1]], ![[0, 1], [0, 168], [70, 124], [23, 49], [32, 164], [75, 90], [115, 117], [74, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [6, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [13, 117, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-661, 762, -160]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![149, 102, -160]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10619104507979309809634, 307284412200845504923, 187315078325545014734]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![10619104507979309809634, 307284412200845504923, 187315078325545014734]] 
 ![![191, 0, 0], ![74, 1, 0], ![63, 0, 1]] where
  M :=![![![10619104507979309809634, 307284412200845504923, 187315078325545014734], ![17420302284275686370262, 504090278399879013998, 307284412200845504923], ![28577450334678631957839, 826944025430029104420, 504090278399879013998]]]
  hmulB := by decide  
  f := ![![![192288884344, -81970387874, -21485010603]], ![![64038070447, -24677116470, -8753199856]], ![![23512846290, -14323766895, -5634613]]]
  g := ![![![-125239748321427191010, 307284412200845504923, 187315078325545014734], ![-205451813015542552229, 504090278399879013998, 307284412200845504923], ![-337037147048879055765, 826944025430029104420, 504090278399879013998]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-192288884344, 81970387874, 21485010603]] ![![10619104507979309809634, 307284412200845504923, 187315078325545014734]]
  ![![191, 0, 0]] where
 M := ![![![-191, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1166347329592, 787982857699, -46936846174]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-1166347329592, 787982857699, -46936846174]] 
 ![![193, 0, 0], ![0, 193, 0], ![123, 29, 1]] where
  M :=![![![-1166347329592, 787982857699, -46936846174], ![-4365126694182, 1368242363804, 787982857699], ![73282405766007, -46916201009928, 1368242363804]]]
  hmulB := by decide  
  f := ![![![-201249996426382035231016, -5823559492312659391132, -3549937644487569829329]], ![![-330144200937343994127597, -9553363624053264447250, -5823559492312659391132]], ![![-180671100623901779722749, -5228069176188923114435, -3186937405041924745065]]]
  g := ![![![23869869170, 11135499465, -46936846174], ![-524803203063, -111312230619, 787982857699], ![-492287072445, -448679945908, 1368242363804]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [44, 190, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 192], [0, 1]]
 g := ![![[171, 151], [101], [98], [138], [63], [67], [3, 1]], ![[45, 42], [101], [98], [138], [63], [67], [6, 192]]]
 h' := ![![[3, 192], [95, 94], [183, 78], [40, 171], [124, 157], [1, 177], [61, 158], [0, 1]], ![[0, 1], [184, 99], [31, 115], [167, 22], [16, 36], [146, 16], [149, 35], [3, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [178]]
 b := ![[], [156, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [44, 190, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![416, 346, 165]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-103, -23, 165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1226771647512882081826082794, -957134394975278752093806656, 127595503170434593237597257]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![1226771647512882081826082794, -957134394975278752093806656, 127595503170434593237597257]] 
 ![![193, 0, 0], ![164, 1, 0], ![124, 0, 1]] where
  M :=![![![1226771647512882081826082794, -957134394975278752093806656, 127595503170434593237597257], ![11866381794850417171096544901, -5663385523690585953004169084, -957134394975278752093806656], ![-89013498732700923944724019008, 63551639123515469784162104325, -5663385523690585953004169084]]]
  hmulB := by decide  
  f := ![![![92901395252121326126126262550586956001195662653912786256, 2688282294541492063185753874656741971465815332139213421, 1638728775588148450800135429937309385085990608632504924]], ![![79731764753769923785539480068810521020772465294531191212, 2307193459456818695053795776050144728118890592013412028, 1406423841922268590644600851732515446246467746880155549]], ![![60983332977489135759149905008372329261629963704529183129, 1764671174858042747914069254974827517179296372293097914, 1075711966545552941358216283140925455736865312218591352]]]
  g := ![![![737694145234843045926157070, -957134394975278752093806656, 127595503170434593237597257], ![5488840790969124760224934197, -5663385523690585953004169084, -957134394975278752093806656], ![-50824987098712980882770943844, 63551639123515469784162104325, -5663385523690585953004169084]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-1166347329592, 787982857699, -46936846174]] ![![1226771647512882081826082794, -957134394975278752093806656, 127595503170434593237597257]]
  ![![193, 0, 0]] where
 M := ![![![12097676499584119370906702133820996878143, -6329213073214790420320144569146416915914, -637204714995884029354680773314006689072]]]
 hmul := by decide  
 g := ![![![![62682261655876266170501047325497393151, -32793850120283888188187277560344129098, -3301578834175564918936169809917133104]]]]
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


lemma PB263I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB263I3 : PrimesBelowBoundCertificateInterval O 137 193 263 where
  m := 11
  g := ![1, 3, 3, 3, 2, 1, 1, 1, 1, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB263I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0]
    · exact ![I181N0]
    · exact ![I191N0, I191N1]
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
    · exact ![2685619]
    · exact ![149, 149, 149]
    · exact ![151, 151, 151]
    · exact ![157, 157, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![5735339]
    · exact ![5929741]
    · exact ![36481, 191]
    · exact ![37249, 193]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I149N0, I149N1, I149N2, I151N0, I151N1, I151N2, I157N0, I157N1, I157N2, I163N1, I191N1, I193N1]
  Il := ![[], [I149N0, I149N1, I149N2], [I151N0, I151N1, I151N2], [I157N0, I157N1, I157N2], [I163N1], [], [], [], [], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
