
import IdealArithmetic.Examples.NF3_1_401464_1.RI3_1_401464_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-62502955712071898174220, 8355079171263296450498, -2679758919073340416711]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-62502955712071898174220, 8355079171263296450498, -2679758919073340416711]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-62502955712071898174220, 8355079171263296450498, -2679758919073340416711], ![327246390540990806039107, -43744643278558515257243, 14030399423453252484285], ![-825429609478711831356469, 110339257702777371099307, -35389564107295218806745]]]
  hmulB := by decide  
  f := ![![![104013386460, 50022310267, 11955563843]], ![![-634338200295, 35173374913, 61977874110]], ![![-3352927721941, -551678346989, 35173374913]]]
  g := ![![![-35429017441667597312359, 8355079171263296450498, -2679758919073340416711], ![185495516909774660648175, -43744643278558515257243, 14030399423453252484285], ![-467884433590744601227888, 110339257702777371099307, -35389564107295218806745]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-953076959612761396192844433, 127402510219745377851441190, -40862331292795378899408609]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-953076959612761396192844433, 127402510219745377851441190, -40862331292795378899408609]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-953076959612761396192844433, 127402510219745377851441190, -40862331292795378899408609], ![4990019934062395466881065661, -667040640563193743896984170, 213942689146695376803473771], ![-12586571844703591093658759243, 1682509299907891225702654037, -539638130343448366045542980]]]
  hmulB := by decide  
  f := ![![![-35216297863073, -6068060941667, 260920692040]], ![![-36166960578750, -21555401824510, -5807140249627]], ![![335222475298390, 9985181025741, -21424941478490]]]
  g := ![![![-519808569269855697572438507, 127402510219745377851441190, -40862331292795378899408609], ![2721558942739446916987288030, -667040640563193743896984170, 213942689146695376803473771], ![-6864721507134016976657935150, 1682509299907891225702654037, -539638130343448366045542980]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-62502955712071898174220, 8355079171263296450498, -2679758919073340416711]] ![![-953076959612761396192844433, 127402510219745377851441190, -40862331292795378899408609]]
  ![![134991116773547766594422177773286931953543008176211, -18044930119079213263244487772550257783936845150767, 5787624681879129433396396494534521135602853486718]] where
 M := ![![![134991116773547766594422177773286931953543008176211, -18044930119079213263244487772550257783936845150767, 5787624681879129433396396494534521135602853486718]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![134991116773547766594422177773286931953543008176211, -18044930119079213263244487772550257783936845150767, 5787624681879129433396396494534521135602853486718]] ![![-953076959612761396192844433, 127402510219745377851441190, -40862331292795378899408609]]
  ![![2, 0, 0]] where
 M := ![![![-291547838020883760680315963681120665090379349529875734931876723695173206129824, 38972641231503513141001792473675375447910475828284172557568844335852014470046, -12499855572783989513153155101352576698512164034744652730734979757797915572496]]]
 hmul := by decide  
 g := ![![![![-145773919010441880340157981840560332545189674764937867465938361847586603064912, 19486320615751756570500896236837687723955237914142086278784422167926007235023, -6249927786391994756576577550676288349256082017372326365367489878898957786248]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 6, 2]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![5, 6, 2]] 
 ![![3, 0, 0], ![0, 3, 0], ![1, 0, 1]] where
  M :=![![![5, 6, 2], ![-232, -9, 14], ![-840, -168, -3]]]
  hmulB := by decide  
  f := ![![![-793, 106, -34]], ![![4152, -555, 178]], ![![-3755, 502, -161]]]
  g := ![![![1, 2, 2], ![-82, -3, 14], ![-279, -56, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2], [0, 1]]
 g := ![![[2, 1]], ![[1, 2]]]
 h' := ![![[2, 2], [0, 1]], ![[0, 1], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-725, -279, -20]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-235, -93, -20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-793, 106, -34]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-793, 106, -34]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![-793, 106, -34], ![4152, -555, 178], ![-10472, 1400, -449]]]
  hmulB := by decide  
  f := ![![![5, 6, 2]], ![![-74, 1, 6]], ![![-280, -56, -1]]]
  g := ![![![-335, 106, -34], ![1754, -555, 178], ![-4424, 1400, -449]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![5, 6, 2]] ![![-793, 106, -34]]
  ![![3, 0, 0]] where
 M := ![![![3, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [4, 1, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 4, 2], [4, 0, 3], [0, 1]]
 g := ![![[0, 4, 1], []], ![[4, 3], [2, 4]], ![[4, 2, 4, 3], [1, 4]]]
 h' := ![![[0, 4, 2], [0, 0, 1], [0, 1]], ![[4, 0, 3], [2, 2], [0, 4, 2]], ![[0, 1], [2, 3, 4], [4, 0, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 4], []]
 b := ![[], [0, 4, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [4, 1, 1, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![876775, 94815, 8305]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![175355, 18963, 1661]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 125 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def PBC5 : ContainsPrimesAboveP 5 ![I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![5, 0, 0]]) timesTableT_eq_Table B_one_repr 5 (by decide) 𝕀


def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![234664532240949660100109607671349468, -31368768456207939268778364908229421, 10061034171883211008128505707401416]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![234664532240949660100109607671349468, -31368768456207939268778364908229421, 10061034171883211008128505707401416]] 
 ![![7, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![234664532240949660100109607671349468, -31368768456207939268778364908229421, 10061034171883211008128505707401416], ![-1228631834910310049236070544088997925, 164237293037767183043210067719539556, -52676502740532667529428224109057426], ![3099038293460102479472529564513011891, -414263773635186718630647305208683261, 132868524581559243774431702811310135]]]
  hmulB := by decide  
  f := ![![![814649238022253874, 198617896835584259, 17056578089319050]], ![![-145209379681589831, 127695869747514969, 61621278549972374]], ![![-3530013449008803853, -352127099639455709, 127695869747514969]]]
  g := ![![![38004757242451085624126853225654127, -31368768456207939268778364908229421, 10061034171883211008128505707401416], ![-198981303992582461754182944544076783, 164237293037767183043210067719539556, -52676502740532667529428224109057426], ![501900295299327028300453838531670736, -414263773635186718630647305208683261, 132868524581559243774431702811310135]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![920213379427080038199, -123009472943757880960, 39453334372378505614]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![920213379427080038199, -123009472943757880960, 39453334372378505614]] 
 ![![7, 0, 0], ![6, 1, 0], ![0, 0, 1]] where
  M :=![![![920213379427080038199, -123009472943757880960, 39453334372378505614], ![-4817956263256800049026, 644040038820430498901, -206565611515137256306], ![12152567214847341980558, -1624493754853540686962, 521030565876672617941]]]
  hmulB := by decide  
  f := ![![![37286900469, -2695301308, -3891996454]], ![![97739097076, 6908438257, -4662082542]], ![![80848090322, 37723269394, 8833653477]]]
  g := ![![![236895745298518189137, -123009472943757880960, 39453334372378505614], ![-1240313785168483291776, 644040038820430498901, -206565611515137256306], ![3128504249138369443190, -1624493754853540686962, 521030565876672617941]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![234664532240949660100109607671349468, -31368768456207939268778364908229421, 10061034171883211008128505707401416]] ![![920213379427080038199, -123009472943757880960, 39453334372378505614]]
  ![![489342190724045337146903996330858327775735909207947592206, -65412790463430293767470696329985795444047929355431233793, 20980113422354174000182638601063313588002663255811296634]] where
 M := ![![![489342190724045337146903996330858327775735909207947592206, -65412790463430293767470696329985795444047929355431233793, 20980113422354174000182638601063313588002663255811296634]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![489342190724045337146903996330858327775735909207947592206, -65412790463430293767470696329985795444047929355431233793, 20980113422354174000182638601063313588002663255811296634]] ![![920213379427080038199, -123009472943757880960, 39453334372378505614]]
  ![![7, 0, 0]] where
 M := ![![![1020417433073093162381105872883922327816327723354565072261568532933106221454384, -136404244310262295993506273657863814067686665398994603951490955175482050645161, 43749494504743963296036042854734018444792574121606284557572429152292704503736]]]
 hmul := by decide  
 g := ![![![![145773919010441880340157981840560332545189674764937867465938361847586603064912, -19486320615751756570500896236837687723955237914142086278784422167926007235023, 6249927786391994756576577550676288349256082017372326365367489878898957786248]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N1
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [4, 7, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2, 6], [2, 8, 5], [0, 1]]
 g := ![![[5, 4, 5], [9, 4, 1], []], ![[1, 3, 4, 2], [6, 0, 1, 10], [3, 3]], ![[0, 8, 5, 9], [6, 6, 7, 9], [4, 3]]]
 h' := ![![[2, 2, 6], [8, 9, 4], [0, 0, 1], [0, 1]], ![[2, 8, 5], [5, 6, 9], [3, 8, 8], [2, 2, 6]], ![[0, 1], [0, 7, 9], [10, 3, 2], [2, 8, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 5], []]
 b := ![[], [1, 0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [4, 7, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2223662507, -202298965, 25381708]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-202151137, -18390815, 2307428]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15651825360058395206206, -2092256895185790885713, 671058162458928906344]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![15651825360058395206206, -2092256895185790885713, 671058162458928906344]] 
 ![![13, 0, 0], ![0, 13, 0], ![2, 3, 1]] where
  M :=![![![15651825360058395206206, -2092256895185790885713, 671058162458928906344], ![-81948178227798330740649, 10954418222845892861798, -3513455627912652865082], ![206701906292196594300175, -27630865968611984899681, 8862161327660101976085]]]
  hmulB := by decide  
  f := ![![![97739097076, 6908438257, -4662082542]], ![![561696260755, 130373674870, 9154793972]], ![![104013386460, 50022310267, 11955563843]]]
  g := ![![![1100746848856964414886, -315802414043275200365, 671058162458928906344], ![-5763174382459463462345, 1653445008198757804388, -3513455627912652865082], ![14536737202836645411385, -4170565380891714679072, 8862161327660101976085]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [12, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 12], [0, 1]]
 g := ![![[11, 12], [12], [11, 1]], ![[0, 1], [12], [9, 12]]]
 h' := ![![[11, 12], [3, 8], [11, 5], [0, 1]], ![[0, 1], [0, 5], [1, 8], [11, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [3, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [12, 2, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-372, -1507, -173]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -76, -173]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97739097076, 6908438257, -4662082542]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![97739097076, 6908438257, -4662082542]] 
 ![![13, 0, 0], ![6, 1, 0], ![2, 0, 1]] where
  M :=![![![97739097076, 6908438257, -4662082542], ![561696260755, 130373674870, 9154793972], ![-528392952437, 245352132347, 137282113127]]]
  hmulB := by decide  
  f := ![![![15651825360058395206206, -2092256895185790885713, 671058162458928906344]], ![![920213379427080038199, -123009472943757880960, 39453334372378505614]], ![![18308119770177952670199, -2447336904537197436239, 784944434813689214521]]]
  g := ![![![5047125586, 6908438257, -4662082542], ![-18373490493, 130373674870, 9154793972], ![-175005382521, 245352132347, 137282113127]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![15651825360058395206206, -2092256895185790885713, 671058162458928906344]] ![![97739097076, 6908438257, -4662082542]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [3, 13, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 1, 11], [12, 15, 6], [0, 1]]
 g := ![![[13, 12, 13], [9, 4], [7, 1], []], ![[0, 2, 9, 14], [6, 1], [9, 4], [2, 2]], ![[0, 11, 10, 12], [7, 1], [6, 1], [7, 2]]]
 h' := ![![[12, 1, 11], [6, 11, 8], [13, 8, 2], [0, 0, 1], [0, 1]], ![[12, 15, 6], [1, 15, 3], [11, 9, 16], [2, 9, 15], [12, 1, 11]], ![[0, 1], [0, 8, 6], [15, 0, 16], [4, 8, 1], [12, 15, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 11], []]
 b := ![[], [6, 4, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [3, 13, 10, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-76840, -8075, 2142]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4520, -475, 126]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [13, 13, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 17, 14], [5, 1, 5], [0, 1]]
 g := ![![[9, 15, 7], [4, 9, 5], [2, 1], []], ![[17, 2, 18, 12], [18, 14, 14, 15], [7, 1], [13, 6]], ![[10, 11, 6, 11], [5, 10, 18, 9], [18, 4], [3, 6]]]
 h' := ![![[16, 17, 14], [5, 13, 11], [12, 18, 10], [0, 0, 1], [0, 1]], ![[5, 1, 5], [11, 11, 3], [11, 8, 15], [11, 12, 1], [16, 17, 14]], ![[0, 1], [11, 14, 5], [0, 12, 13], [5, 7, 17], [5, 1, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 5], []]
 b := ![[], [7, 3, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [13, 13, 17, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1749121, -511537, -80769]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-92059, -26923, -4251]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [8, 19, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 10, 14], [8, 12, 9], [0, 1]]
 g := ![![[22, 5, 4], [16, 5, 3], [7, 16, 1], []], ![[17, 13, 2, 20], [0, 0, 3, 5], [9, 20, 5, 15], [12, 12]], ![[16, 18, 11, 1], [21, 7, 12, 13], [18, 11, 17, 3], [17, 12]]]
 h' := ![![[8, 10, 14], [10, 9, 21], [13, 15, 7], [0, 0, 1], [0, 1]], ![[8, 12, 9], [8, 4, 10], [1, 14, 18], [14, 20, 12], [8, 10, 14]], ![[0, 1], [19, 10, 15], [20, 17, 21], [20, 3, 10], [8, 12, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 19], []]
 b := ![[], [18, 5, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [8, 19, 7, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-146602, -15525, -7659]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6374, -675, -333]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀

instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![621005772788, -83012912563, 26625072998]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![621005772788, -83012912563, 26625072998]] 
 ![![29, 0, 0], ![0, 29, 0], ![27, 6, 1]] where
  M :=![![![621005772788, -83012912563, 26625072998], ![-3251396599325, 434630261802, -139400752128], ![8201156996123, -1096289210933, 351617349239]]]
  hmulB := by decide  
  f := ![![![-177474, -106813, -28908]], ![![3333239, 24882, -242534]], ![![1025503, -5716, -79919]]]
  g := ![![![-3374868902, -8371150019, 26625072998], ![17669783039, 43828785330, -139400752128], ![-44569359770, -110551493323, 351617349239]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [12, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 28], [0, 1]]
 g := ![![[14, 7], [28], [0, 25], [6, 1]], ![[27, 22], [28], [5, 4], [12, 28]]]
 h' := ![![[6, 28], [12, 23], [0, 12], [15, 24], [0, 1]], ![[0, 1], [5, 6], [14, 17], [14, 5], [6, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [14, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [12, 23, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1897, -1037, 6]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-71, -37, 6]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![177474, 106813, 28908]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![177474, 106813, 28908]] 
 ![![29, 0, 0], ![16, 1, 0], ![3, 0, 1]] where
  M :=![![![177474, 106813, 28908], ![-3333239, -24882, 242534], ![-14531951, -2568895, 81931]]]
  hmulB := by decide  
  f := ![![![-621005772788, 83012912563, -26625072998]], ![![-230506750527, 30812977214, -9882772960]], ![![-347040493603, 46390618918, -14879054077]]]
  g := ![![![-55802, 106813, 28908], ![-126301, -24882, 242534], ![907744, -2568895, 81931]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![621005772788, -83012912563, 26625072998]] ![![177474, 106813, 28908]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19967807841872582361, -2671137806659397680, 453008710914798900]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-19967807841872582361, -2671137806659397680, 453008710914798900]] 
 ![![31, 0, 0], ![0, 31, 0], ![19, 8, 1]] where
  M :=![![![-19967807841872582361, -2671137806659397680, 453008710914798900], ![-56579174405520466780, -23138868818276174661, -4889266902403996460], ![289325850204835993220, -9841584141016546940, -25810006624935572341]]]
  hmulB := by decide  
  f := ![![![-17712781480171836683495590100997832871, 2367755091325043949934303219988320480, -759419832427539501008380330146544700]], ![![92738715150202244569931562507427139780, -12396842653179060176436927789972019971, 3976090350222548398860226109830096260]], ![![5530563440438961874012327927776789441, -739297764083773078992123318731741868, 237118013671068401458708323737829719]]]
  g := ![![![-921773333846895531, -203071209483154480, 453008710914798900], ![1171512798069531160, 515331174224380549, -4889266902403996460], ![25152128260600382829, 6343176414789291348, -25810006624935572341]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [28, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 30], [0, 1]]
 g := ![![[12, 10], [13, 16], [17, 9], [5, 1]], ![[0, 21], [0, 15], [0, 22], [10, 30]]]
 h' := ![![[5, 30], [8, 17], [20, 27], [15, 28], [0, 1]], ![[0, 1], [0, 14], [0, 4], [0, 3], [5, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [6, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [28, 26, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1652, -1575, -255]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![103, 15, -255]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-119817553748090699454, 18452014737791243515, 16388201151567647254]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-119817553748090699454, 18452014737791243515, 16388201151567647254]] 
 ![![31, 0, 0], ![14, 1, 0], ![11, 0, 1]] where
  M :=![![![-119817553748090699454, 18452014737791243515, 16388201151567647254], ![-1931743922298758779711, -234534961809064230232, 53292230627150134284], ![-3228246426345919755287, -1161620775713300481607, -216082947071272986717]]]
  hmulB := by decide  
  f := ![![![-112584368019553306199098247410197087942732, 15049709210285120271379374397354583666923, -4826955156144124749162415449624412751188]], ![![-31829799338139042624698988736777404198063, 4254846677982169382075803300004450730726, -1364674481341665506279918804827645933354]], ![![-87911137722643091009257874241000820013195, 11751516505749043234927408739217946386856, -3769112239801441449173178542301295331631]]]
  g := ![![![-18013418475626200918, 18452014737791243515, 16388201151567647254], ![24694548584822224723, -234534961809064230232, 53292230627150134284], ![497140543594331930358, -1161620775713300481607, -216082947071272986717]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-19967807841872582361, -2671137806659397680, 453008710914798900]] ![![-119817553748090699454, 18452014737791243515, 16388201151567647254]]
  ![![31, 0, 0]] where
 M := ![![![6090024360847572153497630699477960417074, -268195411285738014169136965842031809455, -567474800801278434555332074487094759114]]]
 hmul := by decide  
 g := ![![![![196452398737018456564439699983160013454, -8651464880185097231262482769097800305, -18305638735525110792107486273777250294]]]]
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


lemma PB180I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB180I0 : PrimesBelowBoundCertificateInterval O 1 31 180 where
  m := 11
  g := ![3, 2, 1, 3, 1, 2, 1, 1, 1, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB180I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N1]
    · exact ![I5N0]
    · exact ![I7N0, I7N1, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0]
    · exact ![I23N0]
    · exact ![I29N0, I29N1]
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
    · exact ![9, 3]
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![1331]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![6859]
    · exact ![12167]
    · exact ![841, 29]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I7N0, I7N1, I13N0, I13N1, I29N1, I31N1]
  Il := ![[I2N0, I2N1, I2N1], [I3N0, I3N1], [I5N0], [I7N0, I7N1, I7N1], [], [I13N0, I13N1], [], [], [], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
