
import IdealArithmetic.Examples.NF3_1_390104_1.RI3_1_390104_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-217665479381427814379588279, -4849191683552463574582626, -8100382598086962289119499]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-217665479381427814379588279, -4849191683552463574582626, -8100382598086962289119499]] 
 ![![83, 0, 0], ![0, 83, 0], ![71, 38, 1]] where
  M :=![![![-217665479381427814379588279, -4849191683552463574582626, -8100382598086962289119499], ![-826239025004870153490188898, -18407105343788255866137677, -30748340246831315301986876], ![-1320856576727221438097616750, -29426286360306195414167958, -49155445590619571168124553]]]
  hmulB := by decide  
  f := ![![![-2960409715231, -60257361408, 525542284909]], ![![53605313060718, -15513167191639, 870312485594]], ![![22581588779795, -7022562507712, 671596650302]]]
  g := ![![![4306767290153572387324050, 3650184904141591607372992, -8100382598086962289119499], ![16348110030363291963263606, 13855781012479538862763417, -30748340246831315301986876], ![26134699520563471263123211, 22150369229918524204512832, -49155445590619571168124553]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [73, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 82], [0, 1]]
 g := ![![[32, 49], [43, 10], [10], [49], [24, 61], [1]], ![[25, 34], [6, 73], [10], [49], [39, 22], [1]]]
 h' := ![![[71, 82], [15, 76], [34, 50], [73, 33], [74, 7], [10, 71], [0, 1]], ![[0, 1], [16, 7], [15, 33], [9, 50], [73, 76], [71, 12], [71, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [27, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [73, 12, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![889, 491, -413]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![364, 195, -413]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2960409715231, 60257361408, -525542284909]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![2960409715231, 60257361408, -525542284909]] 
 ![![83, 0, 0], ![50, 1, 0], ![41, 0, 1]] where
  M :=![![![2960409715231, 60257361408, -525542284909], ![-53605313060718, 15513167191639, -870312485594], ![-47459062197102, -10905937802154, 14642854706045]]]
  hmulB := by decide  
  f := ![![![217665479381427814379588279, 4849191683552463574582626, 8100382598086962289119499]], ![![141078469808147721355055456, 3142972162908571501147819, 5250210483749149756120022]], ![![123435436522479058164587183, 2749917414288640987615128, 4593628097737168976168964]]]
  g := ![![![258973196700, 60257361408, -525542284909], ![-9561215189558, 15513167191639, -870312485594], ![-1235171265509, -10905937802154, 14642854706045]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-217665479381427814379588279, -4849191683552463574582626, -8100382598086962289119499]] ![![2960409715231, 60257361408, -525542284909]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [64, 73, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 70, 28], [11, 18, 61], [0, 1]]
 g := ![![[79, 52, 5], [68, 5], [35, 88], [72], [88, 28, 1], []], ![[0, 24, 22, 14], [50, 50], [71, 36], [22, 47, 63, 82], [23, 27, 18, 83], [62, 72]], ![[1, 58, 24, 74], [83, 88], [50, 72], [70, 87, 49, 7], [64, 41, 37, 38], [29, 72]]]
 h' := ![![[17, 70, 28], [49, 7, 70], [29, 59, 19], [20, 86, 34], [64, 61], [0, 0, 1], [0, 1]], ![[11, 18, 61], [26, 33, 32], [17, 48, 36], [17, 41, 83], [33, 87, 17], [59, 10, 18], [17, 70, 28]], ![[0, 1], [72, 49, 76], [20, 71, 34], [4, 51, 61], [23, 30, 72], [45, 79, 70], [11, 18, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 70], []]
 b := ![[], [24, 82, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [64, 73, 61, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![921417, -428001, 129851]
  a := ![-1, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10353, -4809, 1459]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![86325492940381166244385, 1923175248710479831416, 3212588062988950441887]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![86325492940381166244385, 1923175248710479831416, 3212588062988950441887]] 
 ![![97, 0, 0], ![0, 97, 0], ![21, 61, 1]] where
  M :=![![![86325492940381166244385, 1923175248710479831416, 3212588062988950441887], ![327683982424872945072474, 7300204179935875807681, 12194701872109340378022], ![523847857793341887876906, 11670379164749591999982, 19494906052045216185703]]]
  hmulB := by decide  
  f := ![![![121137243187, -24566942262, -4594919535]], ![![-468681792570, 255982254289, -82890665856]], ![![-299177496321, 160885667905, -51337446794]]]
  g := ![![![194444779563022752214, -2000460789624902032203, 3212588062988950441887], ![738095289799760795196, -7593573299162205023213, 12194701872109340378022], ![1179946708251467504919, -12139370000103181395133, 19494906052045216185703]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [7, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 96], [0, 1]]
 g := ![![[80, 54], [27], [73], [64], [64], [22, 1]], ![[7, 43], [27], [73], [64], [64], [44, 96]]]
 h' := ![![[22, 96], [84, 65], [46, 67], [84, 48], [85, 89], [40, 89], [0, 1]], ![[0, 1], [59, 32], [65, 30], [73, 49], [6, 8], [58, 8], [22, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [26, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [7, 75, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-697, 114, 13]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, -7, 13]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![121137243187, -24566942262, -4594919535]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![121137243187, -24566942262, -4594919535]] 
 ![![97, 0, 0], ![9, 1, 0], ![73, 0, 1]] where
  M :=![![![121137243187, -24566942262, -4594919535], ![-468681792570, 255982254289, -82890665856], ![-2974509903294, 506898062658, 173091588433]]]
  hmulB := by decide  
  f := ![![![86325492940381166244385, 1923175248710479831416, 3212588062988950441887]], ![![11387767205034056095587, 253698777508558704025, 423793757103194787165]], ![![70367101468465639419763, 1567651261037264120550, 2618699326291119571582]]]
  g := ![![![6986276800, -24566942262, -4594919535], ![33798933261, 255982254289, -82890665856], ![-207961633225, 506898062658, 173091588433]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![86325492940381166244385, 1923175248710479831416, 3212588062988950441887]] ![![121137243187, -24566942262, -4594919535]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-128283516503, -2857923834, -4774048543]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-128283516503, -2857923834, -4774048543]] 
 ![![101, 0, 0], ![0, 101, 0], ![33, 83, 1]] where
  M :=![![![-128283516503, -2857923834, -4774048543], ![-486952951386, -10848427637, -18121868588], ![-778461182454, -17342701758, -28970296225]]]
  hmulB := by decide  
  f := ![![![-140521, 42456, -3401]], ![![-346902, -101353, 120566]], ![![-291549, -80113, 98158]]]
  g := ![![![289703816, 3894931735, -4774048543], ![1099690218, 14784818467, -18121868588], ![1758005871, 23635563217, -28970296225]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [24, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 100], [0, 1]]
 g := ![![[41, 80], [92], [29, 25], [14], [96], [26, 1]], ![[0, 21], [92], [73, 76], [14], [96], [52, 100]]]
 h' := ![![[26, 100], [34, 22], [11, 30], [52, 96], [40, 32], [83, 46], [0, 1]], ![[0, 1], [0, 79], [84, 71], [23, 5], [64, 69], [67, 55], [26, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [100, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [24, 75, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1732, 2526, -2093]
  a := ![1, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![701, 1745, -2093]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![140521, -42456, 3401]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![140521, -42456, 3401]] 
 ![![101, 0, 0], ![52, 1, 0], ![25, 0, 1]] where
  M :=![![![140521, -42456, 3401], ![346902, 101353, -120566], ![-3983610, 1080162, -19213]]]
  hmulB := by decide  
  f := ![![![128283516503, 2857923834, 4774048543]], ![![70868275342, 1578816505, 2637350424]], ![![39460882129, 879116808, 1468529800]]]
  g := ![![![22408, -42456, 3401], ![-18904, 101353, -120566], ![-590809, 1080162, -19213]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-128283516503, -2857923834, -4774048543]] ![![140521, -42456, 3401]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26493690391225106335781749256707509815, 3241283578770777007572345224329659798, 2338396832875172995897724513198293977]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-26493690391225106335781749256707509815, 3241283578770777007572345224329659798, 2338396832875172995897724513198293977]] 
 ![![103, 0, 0], ![8, 1, 0], ![50, 0, 1]] where
  M :=![![![-26493690391225106335781749256707509815, 3241283578770777007572345224329659798, 2338396832875172995897724513198293977], ![238516476953267645581567900346225985654, -85856497959000035244899482797796225061, 14400644402062677014512484699385567348], ![569127401987886900353947113227851285050, -35699662898745534255577244146342543566, -71455853556937358230386998098410657713]]]
  hmulB := by decide  
  f := ![![![6649047495748142224642122389429315352167959819015617010789782488257900628461, 148128706084012601175977135620566719231948531974873235182235887928716819992, 247443135133202506773818924816881612255668157976282410136978403403989833301]], ![![761471648054095082408412713075305313275940103550541183692136476245341437130, 16964205778052138546624350904544890219956929625329629259980116719059828827, 28338033685282163798700200534276857089830360929004308805014482503165522262]], ![![3619424297005466526630925413942577644855678575978628411282028952707098155912, 80634201850310415072855788085811686608084356067182402885473246091441304070, 134696239724716870064669966558671203240685100061177388009608248149777180591]]]
  g := ![![![-1644114569564562836808220744769509583, 3241283578770777007572345224329659798, 2338396832875172995897724513198293977], ![1993555733224602687525626483100169114, -85856497959000035244899482797796225061, 14400644402062677014512484699385567348], ![42985605660434165882698203605040043876, -35699662898745534255577244146342543566, -71455853556937358230386998098410657713]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5996837036104040200850372221478870647980013, 133598641207303610923219374270548674551974, 223171237390825976250583939644931842415611]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![5996837036104040200850372221478870647980013, 133598641207303610923219374270548674551974, 223171237390825976250583939644931842415611]] 
 ![![103, 0, 0], ![22, 1, 0], ![52, 0, 1]] where
  M :=![![![5996837036104040200850372221478870647980013, 133598641207303610923219374270548674551974, 223171237390825976250583939644931842415611], ![22763466213864249577559561843783047926392322, 507128697516913159913138295729957755453375, 847138398403562785270826002101509708487144], ![36390527617009217891727938019379012730693670, 810714884059580910353245931115604974233622, 1354267095920475945183964297831467463940519]]]
  hmulB := by decide  
  f := ![![![1653584501668438246057, 1061215421475023838536, -936321081488943814869]], ![![-574037779370549783528, 450590430178432916623, -187262715449607573216]], ![![958501133644067487466, 124856818781550279722, -236054534951940082747]]]
  g := ![![![-82982887522131941791172998776792776677429, 133598641207303610923219374270548674551974, 223171237390825976250583939644931842415611], ![-314995746101874803637013910403442014902072, 507128697516913159913138295729957755453375, 847138398403562785270826002101509708487144], ![-503563969127828264908831222838840823566534, 810714884059580910353245931115604974233622, 1354267095920475945183964297831467463940519]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![846125030904200170831420349125705, 18850129449862166799756221296658, 31488394464845878291209016209726]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![846125030904200170831420349125705, 18850129449862166799756221296658, 31488394464845878291209016209726]] 
 ![![103, 0, 0], ![72, 1, 0], ![47, 0, 1]] where
  M :=![![![846125030904200170831420349125705, 18850129449862166799756221296658, 31488394464845878291209016209726], ![3211816235414279585703319653392052, 71553434298036925042647738795623, 119527177279278256981686696309426], ![5134529439300220599278454225651168, 114387993570533806047612980655276, 191080611577315182024334435105049]]]
  hmulB := by decide  
  f := ![![![-124337069589031049, 26908040101788134, 3657789288869010]], ![![-83292956339277636, 16488804220437575, 3411655608559914]], ![![-26467258959586705, 6647816791657954, 203143134332723]]]
  g := ![![![-19330474071200311829493702389231, 18850129449862166799756221296658, 31488394464845878291209016209726], ![-73376780254082107723364973460542, 71553434298036925042647738795623, 119527177279278256981686696309426], ![-117302862542835213507702901276369, 114387993570533806047612980655276, 191080611577315182024334435105049]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-26493690391225106335781749256707509815, 3241283578770777007572345224329659798, 2338396832875172995897724513198293977]] ![![5996837036104040200850372221478870647980013, 133598641207303610923219374270548674551974, 223171237390825976250583939644931842415611]]
  ![![-124337069589031049, 26908040101788134, 3657789288869010]] where
 M := ![![![-124337069589031049, 26908040101788134, 3657789288869010]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-124337069589031049, 26908040101788134, 3657789288869010]] ![![846125030904200170831420349125705, 18850129449862166799756221296658, 31488394464845878291209016209726]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4939, -1696, 247]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![4939, -1696, 247]] 
 ![![107, 0, 0], ![0, 107, 0], ![7, 101, 1]] where
  M :=![![![4939, -1696, 247], ![25194, 707, -4594], ![-147798, 45150, -3887]]]
  hmulB := by decide  
  f := ![![![-1912813, -42614, -71185]], ![![-7260870, -161759, -270212]], ![![-7087337, -157893, -263754]]]
  g := ![![![30, -249, 247], ![536, 4343, -4594], ![-1127, 4091, -3887]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [89, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 106], [0, 1]]
 g := ![![[23, 101], [101, 76], [87], [], [], [93, 1]], ![[0, 6], [0, 31], [87], [], [], [79, 106]]]
 h' := ![![[93, 106], [106, 84], [68, 66], [0, 27], [53], [69], [0, 1]], ![[0, 1], [0, 23], [0, 41], [50, 80], [53], [69], [93, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [79, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [89, 14, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![905, 493, -421]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![36, 402, -421]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1912813, 42614, 71185]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![1912813, 42614, 71185]] 
 ![![107, 0, 0], ![16, 1, 0], ![27, 0, 1]] where
  M :=![![![1912813, 42614, 71185], ![7260870, 161759, 270212], ![11607498, 258594, 431971]]]
  hmulB := by decide  
  f := ![![![-4939, 1696, -247]], ![![-974, 247, 6]], ![![135, 6, -26]]]
  g := ![![![-6458, 42614, 71185], ![-24514, 161759, 270212], ![-39189, 258594, 431971]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![4939, -1696, 247]] ![![1912813, 42614, 71185]]
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
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [104, 50, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 101, 76], [82, 7, 33], [0, 1]]
 g := ![![[65, 12, 28], [0, 94], [89, 108, 78], [67, 23, 75], [93, 78], [1]], ![[20, 19, 11, 24], [78, 35], [42, 78, 34, 6], [43, 77, 25, 65], [77, 28], [22, 2, 48, 33]], ![[12, 94, 104, 54], [19, 104], [5, 92, 18, 99], [40, 11, 36, 18], [6, 1], [63, 39, 64, 76]]]
 h' := ![![[107, 101, 76], [81, 21, 30], [9, 78, 58], [8, 8, 80], [54, 36, 82], [5, 59, 80], [0, 1]], ![[82, 7, 33], [106, 82, 62], [77, 41, 12], [98, 94, 78], [107, 32, 40], [102, 13, 30], [107, 101, 76]], ![[0, 1], [95, 6, 17], [0, 99, 39], [106, 7, 60], [96, 41, 96], [34, 37, 108], [82, 7, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 108], []]
 b := ![[], [41, 57, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [104, 50, 29, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![363406, -9387516, 6263031]
  a := ![1, -1, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3334, -86124, 57459]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, 14, -2]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-41, 14, -2]] 
 ![![113, 0, 0], ![25, 1, 0], ![26, 0, 1]] where
  M :=![![![-41, 14, -2], ![-204, -7, 38], ![1224, -372, 31]]]
  hmulB := by decide  
  f := ![![![13919, 310, 518]], ![![3547, 79, 132]], ![![3950, 88, 147]]]
  g := ![![![-3, 14, -2], ![-9, -7, 38], ![86, -372, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![75126625916911349609683432866327445942920606366953645, 1673684824276859930516417992030512204396933319376188, 2795824192976106065648013384204374421690905178292971]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![75126625916911349609683432866327445942920606366953645, 1673684824276859930516417992030512204396933319376188, 2795824192976106065648013384204374421690905178292971]] 
 ![![113, 0, 0], ![37, 1, 0], ![8, 0, 1]] where
  M :=![![![75126625916911349609683432866327445942920606366953645, 1673684824276859930516417992030512204396933319376188, 2795824192976106065648013384204374421690905178292971], ![285174067683562818696097365188846191012472328185883042, 6353160461207944103614693653391947617941948768546153, 10612702858782791922845280744500285456572610314714506], ![455889919759802531608772000375958435860959526762254218, 10156399690925270849270209106946446684909893544244966, 16965863319990736026459974397892233074514559083260659]]]
  hmulB := by decide  
  f := ![![![-219248353867115985446981969, -117685871128140025941853906, 109746553880220747265592565]], ![![27273977015037387252673529, -62742097412437653572813665, 34752725557028221818872109]], ![![-22688470709953046978358518, 34145238122957644830533882, -17620104871207845124327307]]]
  g := ![![![-81117753319834657916886193915367265427373167046983, 1673684824276859930516417992030512204396933319376188, 2795824192976106065648013384204374421690905178292971], ![-307915860631800429384146424271311101804961582018059, 6353160461207944103614693653391947617941948768546153, 10612702858782791922845280744500285456572610314714506], ![-492245799684587416158456033311486336963035460538892, 10156399690925270849270209106946446684909893544244966, 16965863319990736026459974397892233074514559083260659]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8969645087348504756188799, 2471216758487803772123316, -67708810226219535079711]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-8969645087348504756188799, 2471216758487803772123316, -67708810226219535079711]] 
 ![![113, 0, 0], ![50, 1, 0], ![12, 0, 1]] where
  M :=![![![-8969645087348504756188799, 2471216758487803772123316, -67708810226219535079711], ![-6906298643074392578130522, -9815850400407039686399051, 7278232655010972246210526], ![245157810722681592178447710, -60527960787779242162394382, -2537617745396067440188525]]]
  hmulB := by decide  
  f := ![![![465445456909064530798364372504518792948680032754707, 10369279709418600892155260343372901093229576732502, 17321470957266175345432874840178953660313929469955]], ![![221584627284021030311082936804638875405186039324520, 4936503183152104125872417107659257156366327304145, 8246232999168999297690046661233843306336398784382]], ![![74423026999209040228445683705986855754385823236346, 1658009917856353500105563035422534095282263802382, 2769639882789734328569434909641372199398229128497]]]
  g := ![![![-1165645816717027070277859, 2471216758487803772123316, -67708810226219535079711], ![3509269287762353316701732, -9815850400407039686399051, 7278232655010972246210526], ![29221303212888464686552470, -60527960787779242162394382, -2537617745396067440188525]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-41, 14, -2]] ![![75126625916911349609683432866327445942920606366953645, 1673684824276859930516417992030512204396933319376188, 2795824192976106065648013384204374421690905178292971]]
  ![![465445456909064530798364372504518792948680032754707, 10369279709418600892155260343372901093229576732502, 17321470957266175345432874840178953660313929469955]] where
 M := ![![![465445456909064530798364372504518792948680032754707, 10369279709418600892155260343372901093229576732502, 17321470957266175345432874840178953660313929469955]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![465445456909064530798364372504518792948680032754707, 10369279709418600892155260343372901093229576732502, 17321470957266175345432874840178953660313929469955]] ![![-8969645087348504756188799, 2471216758487803772123316, -67708810226219535079711]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9896126477810716488413889798524652727, -220467730353744037299932525275510590, -368282609337663139679165409953131038]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-9896126477810716488413889798524652727, -220467730353744037299932525275510590, -368282609337663139679165409953131038]] 
 ![![127, 0, 0], ![0, 127, 0], ![46, 24, 1]] where
  M :=![![![-9896126477810716488413889798524652727, -220467730353744037299932525275510590, -368282609337663139679165409953131038], ![-37564826152441640247274871815219365876, -836876123353057098813987434373997225, -1397968409736558391258128395732793846], ![-60052534648523532051867989393321446056, -1337861439588079619026596772544104524, -2234844533089615490072115830106791071]]]
  hmulB := by decide  
  f := ![![![1090867932366607727, -153780130045375386, -83570880193594170]], ![![-8524229779746605340, 3250349187058243193, -628482150523314498]], ![![-1406388920231728090, 575755447125314040, -128393425708109851]]]
  g := ![![![55471445289147936510454480782042323, 67860747194883238700787695382674286, -368282609337663139679165409953131038], ![210564729885354690949598695972355520, 257593430789955466861268457190653977, -1397968409736558391258128395732793846], ![336616644674006145601963297571582230, 411798483106792851517355772834794340, -2234844533089615490072115830106791071]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [85, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 126], [0, 1]]
 g := ![![[98, 104], [64, 88], [12, 82], [50, 88], [60, 18], [52, 1]], ![[45, 23], [68, 39], [85, 45], [54, 39], [107, 109], [104, 126]]]
 h' := ![![[52, 126], [21, 55], [123, 56], [68, 92], [107, 56], [25, 79], [0, 1]], ![[0, 1], [87, 72], [114, 71], [26, 35], [98, 71], [69, 48], [52, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [43, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [85, 75, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11, 72, 3]
  a := ![-1, 1, 0]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, 0, 3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1090867932366607727, 153780130045375386, 83570880193594170]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-1090867932366607727, 153780130045375386, 83570880193594170]] 
 ![![127, 0, 0], ![53, 1, 0], ![55, 0, 1]] where
  M :=![![![-1090867932366607727, 153780130045375386, 83570880193594170], ![8524229779746605340, -3250349187058243193, 628482150523314498], ![24209803044374894712, -2186447277604314204, -2621867036534928695]]]
  hmulB := by decide  
  f := ![![![9896126477810716488413889798524652727, 220467730353744037299932525275510590, 368282609337663139679165409953131038]], ![![4425665586428422158529220717614377641, 98595793953555047840239458850205185, 164700367753013423576802323805108180]], ![![4758578668725298731611275026080136583, 106012492984598438350573902855883362, 177089669658748725767135538405740143]]]
  g := ![![![-108957584530859705, 153780130045375386, 83570880193594170], ![1151387546575206277, -3250349187058243193, 628482150523314498], ![2238536974541926187, -2186447277604314204, -2621867036534928695]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-9896126477810716488413889798524652727, -220467730353744037299932525275510590, -368282609337663139679165409953131038]] ![![-1090867932366607727, 153780130045375386, 83570880193594170]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44139249845, 5980634486, 3532675275]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-44139249845, 5980634486, 3532675275]] 
 ![![131, 0, 0], ![0, 131, 0], ![9, 105, 1]] where
  M :=![![![-44139249845, 5980634486, 3532675275], ![360332878050, -134904090931, 25007254008], ![970357595622, -79947072714, -109896836923]]]
  hmulB := by decide  
  f := ![![![128433508670570337275, 2861265387165167788, 4779630475180930923]], ![![487522308468454954146, 10861111879062827335, 18143057111857365210]], ![![405535231642612254117, 9034588664483787099, 15091922442844060442]]]
  g := ![![![-579643720, -2785879919, 3532675275], ![1032577038, -21073784441, 25007254008], ![14957474259, 87474967971, -109896836923]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [87, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 130], [0, 1]]
 g := ![![[68, 121], [64, 35], [11], [45], [21], [48], [1]], ![[16, 10], [115, 96], [11], [45], [21], [48], [1]]]
 h' := ![![[110, 130], [65, 11], [83, 64], [75, 50], [45, 62], [118, 26], [44, 110], [0, 1]], ![[0, 1], [96, 120], [49, 67], [73, 81], [53, 69], [96, 105], [92, 21], [110, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [4, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [87, 21, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2229, 1508, -975]
  a := ![0, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![84, 793, -975]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![128433508670570337275, 2861265387165167788, 4779630475180930923]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![128433508670570337275, 2861265387165167788, 4779630475180930923]] 
 ![![131, 0, 0], ![76, 1, 0], ![65, 0, 1]] where
  M :=![![![128433508670570337275, 2861265387165167788, 4779630475180930923], ![487522308468454954146, 10861111879062827335, 18143057111857365210], ![779371377959302068522, 17362979261292729702, 29004168990920192545]]]
  hmulB := by decide  
  f := ![![![-44139249845, 5980634486, 3532675275]], ![![-22856871070, 2439878855, 2240386068]], ![![-14493844613, 2357207396, 913946992]]]
  g := ![![![-3051134669013304768, 2861265387165167788, 4779630475180930923], ![-11581838981763730244, 10861111879062827335, 18143057111857365210], ![-18515160536708075605, 17362979261292729702, 29004168990920192545]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-44139249845, 5980634486, 3532675275]] ![![128433508670570337275, 2861265387165167788, 4779630475180930923]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [59, 29, 86, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 62, 64], [82, 74, 73], [0, 1]]
 g := ![![[40, 85, 63], [105, 28], [113, 128], [82, 92, 19], [106, 2], [51, 1], []], ![[136, 106, 114, 9], [79, 7], [100, 77], [39, 59, 51, 121], [63, 2], [0, 133], [98, 123]], ![[114, 2, 106, 16], [52, 63], [41, 135], [122, 18, 134, 135], [64, 8], [126, 8], [89, 123]]]
 h' := ![![[106, 62, 64], [88, 13, 101], [114, 118, 24], [94, 126, 111], [73, 60, 108], [5, 106, 106], [0, 0, 1], [0, 1]], ![[82, 74, 73], [73, 101, 86], [79, 114, 12], [15, 19, 112], [63, 81, 50], [128, 131, 106], [111, 31, 74], [106, 62, 64]], ![[0, 1], [49, 23, 87], [69, 42, 101], [76, 129, 51], [88, 133, 116], [24, 37, 62], [103, 106, 62], [82, 74, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 131], []]
 b := ![[], [61, 50, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [59, 29, 86, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![530053, -18906, -67404]
  a := ![2, -2, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3869, -138, -492]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB177I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB177I2 : PrimesBelowBoundCertificateInterval O 79 137 177 where
  m := 11
  g := ![2, 1, 2, 2, 3, 2, 1, 3, 2, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB177I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0]
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
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![113, 113, 113]
    · exact ![16129, 127]
    · exact ![17161, 131]
    · exact ![2571353]
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
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I97N1, I101N1, I103N0, I103N1, I103N2, I107N1, I113N0, I113N1, I113N2, I127N1, I131N1]
  Il := ![[I83N1], [], [I97N1], [I101N1], [I103N0, I103N1, I103N2], [I107N1], [], [I113N0, I113N1, I113N2], [I127N1], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
