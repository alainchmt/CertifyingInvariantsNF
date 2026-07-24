
import IdealArithmetic.Examples.NF3_1_171444_1.RI3_1_171444_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-469592315, 31543939, 23225379]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-469592315, 31543939, 23225379]] 
 ![![83, 0, 0], ![0, 83, 0], ![43, 29, 1]] where
  M :=![![![-469592315, 31543939, 23225379], ![1921118198, -547587012, 212489013], ![3127374974, 238842049, -484499134]]]
  hmulB := by decide  
  f := ![![![-2584989419864337, -250966364308559, -233983811486985]], ![![-19220637647575918, -1866055432581808, -1739781997338339]], ![![-8370047290086921, -812614675070532, -757626144312664]]]
  g := ![![![-17690164, -7734844, 23225379], ![-86938667, -80840583, 212489013], ![288684792, 172160445, -484499134]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [44, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 82], [0, 1]]
 g := ![![[55, 17], [52, 4], [25], [37], [26, 3], [1]], ![[0, 66], [0, 79], [25], [37], [70, 80], [1]]]
 h' := ![![[70, 82], [36, 73], [57, 81], [24, 5], [18, 55], [39, 70], [0, 1]], ![[0, 1], [0, 10], [0, 2], [42, 78], [50, 28], [42, 13], [70, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [73, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [44, 13, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![682, 1095, -237]
  a := ![-3, 1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![131, 96, -237]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2584989419864337, 250966364308559, 233983811486985]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![2584989419864337, 250966364308559, 233983811486985]] 
 ![![83, 0, 0], ![74, 1, 0], ![13, 0, 1]] where
  M :=![![![2584989419864337, 250966364308559, 233983811486985], ![19220637647575918, 1866055432581808, 1739781997338339], ![26160888243346330, 2539856820713687, 2367988161198926]]]
  hmulB := by decide  
  f := ![![![469592315, -31543939, -23225379]], ![![395526664, -21526078, -23267073]], ![![35871387, -7818232, 2199629]]]
  g := ![![![-229256760099998, 250966364308559, 233983811486985], ![-1704634100347907, 1866055432581808, 1739781997338339], ![-2320148946807862, 2539856820713687, 2367988161198926]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-469592315, 31543939, 23225379]] ![![2584989419864337, 250966364308559, 233983811486985]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4802346085358994741, -1870621538941147498, 1848888009726521004]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-4802346085358994741, -1870621538941147498, 1848888009726521004]] 
 ![![89, 0, 0], ![0, 89, 0], ![11, 72, 1]] where
  M :=![![![-4802346085358994741, -1870621538941147498, 1848888009726521004], ![144169797700239385324, -6629500565870889251, -9374841223920363984], ![-101578634862402253736, 27776787204327068048, -10370743643753184247]]]
  hmulB := by decide  
  f := ![![![-3698380006808457740398517371959901261, -359061037932175992296832207696766474, -334763865441940395649278354593261124]], ![![-27499231311219583636535932782854422868, -2669791237992400956803128455076612539, -2489130093034996349430271600773859968]], ![![-23124219977738961647703355789800488399, -2245038749748176156898172553308981974, -2093120028452110499466498989064201523]]]
  g := ![![![-282473193172480065, -1516747845384838874, 1848888009726521004], ![2778573608577116732, 7509652444453879973, -9374841223920363984], ![140444328302053629, 8701913815219734088, -10370743643753184247]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [31, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 88], [0, 1]]
 g := ![![[37, 8], [17], [1], [62, 10], [24, 11], [1]], ![[28, 81], [17], [1], [73, 79], [45, 78], [1]]]
 h' := ![![[10, 88], [12, 39], [19, 27], [36, 88], [57, 59], [58, 10], [0, 1]], ![[0, 1], [46, 50], [22, 62], [26, 1], [24, 30], [69, 79], [10, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [7, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [31, 79, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1905, 1156, 644]
  a := ![3, -3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-101, -508, 644]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3698380006808457740398517371959901261, 359061037932175992296832207696766474, 334763865441940395649278354593261124]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![3698380006808457740398517371959901261, 359061037932175992296832207696766474, 334763865441940395649278354593261124]] 
 ![![89, 0, 0], ![12, 1, 0], ![8, 0, 1]] where
  M :=![![![3698380006808457740398517371959901261, 359061037932175992296832207696766474, 334763865441940395649278354593261124], ![27499231311219583636535932782854422868, 2669791237992400956803128455076612539, 2489130093034996349430271600773859968], ![37428743536064529670627813835166107144, 3633808174880873158846954194318861664, 3387913313856752941396792870470145487]]]
  hmulB := by decide  
  f := ![![![4802346085358994741, 1870621538941147498, -1848888009726521004]], ![![-972378030066645488, 326707404867018643, -143952976323571776]], ![![1573004534216564176, -143952976323571776, -49666971169202065]]]
  g := ![![![-36949026650709857666940404012891971, 359061037932175992296832207696766474, 334763865441940395649278354593261124], ![-274733756055833692590379567238829296, 2669791237992400956803128455076612539, 2489130093034996349430271600773859968], ![-373935517678201929963033477083386480, 3633808174880873158846954194318861664, 3387913313856752941396792870470145487]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-4802346085358994741, -1870621538941147498, 1848888009726521004]] ![![3698380006808457740398517371959901261, 359061037932175992296832207696766474, 334763865441940395649278354593261124]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-197775, 61252, -25460]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-197775, 61252, -25460]] 
 ![![97, 0, 0], ![0, 97, 0], ![42, 18, 1]] where
  M :=![![![-197775, 61252, -25460], ![-1914296, -208107, 342052], ![4238200, -453484, -85603]]]
  hmulB := by decide  
  f := ![![![1782780337, 173083068, 161370772]], ![![13255827896, 1286955725, 1199869180]], ![![3417772802, 331817998, 309364325]]]
  g := ![![![8985, 5356, -25460], ![-167840, -65619, 342052], ![80758, 11210, -85603]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [86, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 96], [0, 1]]
 g := ![![[20, 44], [73], [85], [54], [64], [26, 1]], ![[0, 53], [73], [85], [54], [64], [52, 96]]]
 h' := ![![[26, 96], [81, 23], [65, 49], [87, 45], [50, 32], [92, 8], [0, 1]], ![[0, 1], [0, 74], [78, 48], [93, 52], [9, 65], [9, 89], [26, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [3, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [86, 71, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![424924, 223557, -26849]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16006, 7287, -26849]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1782780337, 173083068, 161370772]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![1782780337, 173083068, 161370772]] 
 ![![97, 0, 0], ![85, 1, 0], ![39, 0, 1]] where
  M :=![![![1782780337, 173083068, 161370772], ![13255827896, 1286955725, 1199869180], ![18042285512, 1751653900, 1633121861]]]
  hmulB := by decide  
  f := ![![![-197775, 61252, -25460]], ![![-193043, 51529, -18784]], ![![-35825, 19952, -11119]]]
  g := ![![![-198172583, 173083068, 161370772], ![-1473508317, 1286955725, 1199869180], ![-2005567511, 1751653900, 1633121861]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-197775, 61252, -25460]] ![![1782780337, 173083068, 161370772]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [46, 73, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 72, 85], [100, 28, 16], [0, 1]]
 g := ![![[54, 55, 45], [72, 4], [94, 66, 58], [80, 5], [85, 85], [1]], ![[81, 63, 95, 87], [93, 16], [92, 82, 62, 68], [9, 4], [26, 13], [3, 84, 31, 45]], ![[86, 33, 19, 45], [2, 36], [45, 0, 55, 16], [65, 88], [52, 25], [90, 8, 9, 56]]]
 h' := ![![[41, 72, 85], [79, 42, 67], [19, 22, 99], [27, 54, 82], [24, 35, 56], [55, 28, 40], [0, 1]], ![[100, 28, 16], [9, 97, 93], [67, 81, 97], [87, 63, 18], [20, 63, 99], [2, 59, 66], [41, 72, 85]], ![[0, 1], [65, 63, 42], [64, 99, 6], [54, 85, 1], [32, 3, 47], [0, 14, 96], [100, 28, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 70], []]
 b := ![[], [48, 0, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [46, 73, 61, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2477126, 225533, 12019]
  a := ![-4, 3, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24526, 2233, 119]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101200720536967257677751316181, 9825176344397613152712030794, 9160320013113057429184472764]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![101200720536967257677751316181, 9825176344397613152712030794, 9160320013113057429184472764]] 
 ![![103, 0, 0], ![0, 103, 0], ![99, 76, 1]] where
  M :=![![![101200720536967257677751316181, 9825176344397613152712030794, 9160320013113057429184472764], ![752475953737839820640181882708, 73054904166343529666670339859, 68111378079498736345456657528], ![1024182427892748545375758755384, 99433807481674520273974084344, 92705256855138755972094401447]]]
  hmulB := by decide  
  f := ![![![-195874465273453, -17682232576234, 32345889697252]], ![![2552306710627692, -242884012091723, -73747505760152]], ![![1689418956035559, -191785096240790, -26027338203765]]]
  g := ![![![-7822048162730343959335062985, -6663681016040725742381630090, 9160320013113057429184472764], ![-58160684234296457063689584588, -49547668251219033326097433323, 68111378079498736345456657528], ![-79161533988019303843316378523, -67438502072901659549565052676, 92705256855138755972094401447]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [23, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [100, 102], [0, 1]]
 g := ![![[27, 9], [81, 7], [97, 81], [38], [93], [100, 1]], ![[0, 94], [60, 96], [60, 22], [38], [93], [97, 102]]]
 h' := ![![[100, 102], [94, 100], [35, 25], [99, 9], [47, 55], [69, 89], [0, 1]], ![[0, 1], [0, 3], [63, 78], [72, 94], [88, 48], [8, 14], [100, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [5, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [23, 3, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![691, 1085, -147]
  a := ![-3, 1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![148, 119, -147]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![195874465273453, 17682232576234, -32345889697252]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![195874465273453, 17682232576234, -32345889697252]] 
 ![![103, 0, 0], ![58, 1, 0], ![33, 0, 1]] where
  M :=![![![195874465273453, 17682232576234, -32345889697252], ![-2552306710627692, 242884012091723, 73747505760152], ![573585473970168, -455861031216744, 278248477244191]]]
  hmulB := by decide  
  f := ![![![-101200720536967257677751316181, -9825176344397613152712030794, -9160320013113057429184472764]], ![![-64292405290115929766502507002, -6241894486809758179844350737, -5819513969320932691632583280]], ![![-42367050539928816007199535819, -4113248804337822857412340782, -3834910847455045156652252453]]]
  g := ![![![2307954717099, 17682232576234, -32345889697252], ![-185177156330414, 242884012091723, 73747505760152], ![173119665393039, -455861031216744, 278248477244191]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![101200720536967257677751316181, 9825176344397613152712030794, 9160320013113057429184472764]] ![![195874465273453, 17682232576234, -32345889697252]]
  ![![103, 0, 0]] where
 M := ![![![-103, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-78396071237, 9925588971, 453993211]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-78396071237, 9925588971, 453993211]] 
 ![![107, 0, 0], ![0, 107, 0], ![78, 62, 1]] where
  M :=![![![-78396071237, 9925588971, 453993211], ![56170634822, -89229646630, 60007527037], ![805850941166, -13949266199, -69378468688]]]
  hmulB := by decide  
  f := ![![![65679226292930490129, 6376535434408447337, 5945043946966173251]], ![![488356586626110754754, 47412602964589696290, 44204256553416857273]], ![![337063383168609731928, 32724146244207134765, 30509747738398254724]]]
  g := ![![![-1063621885, -170298973, 453993211], ![-43218845552, -35604638532, 60007527037], ![58106275690, 40070241051, -69378468688]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [64, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 106], [0, 1]]
 g := ![![[19, 102], [11, 14], [47], [2, 33], [76], [68, 1]], ![[0, 5], [0, 93], [47], [106, 74], [76], [29, 106]]]
 h' := ![![[68, 106], [45, 67], [1, 11], [86, 58], [106, 51], [35, 66], [0, 1]], ![[0, 1], [0, 40], [0, 96], [71, 49], [43, 56], [29, 41], [68, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [64, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [64, 39, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![100858, 55101, -3179]
  a := ![22, -1, 65]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3260, 2357, -3179]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65679226292930490129, -6376535434408447337, -5945043946966173251]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-65679226292930490129, -6376535434408447337, -5945043946966173251]] 
 ![![107, 0, 0], ![55, 1, 0], ![76, 0, 1]] where
  M :=![![![-65679226292930490129, -6376535434408447337, -5945043946966173251], ![-488356586626110754754, -47412602964589696290, -44204256553416857273], ![-664693977373796291486, -64532500441743357589, -60165673833406590964]]]
  hmulB := by decide  
  f := ![![![78396071237, -9925588971, -453993211]], ![![39772086759, -4268016325, -794179006]], ![![48151873578, -6919584071, 325934436]]]
  g := ![![![6886481893167881126, -6376535434408447337, -5945043946966173251], ![51204299761551436392, -47412602964589696290, -44204256553416857273], ![69693315497766255039, -64532500441743357589, -60165673833406590964]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-78396071237, 9925588971, 453993211]] ![![-65679226292930490129, -6376535434408447337, -5945043946966173251]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4100537, 1590136, -763108]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-4100537, 1590136, -763108]] 
 ![![109, 0, 0], ![0, 109, 0], ![43, 44, 1]] where
  M :=![![![-4100537, 1590136, -763108], ![-57868368, -4164457, 8777708], ![107370072, -13100676, -984185]]]
  hmulB := by decide  
  f := ![![![-1092591785717, -106075400552, -98897422348]], ![![-8123944588944, -788721540469, -735349825660]], ![![-3811856639675, -370078033888, -345035356253]]]
  g := ![![![263423, 322632, -763108], ![-3993668, -3581501, 8777708], ![1373303, 277096, -984185]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [32, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 108], [0, 1]]
 g := ![![[86, 22], [60], [31, 74], [28, 26], [105], [82, 1]], ![[37, 87], [60], [104, 35], [89, 83], [105], [55, 108]]]
 h' := ![![[82, 108], [54, 83], [98, 96], [85, 69], [83, 74], [101, 43], [0, 1]], ![[0, 1], [102, 26], [13, 13], [75, 40], [47, 35], [30, 66], [82, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [91, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [32, 27, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![220, 35, 33]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, -13, 33]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1092591785717, 106075400552, 98897422348]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![1092591785717, 106075400552, 98897422348]] 
 ![![109, 0, 0], ![62, 1, 0], ![24, 0, 1]] where
  M :=![![![1092591785717, 106075400552, 98897422348], ![8123944588944, 788721540469, 735349825660], ![11057365025208, 1073515689420, 1000872341573]]]
  hmulB := by decide  
  f := ![![![4100537, -1590136, 763108]], ![![2863318, -866275, 353532]], ![![-82176, -229932, 177053]]]
  g := ![![![-72088267751, 106075400552, 98897422348], ![-536010887486, 788721540469, 735349825660], ![-729555448776, 1073515689420, 1000872341573]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-4100537, 1590136, -763108]] ![![1092591785717, 106075400552, 98897422348]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-598852617203718328041663086970321, -58140224072626911563494276608466, -54205954119392938137593860875006]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-598852617203718328041663086970321, -58140224072626911563494276608466, -54205954119392938137593860875006]] 
 ![![113, 0, 0], ![0, 113, 0], ![59, 19, 1]] where
  M :=![![![-598852617203718328041663086970321, -58140224072626911563494276608466, -54205954119392938137593860875006], ![-4452756777696688874134497423217412, -432300484892305540202981088611843, -403047298555154407518559520525802], ![-6060572732914369316656982511427436, -588396955406854372661731638158146, -548580933037559363329969641828775]]]
  hmulB := by decide  
  f := ![![![-8548514299944241, -2288138804241502, 2525805135129702]], ![![197488133201893156, -11311985765962143, -11203027690319310]], ![![27703823153215149, -2765629864056285, -705515809892563]]]
  g := ![![![23002643149030663912180307120841, 8599760214122468257086629026696, -54205954119392938137593860875006], ![171035697673074523623544374228362, 63943346793412638961501325675915, -403047298555154407518559520525802], ![232793825807979054157621472181153, 87032219223953748058475146518483, -548580933037559363329969641828775]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [10, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 112], [0, 1]]
 g := ![![[96, 14], [50], [69], [95], [85, 88], [57, 1]], ![[103, 99], [50], [69], [95], [16, 25], [1, 112]]]
 h' := ![![[57, 112], [54, 50], [92, 29], [45, 42], [54, 35], [108, 75], [0, 1]], ![[0, 1], [79, 63], [50, 84], [66, 71], [15, 78], [89, 38], [57, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [54, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [10, 56, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1373, 2909, 504]
  a := ![5, -2, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-251, -59, 504]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8548514299944241, 2288138804241502, -2525805135129702]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![8548514299944241, 2288138804241502, -2525805135129702]] 
 ![![113, 0, 0], ![111, 1, 0], ![37, 0, 1]] where
  M :=![![![8548514299944241, 2288138804241502, -2525805135129702], ![-197488133201893156, 11311985765962143, 11203027690319310], ![117380170825947908, -37411744365169130, 15888263374445147]]]
  hmulB := by decide  
  f := ![![![598852617203718328041663086970321, 58140224072626911563494276608466, 54205954119392938137593860875006]], ![![627658383073534719351850443158611, 60936861565963652422573856567713, 56813346954051066732667947589836]], ![![249717872296034933222995723268401, 24244117222071239827531149315676, 22603550756239805968326924727469]]]
  g := ![![![-1344956663460739, 2288138804241502, -2525805135129702], ![-16527704228013323, 11311985765962143, 11203027690319310], ![32586000446949123, -37411744365169130, 15888263374445147]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-598852617203718328041663086970321, -58140224072626911563494276608466, -54205954119392938137593860875006]] ![![8548514299944241, 2288138804241502, -2525805135129702]]
  ![![113, 0, 0]] where
 M := ![![![-113, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)


lemma PB118I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 117 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 117 (by omega)

def PB118I2 : PrimesBelowBoundCertificateInterval O 79 117 118 where
  m := 8
  g := ![2, 2, 2, 1, 2, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB118I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
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
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
  β := ![I83N1, I89N1, I97N1, I103N1, I107N1, I109N1, I113N1]
  Il := ![[I83N1], [I89N1], [I97N1], [], [I103N1], [I107N1], [I109N1], [I113N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
