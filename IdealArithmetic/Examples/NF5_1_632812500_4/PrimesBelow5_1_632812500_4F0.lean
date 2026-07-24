
import IdealArithmetic.Examples.NF5_1_632812500_4.RI5_1_632812500_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-141762, -109669, -33640, 11696, -74450]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-141762, -109669, -33640, 11696, -74450]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-141762, -109669, -33640, 11696, -74450], ![-246742, -192820, -58611, 20062, -129782], ![-429470, -336400, -103162, 36105, -228850], ![-151752, -117222, -35952, 12485, -79542], ![-170979, -133061, -40861, 14293, -90551]]]
  hmulB := by decide  
  f := ![![![24094, -6142, 15199, 14117, -61820]], ![![-106847, -4746, 13722, 109552, -36262]], ![![-327890, 75995, -187588, -151260, 767630]], ![![521082, 27444, -77823, -557410, 218562]], ![![376517, -20259, 45451, -186980, -231153]]]
  g := ![![![-33656, -109669, -33640, 11696, -74450], ![-58480, -192820, -58611, 20062, -129782], ![-100310, -336400, -103162, 36105, -228850], ![-36105, -117222, -35952, 12485, -79542], ![-40214, -133061, -40861, 14293, -90551]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![183948, 124486, 43482, -18332, 95741]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![183948, 124486, 43482, -18332, 95741]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![183948, 124486, 43482, -18332, 95741], ![323887, 243025, 65409, -14817, 140567], ![451335, 434820, 132092, -50205, 303165], ![201981, 130818, 46413, -19684, 101571], ![196602, 161150, 53523, -22511, 121079]]]
  hmulB := by decide  
  f := ![![![-129899, -212962, 542211, 1248433, -2054955]], ![![-4395815, 49525, -56331, 3189527, 883822]], ![![538328, 2604574, -6614809, -14442796, 25228905]], ![![21715685, -761354, 1588845, -12975320, -9380868]], ![![9652399, -1354914, 3284508, -295918, -14035178]]]
  g := ![![![17156, 124486, 43482, -18332, 95741], ![15135, 243025, 65409, -14817, 140567], ![-32686, 434820, 132092, -50205, 303165], ![22217, 130818, 46413, -19684, 101571], ![2220, 161150, 53523, -22511, 121079]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-141683662, -110415494, -33759041, 11697876, -74781205]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-141683662, -110415494, -33759041, 11697876, -74781205]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-141683662, -110415494, -33759041, 11697876, -74781205], ![-247739367, -193069115, -59030041, 20454782, -130760607], ![-433191385, -337590410, -103218072, 35767270, -228643565], ![-151493047, -118060082, -36096277, 12507705, -79958507], ![-171705179, -133811246, -40912495, 14176858, -90627216]]]
  hmulB := by decide  
  f := ![![![2114099, -152722, 354047, -840108, -1676115]], ![![-617015, -697477, 1778828, 4239398, -6712662]], ![![-25885668, 1693874, -3888392, 11234426, 18813745]], ![![8186339, 3127248, -8061082, -23269239, 29600192]], ![![14804272, 687386, -1976849, -15339470, 5313532]]]
  g := ![![![32787101, -110415494, -33759041, 11697876, -74781205], ![57332807, -193069115, -59030041, 20454782, -130760607], ![100246696, -337590410, -103218072, 35767270, -228643565], ![35057057, -118060082, -36096277, 12507705, -79958507], ![39734460, -133811246, -40912495, 14176858, -90627216]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-141762, -109669, -33640, 11696, -74450]] ![![-141762, -109669, -33640, 11696, -74450]]
  ![![72558279000, 56545132296, 17288659977, -5990889320, 38296955776]] where
 M := ![![![72558279000, 56545132296, 17288659977, -5990889320, 38296955776]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![72558279000, 56545132296, 17288659977, -5990889320, 38296955776]] ![![-141762, -109669, -33640, 11696, -74450]]
  ![![-37301872346435886, -29069898729869816, -8888027452238626, 3079839279522105, -19688314391107058]] where
 M := ![![![-37301872346435886, -29069898729869816, -8888027452238626, 3079839279522105, -19688314391107058]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-37301872346435886, -29069898729869816, -8888027452238626, 3079839279522105, -19688314391107058]] ![![183948, 124486, 43482, -18332, 95741]]
  ![![-23537137942862929245341, -18342838565785808760126, -5608263412285648181357, 1943350120455081811972, -12423144920340163387115]] where
 M := ![![![-23537137942862929245341, -18342838565785808760126, -5608263412285648181357, 1943350120455081811972, -12423144920340163387115]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-23537137942862929245341, -18342838565785808760126, -5608263412285648181357, 1943350120455081811972, -12423144920340163387115]] ![![-141683662, -110415494, -33759041, 11697876, -74781205]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![12147236798182167775592157418330, 9466520692986651661083527401900, 2894358004296510826383860980532, -1002939868303906282799362144048, 6411437246512840461288791666128]]]
 hmul := by decide  
 g := ![![![![6073618399091083887796078709165, 4733260346493325830541763700950, 1447179002148255413191930490266, -501469934151953141399681072024, 3205718623256420230644395833064]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N0, I2N1, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4159315, -6511572, 1834819, -3159879, 4121946]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![4159315, -6511572, 1834819, -3159879, 4121946]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 2, 0, 1, 0], ![2, 1, 0, 0, 1]] where
  M :=![![![4159315, -6511572, 1834819, -3159879, 4121946], ![18685596, 1961503, -4313760, 6287894, -12913194], ![-51315370, 18348190, 2298909, -1692900, 11563570], ![7615302, -8627520, 2034084, -3623493, 4229502], ![-11112738, -191814, 2173399, -3099929, 6698311]]]
  hmulB := by decide  
  f := ![![![4828633, -562030, 1349443, -771177, -5897554]], ![![-16150308, -2611275, 6877878, 26753408, -23862078]], ![![-40088139, 4310800, -10302190, 8314741, 45514492]], ![![14292614, 2844402, -7439908, -26547685, 26295034]], ![![25478764, -918337, 1927709, -15088963, -11249575]]]
  g := ![![![-1973132, -1437920, 1834819, -3159879, 4121946], ![16275248, 766303, -4313760, 6287894, -12913194], ![-25580473, 3390140, 2298909, -1692900, 11563570], ![-959262, -1870012, 2034084, -3623493, 4229502], ![-8894253, -230089, 2173399, -3099929, 6698311]]]
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
  c := ![-370, 197, -497, -816, 2018]
  a := ![3, -5, 3, 4, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1303, -63, -497, -816, 2018]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2463, -3677, 1001, -1738, 2226]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![2463, -3677, 1001, -1738, 2226]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![2463, -3677, 1001, -1738, 2226], ![10154, 1213, -2427, 3541, -7226], ![-28760, 10010, 1357, -1080, 6650], ![4422, -4854, 1104, -1985, 2262], ![-6110, -201, 1217, -1748, 3737]]]
  hmulB := by decide  
  f := ![![![7861, -451, 1020, -3753, -5098]], ![![-2596, -1581, 4051, 10551, -15106]], ![![-66420, 3400, -7577, 33920, 39090]], ![![9886, 8102, -20706, -51383, 77726]], ![![35640, 2051, -5764, -39061, 16637]]]
  g := ![![![-663, -3677, 1001, -1738, 2226], ![8202, 1213, -2427, 3541, -7226], ![-14020, 10010, 1357, -1080, 6650], ![-34, -4854, 1104, -1985, 2262], ![-4528, -201, 1217, -1748, 3737]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![4159315, -6511572, 1834819, -3159879, 4121946]] ![![2463, -3677, 1001, -1738, 2226]]
  ![![-147801578681, 9683741619, 23984810808, -33200772235, 76768866716]] where
 M := ![![![-147801578681, 9683741619, 23984810808, -33200772235, 76768866716]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-147801578681, 9683741619, 23984810808, -33200772235, 76768866716]] ![![2463, -3677, 1001, -1738, 2226]]
  ![![-1571381325187987, 941026745800738, -82130374656606, 196977231014724, -27696931087478]] where
 M := ![![![-1571381325187987, 941026745800738, -82130374656606, 196977231014724, -27696931087478]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-1571381325187987, 941026745800738, -82130374656606, 196977231014724, -27696931087478]] ![![2463, -3677, 1001, -1738, 2226]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![9087204512538270339, 5146749128863010115, -3784519839073785885, 5809351686662953548, -10501862021409621348]]]
 hmul := by decide  
 g := ![![![![3029068170846090113, 1715583042954336705, -1261506613024595295, 1936450562220984516, -3500620673803207116]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![803469, -432092, 22256, -68518, -35246]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![803469, -432092, 22256, -68518, -35246]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![803469, -432092, 22256, -68518, -35246], ![31298, 631187, -259810, 422572, -653882], ![-2806790, 222560, 439925, -605120, 1418930], ![1093406, -519620, 2774, -48361, -116834], ![-130350, -295056, 143280, -228506, 373405]]]
  hmulB := by decide  
  f := ![![![-65215, 10140, -24684, -3290, 104370]], ![![63938, 6515, -17530, -85332, 57358]], ![![342738, -49368, 119821, -3728, -510582]], ![![-304858, -35060, 93734, 428407, -312314]], ![![-285145, 5372, -9128, 195280, 78279]]]
  g := ![![![167743, -432092, 22256, -68518, -35246], ![137036, 631187, -259810, 422572, -653882], ![-845144, 222560, 439925, -605120, 1418930], ![242048, -519620, 2774, -48361, -116834], ![-100751, -295056, 143280, -228506, 373405]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![803469, -432092, 22256, -68518, -35246]] ![![803469, -432092, 22256, -68518, -35246]]
  ![![499247224097, -568947218056, 134694683572, -239742098812, 280642018232]] where
 M := ![![![499247224097, -568947218056, 134694683572, -239742098812, 280642018232]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![499247224097, -568947218056, 134694683572, -239742098812, 280642018232]] ![![803469, -432092, 22256, -68518, -35246]]
  ![![-293454069405952947, -503085492448618628, 257730325403220764, -408669249429601178, 678353365727709658]] where
 M := ![![![-293454069405952947, -503085492448618628, 257730325403220764, -408669249429601178, 678353365727709658]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-293454069405952947, -503085492448618628, 257730325403220764, -408669249429601178, 678353365727709658]] ![![803469, -432092, 22256, -68518, -35246]]
  ![![-1510186488037123941932415, -121180921032214148678960, 333618363170937137685416, -483684891912748616102040, 1006049922345375350822320]] where
 M := ![![![-1510186488037123941932415, -121180921032214148678960, 333618363170937137685416, -483684891912748616102040, 1006049922345375350822320]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-1510186488037123941932415, -121180921032214148678960, 333618363170937137685416, -483684891912748616102040, 1006049922345375350822320]] ![![803469, -432092, 22256, -68518, -35246]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-2813580003692191313927254972595, 604793058540865942205212096500, 287445454017079263417644353800, -356108808794754523830133501550, 1038022071932989509887287087650]]]
 hmul := by decide  
 g := ![![![![-562716000738438262785450994519, 120958611708173188441042419300, 57489090803415852683528870760, -71221761758950904766026700310, 207604414386597901977457417530]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![761, 596, 181, -63, 408]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![761, 596, 181, -63, 408]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![4, 6, 3, 1, 0], ![6, 4, 3, 0, 1]] where
  M :=![![![761, 596, 181, -63, 408], ![1350, 1043, 314, -130, 720], ![2420, 1810, 583, -200, 1120], ![752, 628, 218, 31, 352], ![864, 722, 221, -29, 497]]]
  hmulB := by decide  
  f := ![![![-1265, 362, 93, -101, 376]], ![![1330, -1091, 188, -360, 320]], ![![1680, 930, -691, 1060, -1920]], ![![912, -276, -61, 63, -256]], ![![314, 166, -126, 193, -351]]]
  g := ![![![-205, -94, -122, -63, 408], ![-350, -151, -208, -130, 720], ![-500, -210, -311, -200, 1120], ![-212, -138, -133, 31, 352], ![-286, -156, -169, -29, 497]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 0, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 2, 1], [6, 4, 6], [0, 1]]
 g := ![![[5, 1, 2], [1]], ![[6, 4, 3, 4], [1, 4, 3, 1]], ![[2, 0, 0, 6], [4, 2, 1, 6]]]
 h' := ![![[5, 2, 1], [1, 0, 4], [0, 1]], ![[6, 4, 6], [0, 0, 2], [5, 2, 1]], ![[0, 1], [3, 0, 1], [6, 4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [4, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 0, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![858996, 144664, -348355, -1330937, 1207618]
  a := ![-5, 25, -4, -8, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-151852, 471402, 3086, -1330937, 1207618]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1265, 362, 93, -101, 376]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-1265, 362, 93, -101, 376]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![3, 6, 1, 0, 0], ![2, 6, 0, 1, 0], ![6, 5, 0, 0, 1]] where
  M :=![![![-1265, 362, 93, -101, 376], ![1330, -1091, 188, -360, 320], ![1680, 930, -691, 1060, -1920], ![-1576, 376, 146, -175, 544], ![-572, 564, -119, 217, -233]]]
  hmulB := by decide  
  f := ![![![761, 596, 181, -63, 408]], ![![1350, 1043, 314, -130, 720]], ![![1829, 1408, 430, -167, 952]], ![![1482, 1154, 352, -125, 784]], ![![1740, 1359, 411, -151, 935]]]
  g := ![![![-514, -210, 93, -101, 376], ![-62, -237, 188, -360, 320], ![1879, 1188, -691, 1060, -1920], ![-704, -310, 146, -175, 544], ![107, 163, -119, 217, -233]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [4, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6], [0, 1]]
 g := ![![[5, 2], [1, 1]], ![[0, 5], [2, 6]]]
 h' := ![![[1, 6], [3, 4], [0, 1]], ![[0, 1], [0, 3], [1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [6, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [4, 6, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3528, 1778, -4544, -7091, 18071]
  a := ![8, -9, 9, 13, -33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12020, -2681, -4544, -7091, 18071]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![761, 596, 181, -63, 408]] ![![-1265, 362, 93, -101, 376]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![651493, 574508, 166792, -54678, 375112]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![651493, 574508, 166792, -54678, 375112]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![10, 9, 1, 0, 0], ![4, 10, 0, 1, 0], ![5, 1, 0, 0, 1]] where
  M :=![![![651493, 574508, 166792, -54678, 375112], ![1234692, 917249, 308752, -127342, 687912], ![2318420, 1667920, 484021, -137950, 1045000], ![682180, 617504, 179764, -60209, 406280], ![857030, 683864, 194382, -56324, 427551]]]
  hmulB := by decide  
  f := ![![![1120567, -829940, 2087424, 3586270, -8157624]], ![![-31645412, 135483, 155144, 24151182, 4217288]], ![![-28113958, 1254017, -2737603, 15353968, 14749152]], ![![-14065744, -150422, 603236, 11868523, -169848]], ![![5386483, -1092427, 2685966, 1645176, -11096401]]]
  g := ![![![-243025, -68632, 166792, -54678, 375112], ![-434820, -116001, 308752, -127342, 687912], ![-654090, -213979, 484021, -137950, 1045000], ![-264184, -73142, 179764, -60209, 406280], ![-272659, -84535, 194382, -56324, 427551]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [9, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 10], [0, 1]]
 g := ![![[2, 5], [3, 5], [1]], ![[0, 6], [1, 6], [1]]]
 h' := ![![[4, 10], [6, 4], [2, 4], [0, 1]], ![[0, 1], [0, 7], [7, 7], [4, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [2, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [9, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7689, 1038, -2404, 588, 10392]
  a := ![6, -6, 8, 4, -24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3451, 582, -2404, 588, 10392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9667623, -7534919, -2303596, 798133, -5102852]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-9667623, -7534919, -2303596, 798133, -5102852]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![7, 1, 1, 0, 0], ![3, 10, 0, 1, 0], ![9, 2, 0, 0, 1]] where
  M :=![![![-9667623, -7534919, -2303596, 798133, -5102852], ![-16904822, -13174209, -4028333, 1396177, -8923492], ![-29562830, -23035960, -7043071, 2440280, -15601060], ![-10336748, -8056666, -2463092, 853397, -5456188], ![-11717108, -9131185, -2791652, 967197, -6183849]]]
  hmulB := by decide  
  f := ![![![-299161, 27855, -65937, 85274, 297780]], ![![722792, 169167, -440473, -1478847, 1575532]], ![![573905, -26838, 59027, -306759, -313108]], ![![278627, 81299, -210601, -656669, 763480]], ![![-520643, 40576, -94712, 190936, 441555]]]
  g := ![![![4544438, -273359, -2303596, 798133, -5102852], ![7946946, -478242, -4028333, 1396177, -8923492], ![13893397, -835779, -7043071, 2440280, -15601060], ![4859127, -292288, -2463092, 853397, -5456188], ![5507046, -331255, -2791652, 967197, -6183849]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [2, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 10], [0, 1]]
 g := ![![[10, 5], [0, 4], [1]], ![[9, 6], [8, 7], [1]]]
 h' := ![![[2, 10], [0, 7], [9, 2], [0, 1]], ![[0, 1], [3, 4], [2, 9], [2, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [5, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [2, 9, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1754, 1001, -1676, -4827, 6790]
  a := ![7, 5, 8, 11, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3013, 3397, -1676, -4827, 6790]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![169, 121, 36, -11, 78]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![169, 121, 36, -11, 78]] 
 ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![169, 121, 36, -11, 78], ![256, 225, 65, -21, 146], ![480, 360, 121, -50, 270], ![182, 130, 38, -11, 82], ![200, 143, 46, -17, 101]]]
  hmulB := by decide  
  f := ![![![67, -1, 1, -48, -14]], ![![11, -4, 10, 13, -40]], ![![-90, 0, 1, 70, 10]], ![![23, 19, -49, -121, 184]], ![![87, 8, -22, -112, 71]]]
  g := ![![![-69, 121, 36, -11, 78], ![-132, 225, 65, -21, 146], ![-230, 360, 121, -50, 270], ![-73, 130, 38, -11, 82], ![-87, 143, 46, -17, 101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![651493, 574508, 166792, -54678, 375112]] ![![-9667623, -7534919, -2303596, 798133, -5102852]]
  ![![-24771222839027, -19304543972731, -5902319322872, 2045257260143, -13074524418116]] where
 M := ![![![-24771222839027, -19304543972731, -5902319322872, 2045257260143, -13074524418116]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![-24771222839027, -19304543972731, -5902319322872, 2045257260143, -13074524418116]] ![![169, 121, 36, -11, 78]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-14204081254070433, -11069448861592660, -3384448365847901, 1172763926046647, -7497060889536262]]]
 hmul := by decide  
 g := ![![![![-1291280114006403, -1006313532872060, -307677124167991, 106614902367877, -681550989957842]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16727499, -13035986, -3985711, 1381111, -8828948]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-16727499, -13035986, -3985711, 1381111, -8828948]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![2, 12, 12, 2, 1]] where
  M :=![![![-16727499, -13035986, -3985711, 1381111, -8828948], ![-29249066, -22794225, -6969260, 2414956, -15437956], ![-51143780, -39857110, -12186181, 4222700, -26994220], ![-17885612, -13938520, -4261658, 1476731, -9440212], ![-20271920, -15798208, -4830251, 1673757, -10699731]]]
  hmulB := by decide  
  f := ![![![49, -12, 27, 19, -108]], ![![-362, -21, 58, 402, -172]], ![![-1320, 270, -653, -400, 2700]], ![![1780, 116, -326, -2033, 980]], ![![-1170, 242, -587, -367, 2421]]]
  g := ![![![71569, 7147030, 7843205, 1464539, -8828948], ![125142, 12497019, 13714324, 2560836, -15437956], ![218820, 21851810, 23980343, 4477780, -26994220], ![76524, 7641848, 8386222, 1565935, -9440212], ![86734, 8661428, 9505117, 1774863, -10699731]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [2, 4, 5, 8, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 5, 7, 11], [1, 8, 11, 9], [0, 12, 8, 6], [0, 1]]
 g := ![![[11, 2, 3, 10], [7, 5, 1], []], ![[0, 4, 7, 3, 7, 7], [9, 10, 10], [10, 5, 4, 0, 5, 5]], ![[6, 5, 1, 3, 3, 3], [9, 1, 10], [10, 8, 8, 6, 0, 1]], ![[0, 6, 1, 4, 6, 7], [0, 10, 1], [0, 1, 9, 12, 7, 8]]]
 h' := ![![[4, 5, 7, 11], [12, 1, 8, 6], [0, 0, 0, 1], [0, 1]], ![[1, 8, 11, 9], [7, 11, 1, 9], [5, 8, 12, 7], [4, 5, 7, 11]], ![[0, 12, 8, 6], [5, 8, 3, 3], [7, 7, 10, 6], [1, 8, 11, 9]], ![[0, 1], [0, 6, 1, 8], [0, 11, 4, 12], [0, 12, 8, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2, 6, 3], []]
 b := ![[], [], [10, 1, 12, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [2, 4, 5, 8, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7158, 6608, -15323, -23915, 55922]
  a := ![-1, -3, 0, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9154, -51112, -52799, -10443, 55922]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, 12, -27, -19, 108]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-49, 12, -27, -19, 108]] 
 ![![13, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-49, 12, -27, -19, 108], ![362, 21, -58, -402, 172], ![1320, -270, 653, 400, -2700], ![-1780, -116, 326, 2033, -980], ![-1316, 50, -107, 767, 607]]]
  hmulB := by decide  
  f := ![![![16727499, 13035986, 3985711, -1381111, 8828948]], ![![11257043, 8772779, 2682249, -929441, 5941584]], ![![7794329, 6074236, 1857178, -643541, 4113928]], ![![2662547, 2074962, 634413, -219834, 1405320]], ![![11853224, 9237392, 2824303, -978665, 6256255]]]
  g := ![![![-69, 12, -27, -19, 108], ![-45, 21, -58, -402, 172], ![1727, -270, 653, 400, -2700], ![297, -116, 326, 2033, -980], ![-536, 50, -107, 767, 607]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-16727499, -13035986, -3985711, 1381111, -8828948]] ![![-49, 12, -27, -19, 108]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-386755, -46075, 122962, 552083, -411702]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-386755, -46075, 122962, 552083, -411702]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![10, 2, 6, 1, 0], ![0, 16, 1, 0, 1]] where
  M :=![![![-386755, -46075, 122962, 552083, -411702], ![-2339272, 305709, -738539, 193667, 3181558], ![9157340, 1229620, -3263183, -13818370, 11094010], ![12183754, -1477078, 3554470, -1628567, -15452986], ![1958644, -1150241, 2886636, 4651425, -11343119]]]
  hmulB := by decide  
  f := ![![![-372907, 214813, -16143, 41250, 1802]], ![![-77094, -288605, 130511, -209871, 335406]], ![![1425960, -161430, -204269, 275950, -672750]], ![![244616, 50786, -66714, 98957, -194694]], ![![16940, -273341, 106622, -174676, 264963]]]
  g := ![![![-347505, 319823, -163402, 552083, -411702], ![-251526, -2999209, -298947, 193667, 3181558], ![8667120, -8743400, 4032531, -13818370, 11094010], ![1674672, 14648696, 1692874, -1628567, -15452986], ![-2620918, 10060989, -804635, 4651425, -11343119]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [16, 2, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 15, 7], [4, 1, 10], [0, 1]]
 g := ![![[4, 15, 15], [9, 2], [8, 1], []], ![[12, 12, 16, 12], [1, 13], [12, 1], [7, 15]], ![[15, 11, 7, 7], [10, 4], [6, 4], [4, 15]]]
 h' := ![![[4, 15, 7], [5, 16, 10], [8, 2, 11], [0, 0, 1], [0, 1]], ![[4, 1, 10], [10, 5, 3], [14, 1, 8], [6, 2, 1], [4, 15, 7]], ![[0, 1], [14, 13, 4], [15, 14, 15], [3, 15, 15], [4, 1, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 11], []]
 b := ![[], [2, 5, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [16, 2, 9, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1773002, -367813, 914016, 618967, -3767902]
  a := ![4, -1, 11, 4, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-259804, 3451805, 56948, 618967, -3767902]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![372907, -214813, 16143, -41250, -1802]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![372907, -214813, 16143, -41250, -1802]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![14, 4, 1, 0, 0], ![16, 3, 0, 1, 0], ![4, 5, 0, 0, 1]] where
  M :=![![![372907, -214813, 16143, -41250, -1802], ![77094, 288605, -130511, 209871, -335406], ![-1425960, 161430, 204269, -275950, 672750], ![514030, -261022, 8116, -33811, -37870], ![-95524, -132313, 71333, -112494, 189375]]]
  hmulB := by decide  
  f := ![![![386755, 46075, -122962, -552083, 411702]], ![![2339272, -305709, 738539, -193667, -3181558]], ![![330254, -106318, 264463, 312620, -1062142]], ![![60126, 76303, -194485, -457986, 735032]], ![![663808, -11412, 18483, -460476, -171639]]]
  g := ![![![47889, -8625, 16143, -41250, -1802], ![-6592, 109298, -130511, 209871, -335406], ![-150678, -187738, 204269, -275950, 672750], ![64286, -159, 8116, -33811, -37870], ![-3046, -60414, 71333, -112494, 189375]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [14, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 16], [0, 1]]
 g := ![![[7, 16], [9], [16], [1]], ![[3, 1], [9], [16], [1]]]
 h' := ![![[4, 16], [12, 4], [6, 3], [3, 4], [0, 1]], ![[0, 1], [11, 13], [1, 14], [2, 13], [4, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [5, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [14, 13, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1598, 867, -2006, -3117, 7980]
  a := ![-5, 7, -6, -8, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2614, -1274, -2006, -3117, 7980]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-386755, -46075, 122962, 552083, -411702]] ![![372907, -214813, 16143, -41250, -1802]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-987, 244, 88, -104, 332]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-987, 244, 88, -104, 332]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![16, 1, 12, 1, 0], ![14, 7, 7, 0, 1]] where
  M :=![![![-987, 244, 88, -104, 332], ![1204, -863, 120, -244, 164], ![980, 880, -539, 840, -1460], ![-1212, 240, 132, -167, 468], ![-540, 452, -80, 152, -139]]]
  hmulB := by decide  
  f := ![![![-41, -28, -8, 8, -20]], ![![-76, -45, -24, -4, 4]], ![![20, -80, -41, -120, -20]], ![![-24, -79, -32, -67, -40]], ![![-54, -69, -29, -36, -27]]]
  g := ![![![-209, -104, -52, -104, 332], ![148, -93, 100, -244, 164], ![420, 540, -21, 840, -1460], ![-268, -151, -60, -167, 468], ![-54, 67, -49, 152, -139]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [17, 9, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 16, 2], [7, 2, 17], [0, 1]]
 g := ![![[6, 17, 7], [16, 2, 5], [0, 1], []], ![[15, 6, 8, 14], [3, 4, 17, 12], [5, 4], [7, 4]], ![[1, 6], [7, 2, 16, 6], [17, 9], [11, 4]]]
 h' := ![![[12, 16, 2], [13, 12, 11], [0, 2, 10], [0, 0, 1], [0, 1]], ![[7, 2, 17], [14, 11, 8], [8, 16, 5], [6, 6, 2], [12, 16, 2]], ![[0, 1], [4, 15], [2, 1, 4], [14, 13, 16], [7, 2, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 14], []]
 b := ![[], [8, 5, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [17, 9, 0, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-106265, 8060, -18257, 41311, 86648]
  a := ![-1, 5, -2, -1, 8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-104227, -33673, -58975, 41311, 86648]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2463, -175, 535, -774, 1618]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-2463, -175, 535, -774, 1618]] 
 ![![19, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-2463, -175, 535, -774, 1618], ![6402, -2393, -245, 143, -1338], ![-4300, 5350, -1341, 2360, -2870], ![-2666, -490, 700, -1035, 2054], ![-3262, 1373, 63, 28, 527]]]
  hmulB := by decide  
  f := ![![![5643, 4407, 1336, -483, 3022]], ![![1716, 1333, 405, -151, 910]], ![![1811, 1399, 441, -131, 904]], ![![2951, 2335, 710, -222, 1600]], ![![4793, 3762, 1136, -404, 2597]]]
  g := ![![![-1088, -175, 535, -774, 1618], ![1868, -2393, -245, 143, -1338], ![7, 5350, -1341, 2360, -2870], ![-1279, -490, 700, -1035, 2054], ![-900, 1373, 63, 28, 527]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-50161, -37644, 24605, -38127, 67268]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-50161, -37644, 24605, -38127, 67268]] 
 ![![19, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-50161, -37644, 24605, -38127, 67268], ![278058, -59147, -28658, 35602, -103212], ![-380840, 246050, -27139, 59540, -24820], ![-38708, -57316, 30358, -47971, 80372], ![-149648, 38610, 12697, -14713, 48723]]]
  hmulB := by decide  
  f := ![![![-53579, -41674, -12903, 4139, -27708]], ![![-38650, -30163, -9320, 2940, -20132]], ![![-31108, -24338, -7295, 2808, -16956]], ![![-45899, -35242, -10913, 3940, -23344]], ![![-26268, -20176, -6325, 2079, -13125]]]
  g := ![![![12552, -37644, 24605, -38127, 67268], ![79408, -59147, -28658, 35602, -103212], ![-200572, 246050, -27139, 59540, -24820], ![25411, -57316, 30358, -47971, 80372], ![-46507, 38610, 12697, -14713, 48723]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-987, 244, 88, -104, 332]] ![![-2463, -175, 535, -774, 1618]]
  ![![2808949, 566429, -757717, 1123446, -2214650]] where
 M := ![![![2808949, 566429, -757717, 1123446, -2214650]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![2808949, 566429, -757717, 1123446, -2214650]] ![![-50161, -37644, 24605, -38127, 67268]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![593100961805, -475577987505, 79431312144, -153353946061, 131685857286]]]
 hmul := by decide  
 g := ![![![![31215840095, -25030420395, 4180595376, -8071260319, 6930834594]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37581221, 29287621, 8954552, -3102857, 19835664]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![37581221, 29287621, 8954552, -3102857, 19835664]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![15, 2, 7, 1, 0], ![3, 20, 18, 0, 1]] where
  M :=![![![37581221, 29287621, 8954552, -3102857, 19835664], ![65712706, 51211171, 15657671, -5425661, 34684136], ![114903730, 89545520, 27378357, -9487070, 60647120], ![40183100, 31315342, 9574508, -3317673, 21208960], ![45544502, 35493335, 10851966, -3760359, 24038709]]]
  hmulB := by decide  
  f := ![![![-20281, -2001, 5395, 26716, -17560]], ![![-106112, 15591, -37873, -493, 161048]], ![![484130, 53950, -144471, -671030, 479200]], ![![149061, 13177, -35772, -188123, 114216]], ![![286729, 53108, -139224, -511296, 489133]]]
  g := ![![![1070308, -15705215, -14189887, -3102857, 19835664], ![1871531, -27461749, -24812050, -5425661, 34684136], ![3272540, -48018380, -43385231, -9487070, 60647120], ![1144405, -16792544, -15172307, -3317673, 21208960], ![1297120, -19033049, -17196621, -3760359, 24038709]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [20, 5, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 1, 20], [7, 21, 3], [0, 1]]
 g := ![![[16, 0, 1], [20, 22, 4], [7, 9, 1], []], ![[17, 15], [6, 0, 18, 17], [17, 3, 0, 11], [6, 9]], ![[4, 11, 0, 3], [21, 20, 16, 4], [19, 4, 19, 3], [0, 9]]]
 h' := ![![[2, 1, 20], [14, 16, 22], [21, 15, 21], [0, 0, 1], [0, 1]], ![[7, 21, 3], [1, 15], [7, 13, 5], [22, 1, 21], [2, 1, 20]], ![[0, 1], [8, 15, 1], [5, 18, 20], [3, 22, 1], [7, 21, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 15], []]
 b := ![[], [20, 13, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [20, 5, 14, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11966582, 3535068, -8614597, -9938363, 35199690]
  a := ![-2, 11, -27, -3, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1369991, -29590522, -24897412, -9938363, 35199690]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20281, 2001, -5395, -26716, 17560]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![20281, 2001, -5395, -26716, 17560]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![21, 11, 1, 0, 0], ![9, 3, 0, 1, 0], ![12, 4, 0, 0, 1]] where
  M :=![![![20281, 2001, -5395, -26716, 17560], ![106112, -15591, 37873, 493, -161048], ![-484130, -53950, 144471, 671030, -479200], ![-555932, 75746, -183362, 29373, 786128], ![-63510, 55433, -139601, -248444, 543821]]]
  hmulB := by decide  
  f := ![![![-37581221, -29287621, -8954552, 3102857, -19835664]], ![![-65712706, -51211171, -15657671, 5425661, -34684136]], ![![-70736919, -55126454, -16854710, 5840406, -37335720]], ![![-25024009, -19501628, -5962543, 2066103, -13207928]], ![![-33016086, -25729977, -7866838, 2725969, -17426227]]]
  g := ![![![7100, 3098, -5395, -26716, 17560], ![53866, 9153, 37873, 493, -161048], ![-165517, -75627, 144471, 671030, -479200], ![-278401, -49561, -183362, 29373, 786128], ![-61815, 7004, -139601, -248444, 543821]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [16, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 22], [0, 1]]
 g := ![![[5, 13], [16, 16], [10, 6], [1]], ![[0, 10], [1, 7], [13, 17], [1]]]
 h' := ![![[12, 22], [20, 6], [1, 4], [7, 12], [0, 1]], ![[0, 1], [0, 17], [3, 19], [13, 11], [12, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [22, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [16, 11, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-278, 213, -29, 136, -84]
  a := ![3, 1, -3, 4, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5, 20, -29, 136, -84]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![37581221, 29287621, 8954552, -3102857, 19835664]] ![![20281, 2001, -5395, -26716, 17560]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)


lemma PB1567I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1567I0 : PrimesBelowBoundCertificateInterval O 1 23 1567 where
  m := 9
  g := ![5, 4, 5, 2, 3, 2, 2, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1567I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0, I2N1, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![9, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![343, 49]
    · exact ![121, 121, 11]
    · exact ![28561, 13]
    · exact ![4913, 289]
    · exact ![6859, 19, 19]
    · exact ![12167, 529]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N0
      exact NI2N1
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N0, I7N1, I11N0, I11N1, I11N2, I13N1, I17N1, I19N1, I19N2, I23N1]
  Il := ![[I2N0, I2N0, I2N0, I2N1, I2N2], [I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1], [I11N0, I11N1, I11N2], [I13N1], [I17N1], [I19N1, I19N2], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
