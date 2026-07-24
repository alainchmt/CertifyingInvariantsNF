import IdealArithmetic.Examples.NF3_1_392196_1.PrimesBelow3_1_392196_1F1
import IdealArithmetic.Examples.NF3_1_392196_1.ClassGroupData3_1_392196_1

set_option linter.all false

noncomputable section


noncomputable def E43RS1 : RelationCertificate Table 12 ![![43, 0, 0], ![-17, 1, 0]]
  ![-4490238, -46582, -192559] ![![12, 0, 0], ![19, 0, 1]] where
    su := ![![516, 0, 0], ![-204, 12, 0]]
    hsu := by decide
    w := ![![-53882856, -558984, -2310708], ![-97898796, -1015608, -4198284]]
    hw := by decide
    g := ![![![-15849, 2154, 768], ![-25021, 8248, 0]], ![![-236153261809, 31005072705, 10416724040], ![-373041270857, 124020291145, 0]]]
    h := ![![![2377486, -29662314, 9374195], ![-1629736, -67213824, 0]], ![![4319611, -53892927, 17031807], ![-2961040, -122119593, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {12} * I43N1 =  Ideal.span {B.equivFun.symm ![-4490238, -46582, -192559]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 12 ![![47, 0, 0], ![19, 1, 0]]
  ![-190, 38, 21] ![![12, 0, 0], ![69, 1, 5]] where
    su := ![![564, 0, 0], ![228, 12, 0]]
    hsu := by decide
    w := ![![-2280, 456, 252], ![8676, -1656, -1056]]
    hw := by decide
    g := ![![![-14237227263399312, 51897806490352627, 12980294800368167], ![-72130783390196469, 12805648709163900, 1645]], ![![-5452555535206868, 19875757182828163, 4971177108643364], ![-27624557433602143, 4904291366519549, 630]]]
    h := ![![![-18240, -194160, -68613], ![-11466, 537472, 0]], ![![69229, 737530, 260632], ![43696, -2041632, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {12} * I47N1 =  Ideal.span {B.equivFun.symm ![-190, 38, 21]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E47RS1 


noncomputable def E61RS0 : RelationCertificate Table 2 ![![61, 0, 0], ![16, 1, 0]]
  ![24, 0, 1] ![![2, 0, 0], ![15, 0, 1]] where
    su := ![![122, 0, 0], ![32, 2, 0]]
    hsu := by decide
    w := ![![48, 0, 2], ![406, 6, 18]]
    hw := by decide
    g := ![![![141, -639, -296], ![957, -183, 0]], ![![29, -157, -73], ![236, -45, 0]]]
    h := ![![![808, 6241, 2677], ![323, -27216, 0]], ![![6849, 52771, 22635], ![2666, -230121, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {2} * I61N0 =  Ideal.span {B.equivFun.symm ![24, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 12 ![![61, 0, 0], ![21, 1, 0]]
  ![255830, 2654, 10971] ![![12, 0, 0], ![69, 1, 5]] where
    su := ![![732, 0, 0], ![252, 12, 0]]
    hsu := by decide
    w := ![![3069960, 31848, 131652], ![22120188, 229476, 948600]]
    hw := by decide
    g := ![![![2936317521, -10703518816, -2677085604], ![14876413693, -2641065429, -171]], ![![1030286847, -3755620634, -939328281], ![5219794269, -926689622, -60]]]
    h := ![![![-4310057, -48395251, -15294333], ![-2277101, 155494214, 0]], ![![-31055431, -348705532, -110201280], ![-16407670, 1120392855, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {12} * I61N1 =  Ideal.span {B.equivFun.symm ![255830, 2654, 10971]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 3 ![![61, 0, 0], ![24, 1, 0]]
  ![121071, 1256, 5192] ![![3, 0, 0], ![13, 0, 1]] where
    su := ![![183, 0, 0], ![72, 3, 0]]
    hsu := by decide
    w := ![![363213, 3768, 15576], ![1913235, 19848, 82047]]
    hw := by decide
    g := ![![![-12, -72, 61], ![17, 0, 0]], ![![1, -49, 13], ![25, 0, 0]]]
    h := ![![![-802821, -10991339, -2999776], ![-496001, 30498588, 0]], ![![-4228819, -57897194, -15801407], ![-2612862, 160652196, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {3} * I61N2 =  Ideal.span {B.equivFun.symm ![121071, 1256, 5192]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E61RS2 


noncomputable def E67RS0 : RelationCertificate Table 3 ![![67, 0, 0], ![1, 1, 0]]
  ![1, 1, 0] ![![3, 0, 0], ![-14, -1, -1]] where
    su := ![![201, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![3, 3, 0], ![-96, 9, -9]]
    hw := by decide
    g := ![![![112383, -338124, -185817], ![-349763, 0, 41538]], ![![4887, -14701, -8079], ![-15207, 0, 1806]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![186, -94, 561], ![36, -6265, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {3} * I67N0 =  Ideal.span {B.equivFun.symm ![1, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 4 ![![67, 0, 0], ![18, 1, 0]]
  ![210, 2, 9] ![![4, 0, 0], ![15, 0, 1]] where
    su := ![![268, 0, 0], ![72, 4, 0]]
    hsu := by decide
    w := ![![840, 8, 36], ![3724, 40, 160]]
    hw := by decide
    g := ![![![130840, -166650, -70636], ![473001, -95230, 0]], ![![44220485, -56322939, -23872415], ![159858734, -32184537, 0]]]
    h := ![![![-61938, -548486, -205821], ![-24812, 2298336, 0]], ![![-274583, -2431549, -912446], ![-109999, 10188987, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {4} * I67N1 =  Ideal.span {B.equivFun.symm ![210, 2, 9]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 6 ![![67, 0, 0], ![-19, 1, 0]]
  ![52, -24, 11] ![![6, 0, 0], ![13, 0, 1]] where
    su := ![![402, 0, 0], ![-114, 6, 0]]
    hsu := by decide
    w := ![![312, -144, 66], ![-738, 282, -84]]
    hw := by decide
    g := ![![![-3305, 1015, 553], ![-7037, 737, 0]], ![![874, -309, -154], ![1885, -220, 0]]]
    h := ![![![-233, 2795, -799], ![115, 8924, 0]], ![![564, -6542, 1870], ![-203, -20884, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {6} * I67N2 =  Ideal.span {B.equivFun.symm ![52, -24, 11]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E67RS2 


noncomputable def E71RS0 : RelationCertificate Table 6 ![![71, 0, 0], ![24, 1, 0]]
  ![40, -14, 3] ![![6, 0, 0], ![17, 1, 1]] where
    su := ![![426, 0, 0], ![144, 6, 0]]
    hsu := by decide
    w := ![![240, -84, 18], ![-90, 90, -78]]
    hw := by decide
    g := ![![![-1322501, 1572154, -521270], ![-3571901, 837445, -71]], ![![-428419, 509287, -168863], ![-1157078, 271285, -23]]]
    h := ![![![1260, 16391, 4473], ![685, -52930, 0]], ![![-585, -7340, -2003], ![-245, 23700, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {6} * I71N0 =  Ideal.span {B.equivFun.symm ![40, -14, 3]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 12 ![![71, 0, 0], ![-21, 1, 0]]
  ![-166, -2, -7] ![![12, 0, 0], ![19, 0, 1]] where
    su := ![![852, 0, 0], ![-252, 12, 0]]
    hsu := by decide
    w := ![![-1992, -24, -84], ![-3636, -36, -156]]
    hw := by decide
    g := ![![![-141, 19, 6], ![-213, 71, 0]], ![![39, -6, -2], ![69, -22, 0]]]
    h := ![![![-92804, 1218436, -318017], ![44642, 3763200, 0]], ![![-169416, 2224190, -580523], ![81467, 6869520, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {12} * I71N1 =  Ideal.span {B.equivFun.symm ![-166, -2, -7]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 6 ![![73, 0, 0], ![-9, 1, 0]]
  ![-4, 0, 1] ![![6, 0, 0], ![13, 0, 1]] where
    su := ![![438, 0, 0], ![-54, 6, 0]]
    hsu := by decide
    w := ![![-24, 0, 6], ![-6, 6, -12]]
    hw := by decide
    g := ![![![-1922, 1204, 410], ![-4079, 803, 0]], ![![251, -165, -57], ![563, -110, 0]]]
    h := ![![![353, -1981, 1081], ![-59, -13152, 0]], ![![107, -558, 304], ![46, -3699, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {6} * I73N1 =  Ideal.span {B.equivFun.symm ![-4, 0, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 12 ![![79, 0, 0], ![29, 1, 0]]
  ![-90034, -934, -3861] ![![12, 0, 0], ![69, 1, 5]] where
    su := ![![948, 0, 0], ![348, 12, 0]]
    hsu := by decide
    w := ![![-1080408, -11208, -46332], ![-7784724, -80760, -333840]]
    hw := by decide
    g := ![![![-1445555857929049830973, 5269367187715651740874, 1317935075360276049534], ![-7323692636048950528639, 1300202642245090008932, 2765]], ![![-512348911887280777126, 1867623814155760686925, 467116229438752549316], ![-2595739163239404181943, 460831316433249396955, 980]]]
    h := ![![![676529, 11068841, 2460789], ![388491, -32401032, 0]], ![![4874708, 79754939, 17730860], ![2799009, -233460960, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {12} * I79N1 =  Ideal.span {B.equivFun.symm ![-90034, -934, -3861]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E79RS1 
