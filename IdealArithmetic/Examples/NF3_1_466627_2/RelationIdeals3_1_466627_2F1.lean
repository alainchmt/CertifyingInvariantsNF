import IdealArithmetic.Examples.NF3_1_466627_2.PrimesBelow3_1_466627_2F1
import IdealArithmetic.Examples.NF3_1_466627_2.ClassGroupData3_1_466627_2

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 1024 ![![37, 0, 0], ![-3, 1, 0]]
  ![-375, 5, 3] ![![1024, 0, 0], ![-343, 1, 0]] where
    su := ![![37888, 0, 0], ![-3072, 1024, 0]]
    hsu := by decide
    w := ![![-384000, 5120, 3072], ![129024, -2048, -1024]]
    hw := by decide
    g := ![![![97777865, 332451209210, -969246339], ![291908262, 992508251135, 0]], ![![-8456323, -28752536533, 83826709], ![-25245699, -85838550016, 0]]]
    h := ![![![-1211835, 406450, -836], ![-14945840, 30935, 0]], ![![407184, -136567, 280], ![5021894, -10361, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {1024} * I37N1 =  Ideal.span {B.equivFun.symm ![-375, 5, 3]} * (J0 ^ 10*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10J1_0 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 24576 ![![41, 0, 0], ![8, 1, 0]]
  ![6263, 1787, 253] ![![24576, 0, 0], ![-1367, 1, 0]] where
    su := ![![1007616, 0, 0], ![196608, 24576, 0]]
    hsu := by decide
    w := ![![153919488, 43917312, 6217728], ![-8527872, -2433024, -344064]]
    hw := by decide
    g := ![![![85275258437, 37793623860152582, -27647127960888], ![1533083212398, 679455816766783517, 0]], ![![14562129033, 6453871950350592, -4721193826630], ![261798744049, 116028059483258883, 0]]]
    h := ![![![828351015, 109185820, 705246], ![-4245298169, -28914833, 0]], ![![-45894587, -6049422, -39075], ![235209715, 1602061, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {24576} * I41N1 =  Ideal.span {B.equivFun.symm ![6263, 1787, 253]} * (J0 ^ 10*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10J1_1 E41RS1 


noncomputable def E47RS0 : RelationCertificate Table 4608 ![![47, 0, 0], ![4, 1, 0]]
  ![1243, 79, -55] ![![4608, 0, 0], ![169, 1, 0]] where
    su := ![![216576, 0, 0], ![18432, 4608, 0]]
    hsu := by decide
    w := ![![5727744, 364032, -253440], ![202752, 13824, -9216]]
    hw := by decide
    g := ![![![-41, -1262937, -7473], ![1117, 34435577, 0]], ![![-12, -140946, -834], ![327, 3843070, 0]]]
    h := ![![![1237, 305, -1], ![-14224, -8, 0]], ![![36, 5, -1], ![-412, 45, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {4608} * I47N0 =  Ideal.span {B.equivFun.symm ![1243, 79, -55]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E47RS0 


noncomputable def E47RS1 : RelationCertificate Table 1024 ![![47, 0, 0], ![5, 1, 0]]
  ![-173, -25, -15] ![![1024, 0, 0], ![-343, 1, 0]] where
    su := ![![48128, 0, 0], ![5120, 1024, 0]]
    hsu := by decide
    w := ![![-177152, -25600, -15360], ![57344, 8192, 5120]]
    hw := by decide
    g := ![![![-412175919642922, -1401428168763241351, 4085799913825969], ![-1230519363598694, -4183859111757792251, 0]], ![![-43173909773296, -146794440016649764, 427972495300603], ![-128892372034563, -438243835187817472, 0]]]
    h := ![![![-324, -68, -1], ![3011, 32, 0]], ![![98, 19, 0], ![-910, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {1024} * I47N1 =  Ideal.span {B.equivFun.symm ![-173, -25, -15]} * (J0 ^ 10*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10J1_0 E47RS1 


noncomputable def E47RS2 : RelationCertificate Table 49152 ![![47, 0, 0], ![-9, 1, 0]]
  ![-3323, -1007, 215] ![![49152, 0, 0], ![-1367, 1, 0]] where
    su := ![![2310144, 0, 0], ![-442368, 49152, 0]]
    hsu := by decide
    w := ![![-163332096, -49496064, 10567680], ![4571136, 1376256, -294912]]
    hw := by decide
    g := ![![![529, 37392917, -27354], ![19021, 1344503786, 0]], ![![114, -7135740, 5220], ![4099, -256573437, 0]]]
    h := ![![![-16120, 1821, -2], ![-83813, 309, 0]], ![![456, -51, 0], ![2371, -6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N2 : Ideal.span {49152} * I47N2 =  Ideal.span {B.equivFun.symm ![-3323, -1007, 215]} * (J0 ^ 11*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_1 E47RS2 


noncomputable def E53RS0 : RelationCertificate Table 24 ![![53, 0, 0], ![6, 1, 0]]
  ![11, -1, 1] ![![24, 0, 0], ![1, 1, 0]] where
    su := ![![1272, 0, 0], ![144, 24, 0]]
    hsu := by decide
    w := ![![264, -24, 24], ![144, 24, 0]]
    hw := by decide
    g := ![![![-987, 570009, 570997], ![23719, -13703929, 0]], ![![-159, 91404, 91563], ![3817, -2197512, 0]]]
    h := ![![![1, 0, 0], ![-7, 1, 0]], ![![-6, -1, 0], ![54, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {24} * I53N0 =  Ideal.span {B.equivFun.symm ![11, -1, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 73728 ![![53, 0, 0], ![23, 1, 0]]
  ![-6283, 1217, -89] ![![73728, 0, 0], ![23209, 1, 0]] where
    su := ![![3907584, 0, 0], ![1695744, 73728, 0]]
    hsu := by decide
    w := ![![-463233024, 89726976, -6561792], ![-145833984, 28237824, -2064384]]
    hw := by decide
    g := ![![![6927191774301, -1783202151060533862, -76832356041148], ![-22005601065779, 5664695946201759733, 0]], ![![2987468138293, -769035968112667965, -33135247888379], ![-9490286134692, 2442995556314406905, 0]]]
    h := ![![![-6222472986, -343932178, -3190867], ![14338741825, 169115862, 0]], ![![-1958948134, -108276103, -1004542], ![4514097788, 53240698, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {73728} * I53N1 =  Ideal.span {B.equivFun.symm ![-6283, 1217, -89]} * (J0 ^ 7*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_2 E53RS1 


noncomputable def E53RS2 : RelationCertificate Table 32 ![![53, 0, 0], ![24, 1, 0]]
  ![3, -9, 1] ![![32, 0, 0], ![9, 1, 0]] where
    su := ![![1696, 0, 0], ![768, 32, 0]]
    hsu := by decide
    w := ![![96, -288, 32], ![160, -64, 0]]
    hw := by decide
    g := ![![![-189031, 23207808, 2580979], ![672109, -82591330, 0]], ![![-88553, 10871989, 1209092], ![314854, -38690945, 0]]]
    h := ![![![783, 32, 0], ![-1729, 1, 0]], ![![1513, 87, 1], ![-3341, -53, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {32} * I53N2 =  Ideal.span {B.equivFun.symm ![3, -9, 1]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E53RS2 


noncomputable def E59RS0 : RelationCertificate Table 2048 ![![59, 0, 0], ![3, 1, 0]]
  ![447, 35, 21] ![![2048, 0, 0], ![681, 1, 0]] where
    su := ![![120832, 0, 0], ![6144, 2048, 0]]
    hsu := by decide
    w := ![![915456, 71680, 43008], ![307200, 24576, 14336]]
    hw := by decide
    g := ![![![-844249550, 5774697369803, 8479733641], ![2538947252, -17366494496775, 0]], ![![-28619026, 195752481134, 287448639], ![86067203, -588694812672, 0]]]
    h := ![![![441, 144, 0], ![-8524, 21, 0]], ![![144, 47, 0], ![-2782, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {2048} * I59N0 =  Ideal.span {B.equivFun.symm ![447, 35, 21]} * (J0 ^ 11*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_0 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 589824 ![![59, 0, 0], ![19, 1, 0]]
  ![-29587, -7975, -689] ![![589824, 0, 0], ![-50519, 1, 0]] where
    su := ![![34799616, 0, 0], ![11206656, 589824, 0]]
    hsu := by decide
    w := ![![-17451122688, -4703846400, -406388736], ![1494614016, 402849792, 34799616]]
    hw := by decide
    g := ![![![-8490942430901667, -58900695726610912080104, 1165911750564717954], ![-99134219370220013, -687682732365084202500158, 0]], ![![-2713812782377341, -18825408634684621532340, 372640167753485623], ![-31684552555532231, -219792114305031904100367, 0]]]
    h := ![![![-194049, -11639, -81], ![601016, 4090, 0]], ![![16600, 978, 6], ![-51414, -295, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {589824} * I59N1 =  Ideal.span {B.equivFun.symm ![-29587, -7975, -689]} * (J0 ^ 10*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10J1_2 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 192 ![![59, 0, 0], ![-22, 1, 0]]
  ![131, 23, 1] ![![192, 0, 0], ![-23, 1, 0]] where
    su := ![![11328, 0, 0], ![-4224, 192, 0]]
    hsu := by decide
    w := ![![25152, 4416, 192], ![-2880, -384, 0]]
    hw := by decide
    g := ![![![1181031, 1920084653, -83484174], ![9859039, 16028961410, 0]], ![![-436657, -709936321, 30867622], ![-3645136, -5926583425, 0]]]
    h := ![![![600993, -30375, 139], ![1611748, -8200, 0]], ![![-68817, 3480, -16], ![-184554, 944, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {192} * I59N2 =  Ideal.span {B.equivFun.symm ![131, 23, 1]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E59RS2 


noncomputable def E61RS1 : RelationCertificate Table 294912 ![![61, 0, 0], ![-23, 1, 0]]
  ![-38737, 2387, 613] ![![294912, 0, 0], ![-50519, 1, 0]] where
    su := ![![17989632, 0, 0], ![-6782976, 294912, 0]]
    hsu := by decide
    w := ![![-11424006144, 703954944, 180781056], ![1957036032, -120619008, -30965760]]
    hw := by decide
    g := ![![![48074, 8804299748, -174277], ![280639, 51396378542, 0]], ![![47507, -3195528823, 63254], ![277329, -18654363625, 0]]]
    h := ![![![-184399, 8674, -18], ![-487374, 1711, 0]], ![![31612, -1462, 2], ![83552, -227, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {294912} * I61N1 =  Ideal.span {B.equivFun.symm ![-38737, 2387, 613]} * (J0 ^ 9*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9J1_2 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 192 ![![67, 0, 0], ![-25, 1, 0]]
  ![-61, 23, 1] ![![192, 0, 0], ![-23, 1, 0]] where
    su := ![![12864, 0, 0], ![-4800, 192, 0]]
    hsu := by decide
    w := ![![-11712, 4416, 192], ![1536, -576, 0]]
    hw := by decide
    g := ![![![9, 0, 0], ![77, 3, 0]], ![![20, -1, 0], ![166, -1, 0]]]
    h := ![![![-316533, 14112, -58], ![-848306, 3887, 0]], ![![41524, -1836, 7], ![111284, -469, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {192} * I67N1 =  Ideal.span {B.equivFun.symm ![-61, 23, 1]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 24576 ![![71, 0, 0], ![-34, 1, 0]]
  ![5657, 1877, 307] ![![24576, 0, 0], ![-1367, 1, 0]] where
    su := ![![1744896, 0, 0], ![-835584, 24576, 0]]
    hsu := by decide
    w := ![![139026432, 46129152, 7544832], ![-7692288, -2555904, -417792]]
    hw := by decide
    g := ![![![82, 29311215, -21442], ![1475, 526958611, 0]], ![![756, -12996070, 9507], ![13591, -233644040, 0]]]
    h := ![![![94989, -3094, 14], ![198193, -687, 0]], ![![-5193, 177, -1], ![-10835, 54, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {24576} * I71N1 =  Ideal.span {B.equivFun.symm ![5657, 1877, 307]} * (J0 ^ 10*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10J1_1 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 2048 ![![73, 0, 0], ![-1, 1, 0]]
  ![-649, -5, -3] ![![2048, 0, 0], ![681, 1, 0]] where
    su := ![![149504, 0, 0], ![-2048, 2048, 0]]
    hsu := by decide
    w := ![![-1329152, -10240, -6144], ![-442368, -4096, -2048]]
    hw := by decide
    g := ![![![-27009596, 184743908068, 271283330], ![81227096, -555588259839, 0]], ![![739567, -5061480339, -7432425], ![-2224131, 15221606400, 0]]]
    h := ![![![-18, 10, -1], ![-665, 70, 0]], ![![-4, 2, -1], ![-76, 72, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {2048} * I73N1 =  Ideal.span {B.equivFun.symm ![-649, -5, -3]} * (J0 ^ 11*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_0 E73RS1 
