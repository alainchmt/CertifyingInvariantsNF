import IdealArithmetic.Examples.NF3_1_420812_2.PrimesBelow3_1_420812_2F2
import IdealArithmetic.Examples.NF3_1_420812_2.ClassGroupData3_1_420812_2

set_option linter.all false

noncomputable section


noncomputable def E97RS1 : RelationCertificate Table 10 ![![97, 0, 0], ![24, 1, 0]]
  ![4, -2, 1] ![![10, 0, 0], ![3, 1, 0]] where
    su := ![![970, 0, 0], ![240, 10, 0]]
    hsu := by decide
    w := ![![40, -20, 10], ![10, -40, 0]]
    hw := by decide
    g := ![![![-168686, -594154, -403436], ![-110015, 2017184, 0]], ![![-42173, -148539, -100859], ![-27499, 504296, 0]]]
    h := ![![![-170, -4164, -347], ![-14, 16830, 0]], ![![-44, -1080, -90], ![-4, 4365, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {10} * I97N1 =  Ideal.span {B.equivFun.symm ![4, -2, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 250 ![![101, 0, 0], ![-24, 1, 0]]
  ![-318, -6, -7] ![![250, 0, 0], ![33, 1, 0]] where
    su := ![![25250, 0, 0], ![-6000, 250, 0]]
    hsu := by decide
    w := ![![-79500, -1500, -1750], ![-10500, -250, -250]]
    hw := by decide
    g := ![![![-137602963, -4701793972, -284966173], ![-36970635, 35620771626, 0]], ![![32004922, 1093585785, 66280011], ![8599118, -8285001375, 0]]]
    h := ![![![546, -14267, 1189], ![-191, -60048, 0]], ![![75, -1884, 157], ![-13, -7929, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {250} * I101N1 =  Ideal.span {B.equivFun.symm ![-318, -6, -7]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 5 ![![103, 0, 0], ![23, 1, 0]]
  ![112, -1, 3] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![515, 0, 0], ![115, 5, 0]]
    hsu := by decide
    w := ![![560, -5, 15], ![-225, 0, -5]]
    hw := by decide
    g := ![![![63, -157, 165], ![-51, -412, 0]], ![![15, -35, 36], ![-8, -90, 0]]]
    h := ![![![4367, 111058, 9659], ![2076, -497437, 0]], ![![-1769, -44578, -3877], ![-761, 199665, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {5} * I103N0 =  Ideal.span {B.equivFun.symm ![112, -1, 3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 50 ![![103, 0, 0], ![37, 1, 0]]
  ![-24, -8, -1] ![![50, 0, 0], ![-17, 1, 0]] where
    su := ![![5150, 0, 0], ![1850, 50, 0]]
    hsu := by decide
    w := ![![-1200, -400, -50], ![400, 150, 0]]
    hw := by decide
    g := ![![![128, -2626, 309], ![-65, -7728, 0]], ![![62, -1012, 119], ![12, -2976, 0]]]
    h := ![![![35410, 1699514, 91881], ![29314, -4731872, 0]], ![![-11820, -565895, -30594], ![-9679, 1575591, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {50} * I103N1 =  Ideal.span {B.equivFun.symm ![-24, -8, -1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 250 ![![103, 0, 0], ![42, 1, 0]]
  ![-417, 11, -8] ![![250, 0, 0], ![-44, 0, 1]] where
    su := ![![25750, 0, 0], ![10500, 250, 0]]
    hsu := by decide
    w := ![![-104250, 2750, -2000], ![18500, -750, 250]]
    hw := by decide
    g := ![![![19911685539, -2391145066304623, 29159852858852], ![113134954977, -7290076421457580, -875483]], ![![8198929310, -984589141471215, 12006998193587], ![46584981293, -3001796162938468, -360493]]]
    h := ![![![-2010461, -118095324, -5624496], ![-1966297, 289661540, 0]], ![![356948, 20967945, 998635], ![349146, -51429702, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {250} * I103N2 =  Ideal.span {B.equivFun.symm ![-417, 11, -8]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E103RS2 


noncomputable def E109RS1 : RelationCertificate Table 10 ![![109, 0, 0], ![-29, 1, 0]]
  ![-151, 3, -4] ![![10, 0, 0], ![26, 0, 1]] where
    su := ![![1090, 0, 0], ![-290, 10, 0]]
    hsu := by decide
    w := ![![-1510, 30, -40], ![-3850, 40, -100]]
    hw := by decide
    g := ![![![258505, 121684185, -10645712], ![-392417, 102038304, -400936]], ![![-67463, -31743698, 2777141], ![102380, -26618686, 104592]]]
    h := ![![![18769, -626245, 43196], ![-10628, -2354184, 0]], ![![47771, -1595708, 110066], ![-27282, -5998602, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {10} * I109N1 =  Ideal.span {B.equivFun.symm ![-151, 3, -4]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E109RS1 


noncomputable def E113RS0 : RelationCertificate Table 1250 ![![113, 0, 0], ![41, 1, 0]]
  ![57, -131, -7] ![![1250, 0, 0], ![-217, 1, 0]] where
    su := ![![141250, 0, 0], ![51250, 1250, 0]]
    hsu := by decide
    w := ![![71250, -163750, -8750], ![-12500, 28750, 1250]]
    hw := by decide
    g := ![![![-4694051405, 1081911140286, -9971543637], ![1680417118, 6232214773155, 0]], ![![-1744701635, 402128570153, -3706258708], ![624583631, 2316411692511, 0]]]
    h := ![![![-5700371, -304531247, -14857239], ![-4763220, 839434000, 0]], ![![1000072, 53427433, 2606577], ![835694, -147271600, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N0 : Ideal.span {1250} * I113N0 =  Ideal.span {B.equivFun.symm ![57, -131, -7]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E113RS0 


noncomputable def E113RS1 : RelationCertificate Table 1250 ![![113, 0, 0], ![-21, 1, 0]]
  ![1152, -16, 23] ![![1250, 0, 0], ![-217, 1, 0]] where
    su := ![![141250, 0, 0], ![-26250, 1250, 0]]
    hsu := by decide
    w := ![![1440000, -20000, 28750], ![-250000, 3750, -5000]]
    hw := by decide
    g := ![![![4847, -1115705, 10283], ![-1697, -6426880, 0]], ![![-805, 206475, -1903], ![844, 1189376, 0]]]
    h := ![![![-57792428, 1300266860, -123853689], ![22247044, 6997733440, 0]], ![![10033677, -225746606, 21502932], ![-3862379, -1214915660, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {1250} * I113N1 =  Ideal.span {B.equivFun.symm ![1152, -16, 23]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E113RS1 


noncomputable def E127RS1 : RelationCertificate Table 10 ![![127, 0, 0], ![-10, 1, 0]]
  ![34, -2, 1] ![![10, 0, 0], ![3, 1, 0]] where
    su := ![![1270, 0, 0], ![-100, 10, 0]]
    hsu := by decide
    w := ![![340, -20, 10], ![100, -10, 0]]
    hw := by decide
    g := ![![![43, 147, 100], ![36, -499, 0]], ![![-5, -11, -7], ![4, 35, 0]]]
    h := ![![![-448, 4584, -917], ![130, 58230, 0]], ![![-125, 1349, -270], ![126, 17145, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {10} * I127N1 =  Ideal.span {B.equivFun.symm ![34, -2, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E127RS1 


noncomputable def E131RS0 : RelationCertificate Table 2 ![![131, 0, 0], ![5, 1, 0]]
  ![5, 1, 0] ![![2, 0, 0], ![26, 0, 1]] where
    su := ![![262, 0, 0], ![10, 2, 0]]
    hsu := by decide
    w := ![![10, 2, 0], ![130, -12, 6]]
    hw := by decide
    g := ![![![-20939, 1247092, 738867], ![97543, 0, 131273]], ![![-858, 49685, 29436], ![3888, 0, 5230]]]
    h := ![![![-152, -760, -304], ![1, 19912, 0]], ![![-1978, -9907, -3963], ![-79, 259578, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N0 : Ideal.span {2} * I131N0 =  Ideal.span {B.equivFun.symm ![5, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E131RS0 


noncomputable def E131RS1 : RelationCertificate Table 625 ![![131, 0, 0], ![61, 1, 0]]
  ![1898, -9, 52] ![![625, 0, 0], ![-217, 1, 0]] where
    su := ![![81875, 0, 0], ![38125, 625, 0]]
    hsu := by decide
    w := ![![1186250, -5625, 32500], ![-411875, 1875, -11250]]
    hw := by decide
    g := ![![![14316, -3909237, 36030], ![-10654, -11259372, 0]], ![![6857, -1850351, 17054], ![-4810, -5329374, 0]]]
    h := ![![![23766, 2255429, 73956], ![28404, -4844092, 0]], ![![-8282, -783100, -25678], ![-9797, 1681900, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {625} * I131N1 =  Ideal.span {B.equivFun.symm ![1898, -9, 52]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E131RS1 


noncomputable def E131RS2 : RelationCertificate Table 50 ![![131, 0, 0], ![64, 1, 0]]
  ![147, -1, 3] ![![50, 0, 0], ![-17, 1, 0]] where
    su := ![![6550, 0, 0], ![3200, 50, 0]]
    hsu := by decide
    w := ![![7350, -50, 150], ![-2500, 50, -50]]
    hw := by decide
    g := ![![![-114, 2615, -308], ![115, 7698, 0]], ![![-55, 1282, -151], ![59, 3774, 0]]]
    h := ![![![679, 77207, 2413], ![1082, -158050, 0]], ![![-299, -26270, -821], ![-229, 53775, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N2 : Ideal.span {50} * I131N2 =  Ideal.span {B.equivFun.symm ![147, -1, 3]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E131RS2 


noncomputable def E137RS1 : RelationCertificate Table 3125 ![![137, 0, 0], ![-37, 1, 0]]
  ![-504, 7, 29] ![![3125, 0, 0], ![-217, 1, 0]] where
    su := ![![428125, 0, 0], ![-115625, 3125, 0]]
    hsu := by decide
    w := ![![-1575000, 21875, 90625], ![109375, -3125, -6250]]
    hw := by decide
    g := ![![![91603, -20067180, 184951], ![-12561, -288985945, 0]], ![![-24031, 5268325, -48556], ![3556, 75868752, 0]]]
    h := ![![![5897, -251886, 13617], ![-3361, -932750, 0]], ![![-372, 17498, -946], ![373, 64800, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {3125} * I137N1 =  Ideal.span {B.equivFun.symm ![-504, 7, 29]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E137RS1 
