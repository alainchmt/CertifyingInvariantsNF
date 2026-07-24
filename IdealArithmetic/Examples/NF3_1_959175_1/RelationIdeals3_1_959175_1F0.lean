import IdealArithmetic.Examples.NF3_1_959175_1.PrimesBelow3_1_959175_1F0
import IdealArithmetic.Examples.NF3_1_959175_1.ClassGroupData3_1_959175_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 4 ![![2, 0, 0], ![0, 1, 0]]
  ![-7145672, -2078643, -313212] ![![4, 0, 0], ![-69, -3, 2]] where
    su := ![![8, 0, 0], ![0, 4, 0]]
    hsu := by decide
    w := ![![-28582688, -8314572, -1252848], ![-232491912, -67630824, -10190680]]
    hw := by decide
    g := ![![![56, -18, 58], ![-473, 0, 0]], ![![-81, 718, -296], ![1444, 0, 0]]]
    h := ![![![-47422516, -7346267, 0], ![-3673133, 0, 313212]], ![![-385735289, -59754619, 0], ![-29877308, 0, 2547670]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {4} * I2N0 =  Ideal.span {B.equivFun.symm ![-7145672, -2078643, -313212]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![-35, -2, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![-35, -2, 1]] where
    su := ![![2, 0, 0], ![-35, -2, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![-35, -2, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, -3], ![17, 2, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, -3], ![17, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E2RS2 : RelationCertificate Table 1 ![![2, 0, 0], ![-35, -1, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![-35, -1, 1]] where
    su := ![![2, 0, 0], ![-35, -1, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![-35, -1, 1]]
    hw := by decide
    g := ![![![1, 8, 5], ![-16, -2, 0]], ![![0, -144, -90], ![289, 36, 0]]]
    h := ![![![1, 8, 5], ![-16, -2, 0]], ![![0, -144, -90], ![289, 36, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N2 : Ideal.span {1} * I2N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E2RS2 


noncomputable def E3RS0 : RelationCertificate Table 4 ![![3, 0, 0], ![1, 1, 0]]
  ![4212, -67, -49] ![![4, 0, 0], ![35, 3, -1]] where
    su := ![![12, 0, 0], ![4, 4, 0]]
    hsu := by decide
    w := ![![16848, -268, -196], ![111300, 11516, -3652]]
    hw := by decide
    g := ![![![-201, 24308, 8696], ![14455, 94, 0]], ![![-1152, 108212, 38413], ![61785, 141, 0]]]
    h := ![![![-3150, -4237, 323], ![13662, -509, 0]], ![![-16574, -22862, 1723], ![77547, -3041, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {4} * I3N0 =  Ideal.span {B.equivFun.symm ![4212, -67, -49]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 4 ![![5, 0, 0], ![0, 1, 0]]
  ![-260, -69, 16] ![![4, 0, 0], ![-69, -3, 2]] where
    su := ![![20, 0, 0], ![0, 4, 0]]
    hsu := by decide
    w := ![![-1040, -276, 64], ![-43100, -276, 672]]
    hw := by decide
    g := ![![![-45, 3636, 1072], ![-855, 0, 0]], ![![-133, 8924, 2632], ![-2100, 0, 0]]]
    h := ![![![-52, -69, -112], ![-12, 288, 0]], ![![-2155, -595, -1176], ![-118, 3024, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {4} * I5N0 =  Ideal.span {B.equivFun.symm ![-260, -69, 16]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 4 ![![7, 0, 0], ![0, 1, 0]]
  ![36092, 10499, 1582] ![![4, 0, 0], ![-69, -3, 2]] where
    su := ![![28, 0, 0], ![0, 4, 0]]
    hsu := by decide
    w := ![![144368, 41996, 6328], ![1174292, 341596, 51472]]
    hw := by decide
    g := ![![![61, 64, -14], ![15, 0, 0]], ![![16, -57, 8], ![16, 0, 0]]]
    h := ![![![5156, -4068, -11074], ![-575, 39550, 0]], ![![41939, -33083, -90076], ![-4720, 321700, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {4} * I7N0 =  Ideal.span {B.equivFun.symm ![36092, 10499, 1582]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E7RS0 


noncomputable def E17RS0 : RelationCertificate Table 4 ![![17, 0, 0], ![3, 1, 0]]
  ![-54568188, -15873634, -2391855] ![![4, 0, 0], ![-33, -2, 1]] where
    su := ![![68, 0, 0], ![12, 4, 0]]
    hsu := by decide
    w := ![![-218272752, -63494536, -9567420], ![-634709116, -184633952, -27820828]]
    hw := by decide
    g := ![![![-8949, -1374, -7012], ![72965, 8370, 0]], ![![-6965902548605, -473189983869, -5655530286098], ![56291408446663, 6733857460597, 0]]]
    h := ![![![33364962, 10312616, -613327], ![-207257514, 4017352, 0]], ![![97021027, 29987770, -1783473], ![-602678246, 11681917, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {4} * I17N0 =  Ideal.span {B.equivFun.symm ![-54568188, -15873634, -2391855]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 4 ![![17, 0, 0], ![4, 1, 0]]
  ![2597188, 755510, 113841] ![![4, 0, 0], ![-33, -2, 1]] where
    su := ![![68, 0, 0], ![16, 4, 0]]
    hsu := by decide
    w := ![![10388752, 3022040, 455364], ![30209156, 8787704, 1324140]]
    hw := by decide
    g := ![![![6046, 492, 4941], ![-48799, -5940, 0]], ![![251108579659, 17057669602, 203871955902], ![-2029206627792, -242743760827, 0]]]
    h := ![![![37469564, 10138615, 312687], ![-158596350, -2600919, 0]], ![![108956681, 29481794, 909255], ![-461177822, -7563150, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {4} * I17N1 =  Ideal.span {B.equivFun.symm ![2597188, 755510, 113841]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 4 ![![17, 0, 0], ![-7, 1, 0]]
  ![589892, -74426, 4677] ![![4, 0, 0], ![-33, -2, 1]] where
    su := ![![68, 0, 0], ![-28, 4, 0]]
    hsu := by decide
    w := ![![2359568, -297704, 18708], ![-44234396, -2398256, 1064916]]
    hw := by decide
    g := ![![![-32858389, -2588942661, -831798549], ![1357603405, -5670, 0]], ![![180822645236, 11480836261, 146557940271], ![-1460887756199, -174809014927, 0]]]
    h := ![![![1551770, -239594, 6439], ![3684314, -52393, 0]], ![![-29008128, 4376155, -104451], ![-68868511, 1020948, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {4} * I17N2 =  Ideal.span {B.equivFun.symm ![589892, -74426, 4677]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E17RS2 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![1, 1, 0]]
  ![-28769960001306, -8369048560822, -1261056582575] ![![2, 0, 0], ![-35, -2, 1]] where
    su := ![![38, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![-57539920002612, -16738097121644, -2522113165150], ![-277097467621450, -80606374235468, -12145848848696]]
    hw := by decide
    g := ![![![-58249, -1212537, 58520], ![2261651, 0, 0]], ![![56694, -75922, 73844], ![-879081, 3, 0]]]
    h := ![![![-2674526202224, -1611713921222, -77291299159], ![22046037840950, 103739050723, 0]], ![![-12879830866804, -7761600052279, -372215033756], ![106168052658551, 499580608508, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![-28769960001306, -8369048560822, -1261056582575]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 4 ![![23, 0, 0], ![11, 1, 0]]
  ![12, -1, 0] ![![4, 0, 0], ![-69, -3, 2]] where
    su := ![![92, 0, 0], ![44, 4, 0]]
    hsu := by decide
    w := ![![48, -4, 0], ![-1388, -68, 32]]
    hw := by decide
    g := ![![![42, -1, -2], ![3, 0, 0]], ![![41, -1, -2], ![3, 0, 0]]]
    h := ![![![-10, 263, 44], ![22, -506, 0]], ![![115, -7575, -1264], ![-272, 14540, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {4} * I23N1 =  Ideal.span {B.equivFun.symm ![12, -1, 0]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E23RS1 


noncomputable def E31RS1 : RelationCertificate Table 4 ![![31, 0, 0], ![-15, 1, 0]]
  ![-44, -2, 1] ![![4, 0, 0], ![-33, -2, 1]] where
    su := ![![124, 0, 0], ![-60, 4, 0]]
    hsu := by decide
    w := ![![-176, -8, 4], ![52, 64, -12]]
    hw := by decide
    g := ![![![-25017, -1698, -20330], ![202351, 24206, 0]], ![![-4836822, -328563, -3926971], ![39086469, 4675717, 0]]]
    h := ![![![-2684, 214, -5], ![-5544, 78, 0]], ![![13, 510, -73], ![26, 1130, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {4} * I31N1 =  Ideal.span {B.equivFun.symm ![-44, -2, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E31RS1 
