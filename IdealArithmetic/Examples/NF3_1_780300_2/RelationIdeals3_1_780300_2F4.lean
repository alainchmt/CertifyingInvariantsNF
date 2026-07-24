import IdealArithmetic.Examples.NF3_1_780300_2.PrimesBelow3_1_780300_2F4
import IdealArithmetic.Examples.NF3_1_780300_2.ClassGroupData3_1_780300_2

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 2783 ![![197, 0, 0], ![63, 1, 0]]
  ![1077, 45, -35] ![![2783, 0, 0], ![-395, 1, 0]] where
    su := ![![548251, 0, 0], ![175329, 2783, 0]]
    hsu := by decide
    w := ![![2997291, 125235, -97405], ![-431365, -16698, 13915]]
    hw := by decide
    g := ![![![-4755418599, -95121789169742, 481629373209], ![-33504632814, -670187272820316, 0]], ![![-1524879386, -30501895904718, 154439998811], ![-10743643877, -214903258345504, 0]]]
    h := ![![![93186561, 1757145, 8825], ![-291392880, -869280, 0]], ![![-13411105, -252912, -1271], ![41936310, 125196, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {2783} * I197N1 =  Ideal.span {B.equivFun.symm ![1077, 45, -35]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E197RS1 


noncomputable def E211RS0 : RelationCertificate Table 64009 ![![211, 0, 0], ![52, 1, 0]]
  ![-22851, 1929, 355] ![![64009, 0, 0], ![-5961, 1, 0]] where
    su := ![![13505899, 0, 0], ![3328468, 64009, 0]]
    hsu := by decide
    w := ![![-1462669659, 123473361, 22723195], ![136275161, -11521620, -2112297]]
    hw := by decide
    g := ![![![529228090266, 366907113379555787, -123102537650843], ![5682831878853, 3939835166246404672, 0]], ![![133291714416, 92409451537824233, -31004680946212], ![1431281554782, 992289311343041920, 0]]]
    h := ![![![-329653, -6762, -15], ![1337191, 1760, 0]], ![![30679, 619, 1], ![-124445, -122, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N0 : Ideal.span {64009} * I211N0 =  Ideal.span {B.equivFun.symm ![-22851, 1929, 355]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E211RS0 


noncomputable def E211RS1 : RelationCertificate Table 121 ![![211, 0, 0], ![64, 1, 0]]
  ![131, 23, 9] ![![121, 0, 0], ![-32, 1, 0]] where
    su := ![![25531, 0, 0], ![7744, 121, 0]]
    hsu := by decide
    w := ![![15851, 2783, 1089], ![-2662, -605, -242]]
    hw := by decide
    g := ![![![67, 27278, -1705], ![258, 103152, 0]], ![![34, 8511, -532], ![130, 32186, 0]]]
    h := ![![![686609, 12039, 41], ![-2263662, -4321, 0]], ![![-115410, -2059, -8], ![380492, 843, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {121} * I211N1 =  Ideal.span {B.equivFun.symm ![131, 23, 9]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E211RS1 


noncomputable def E211RS2 : RelationCertificate Table 2783 ![![211, 0, 0], ![95, 1, 0]]
  ![-2301, 431, -26] ![![2783, 0, 0], ![-395, 1, 0]] where
    su := ![![587213, 0, 0], ![264385, 2783, 0]]
    hsu := by decide
    w := ![![-6403683, 1199473, -72358], ![904475, -172546, 11132]]
    hw := by decide
    g := ![![![-5287867336, -105772265067101, 535555840274], ![-37256037465, -745225951741215, 0]], ![![-2400253090, -48011838345306, 243097946440], ![-16911150255, -338270792471233, 0]]]
    h := ![![![-19381, -291, -2], ![43022, 198, 0]], ![![2585, 26, 0], ![-5738, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N2 : Ideal.span {2783} * I211N2 =  Ideal.span {B.equivFun.symm ![-2301, 431, -26]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E211RS2 


noncomputable def E227RS1 : RelationCertificate Table 64009 ![![227, 0, 0], ![66, 1, 0]]
  ![453963, 65116, 18620] ![![64009, 0, 0], ![-5961, 1, 0]] where
    su := ![![14530043, 0, 0], ![4224594, 64009, 0]]
    hsu := by decide
    w := ![![29057717667, 4168010044, 1191847580], ![-2702908043, -387702513, -110863588]]
    hw := by decide
    g := ![![![691683662804, 479535497908743191, -160890957230256], ![7427273875595, 5149234640675728366, 0]], ![![207457888535, 143827918099475910, -48256305362952], ![2227675220137, 1544418924988597340, 0]]]
    h := ![![![9050865, 150722, 486], ![-31122612, -45851, 0]], ![![-841957, -14047, -46], ![2895182, 4355, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {64009} * I227N1 =  Ideal.span {B.equivFun.symm ![453963, 65116, 18620]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E227RS1 


noncomputable def E233RS1 : RelationCertificate Table 11 ![![233, 0, 0], ![102, 1, 0]]
  ![337, 48, 14] ![![11, 0, 0], ![1, 1, 0]] where
    su := ![![2563, 0, 0], ![1122, 11, 0]]
    hsu := by decide
    w := ![![3707, 528, 154], ![2717, 385, 110]]
    hw := by decide
    g := ![![![-8757, 1067598, 2152690], ![96266, -11839800, 0]], ![![-3962, 482961, 973836], ![43548, -5356100, 0]]]
    h := ![![![2129, 18, 0], ![-4860, 7, 0]], ![![1535, 13, 0], ![-3504, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N1 : Ideal.span {11} * I233N1 =  Ideal.span {B.equivFun.symm ![337, 48, 14]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E233RS1 


noncomputable def E239RS1 : RelationCertificate Table 121 ![![239, 0, 0], ![-67, 1, 0]]
  ![149, 16, 1] ![![121, 0, 0], ![-32, 1, 0]] where
    su := ![![28919, 0, 0], ![-8107, 121, 0]]
    hsu := by decide
    w := ![![18029, 1936, 121], ![-4598, -363, 0]]
    hw := by decide
    g := ![![![42101897, 20610178892, -1288218411], ![159197793, 77937213867, 0]], ![![-11670467, -5713071634, 357089771], ![-44128952, -21603931146, 0]]]
    h := ![![![1483361, -23446, 39], ![5291390, -4660, 0]], ![![-378216, 5980, -10], ![-1349158, 1195, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N1 : Ideal.span {121} * I239N1 =  Ideal.span {B.equivFun.symm ![149, 16, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E239RS1 
