import IdealArithmetic.Examples.NF3_1_193320_1.PrimesBelow3_1_193320_1F1
import IdealArithmetic.Examples.NF3_1_193320_1.ClassGroupData3_1_193320_1

set_option linter.all false

noncomputable section


noncomputable def E41RS0 : RelationCertificate Table 8 ![![41, 0, 0], ![12, 1, 0]]
  ![1364267, 572502, 64801] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![328, 0, 0], ![96, 8, 0]]
    hsu := by decide
    w := ![![10914136, 4580016, 518408], ![14781520, 6202928, 702104]]
    hw := by decide
    g := ![![![-5731, 104114, 53203], ![11585, -424764, 0]], ![![-20495897224, 696860494647, 353554221612], ![81983587528, -2828433772767, 0]]]
    h := ![![![85722055, 7969669, 69495], ![-292769999, -2784494, 0]], ![![116097346, 10793688, 94120], ![-396511958, -3771157, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {8} * I41N0 =  Ideal.span {B.equivFun.symm ![1364267, 572502, 64801]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 8 ![![41, 0, 0], ![14, 1, 0]]
  ![-11, -6, -1] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![328, 0, 0], ![112, 8, 0]]
    hsu := by decide
    w := ![![-88, -48, -8], ![-208, -80, -8]]
    hw := by decide
    g := ![![![-21, -58, -28], ![-7, 228, 0]], ![![136, -4810, -2440], ![-566, 19521, 0]]]
    h := ![![![-17, -15, -1], ![49, 40, 0]], ![![-30, -16, -1], ![86, 40, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {8} * I41N1 =  Ideal.span {B.equivFun.symm ![-11, -6, -1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 16 ![![41, 0, 0], ![15, 1, 0]]
  ![-14675, -6158, -697] ![![16, 0, 0], ![2, 1, 0]] where
    su := ![![656, 0, 0], ![240, 16, 0]]
    hsu := by decide
    w := ![![-234800, -98528, -11152], ![-158992, -66720, -7552]]
    hw := by decide
    g := ![![![232, -12682, -6386], ![-757, 102090, 0]], ![![60, -4613, -2320], ![-273, 37101, 0]]]
    h := ![![![-49510, -3877, -47], ![134349, 1230, 0]], ![![-33542, -2629, -32], ![91019, 840, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {16} * I41N2 =  Ideal.span {B.equivFun.symm ![-14675, -6158, -697]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E41RS2 


noncomputable def E43RS1 : RelationCertificate Table 8 ![![43, 0, 0], ![-19, 1, 0]]
  ![-46191745, -19383938, -2194051] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![344, 0, 0], ![-152, 8, 0]]
    hsu := by decide
    w := ![![-369533960, -155071504, -17552408], ![-500476976, -210020528, -23772040]]
    hw := by decide
    g := ![![![-1509, 2176, -240], ![-97, 96, 0]], ![![220174653, -7485948089, -3798016981], ![-880699847, 30384137061, 0]]]
    h := ![![![-7846494978, 471296202, -3147346], ![-17755425911, 133141827, 0]], ![![-10626871964, 638298306, -4262597], ![-24046996570, 180320166, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {8} * I43N1 =  Ideal.span {B.equivFun.symm ![-46191745, -19383938, -2194051]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 4 ![![47, 0, 0], ![-20, 1, 0]]
  ![-22225, -2370, 553] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![188, 0, 0], ![-80, 4, 0]]
    hsu := by decide
    w := ![![-88900, -9480, 2212], ![58408, 4556, -1264]]
    hw := by decide
    g := ![![![487183, 141043, 3666], ![278856, 104389, 0]], ![![-116628, -24573, 3819], ![-64457, -43558, 0]]]
    h := ![![![-1892955, 107709, -645], ![-4447333, 30868, 0]], ![![1244206, -70785, 424], ![2923154, -20244, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {4} * I47N1 =  Ideal.span {B.equivFun.symm ![-22225, -2370, 553]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E47RS1 


noncomputable def E59RS1 : RelationCertificate Table 16 ![![59, 0, 0], ![17, 1, 0]]
  ![144631, 13270, -3355] ![![16, 0, 0], ![2, 1, 0]] where
    su := ![![944, 0, 0], ![272, 16, 0]]
    hsu := by decide
    w := ![![2314096, 212320, -53680], ![-334768, -20064, 6560]]
    hw := by decide
    g := ![![![-1198205086, 155558903352, 78078860636], ![9572655825, -1249263003706, 0]], ![![-335343292, 43503655340, 21835601178], ![2677060557, -349370158983, 0]]]
    h := ![![![275614, 17583, 19], ![-948035, -4476, 0]], ![![-39890, -2550, -5], ![137211, 705, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {16} * I59N1 =  Ideal.span {B.equivFun.symm ![144631, 13270, -3355]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 8 ![![61, 0, 0], ![-10, 1, 0]]
  ![-6017, -706, 157] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![488, 0, 0], ![-80, 8, 0]]
    hsu := by decide
    w := ![![-48136, -5648, 1256], ![17168, 1520, -392]]
    hw := by decide
    g := ![![![11659, 4779, 574], ![3513, 172, 0]], ![![2654, -97947, -49658], ![-11574, 397173, 0]]]
    h := ![![![-490157, 50240, -122], ![-2989356, 7599, 0]], ![![174866, -17918, 43], ![1066468, -2672, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {8} * I61N1 =  Ideal.span {B.equivFun.symm ![-6017, -706, 157]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 8 ![![67, 0, 0], ![9, 1, 0]]
  ![70465, 29570, 3347] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![536, 0, 0], ![72, 8, 0]]
    hsu := by decide
    w := ![![563720, 236560, 26776], ![763472, 320384, 36264]]
    hw := by decide
    g := ![![![-36960681281, 1256663124135, 637571732115], ![147842720205, -5100573856766, 0]], ![![-4689041631, 159427411842, 80885966306], ![18756166077, -647087730431, 0]]]
    h := ![![![134830, 15576, 80], ![-995905, -2013, 0]], ![![182614, 21093, 108], ![-1348856, -2703, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {8} * I67N1 =  Ideal.span {B.equivFun.symm ![70465, 29570, 3347]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 4 ![![71, 0, 0], ![-20, 1, 0]]
  ![149, 62, 7] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![284, 0, 0], ![-80, 4, 0]]
    hsu := by decide
    w := ![![596, 248, 28], ![1600, 672, 76]]
    hw := by decide
    g := ![![![-77, 1004, 533], ![213, -2130, 0]], ![![22, -290, -154], ![-58, 615, 0]]]
    h := ![![![1739, -84, 0], ![6166, 7, 0]], ![![4640, -224, 0], ![16452, 19, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {4} * I71N1 =  Ideal.span {B.equivFun.symm ![149, 62, 7]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS1 


noncomputable def E73RS0 : RelationCertificate Table 4 ![![73, 0, 0], ![29, 1, 0]]
  ![187, -30, 1] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![292, 0, 0], ![116, 4, 0]]
    hsu := by decide
    w := ![![748, -120, 4], ![560, 184, -28]]
    hw := by decide
    g := ![![![3329, -26389, -13951], ![-4931, 55968, 0]], ![![377851, -3774931, -1981889], ![-754807, 7927641, 0]]]
    h := ![![![7624, 349, 3], ![-19185, -218, 0]], ![![5790, 261, 2], ![-14570, -153, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N0 : Ideal.span {4} * I73N0 =  Ideal.span {B.equivFun.symm ![187, -30, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E73RS0 


noncomputable def E73RS2 : RelationCertificate Table 8 ![![73, 0, 0], ![-2, 1, 0]]
  ![2803, 310, -71] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![584, 0, 0], ![-16, 8, 0]]
    hsu := by decide
    w := ![![22424, 2480, -568], ![-7600, -624, 168]]
    hw := by decide
    g := ![![![2377, 992, 126], ![723, -36, 0]], ![![-42, 9035, 4549], ![1126, -36301, 0]]]
    h := ![![![43255, -21618, 6], ![1577406, -509, 0]], ![![-14658, 7328, -3], ![-534542, 240, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N2 : Ideal.span {8} * I73N2 =  Ideal.span {B.equivFun.symm ![2803, 310, -71]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E73RS2 
