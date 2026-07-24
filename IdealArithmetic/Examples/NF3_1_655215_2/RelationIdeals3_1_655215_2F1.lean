import IdealArithmetic.Examples.NF3_1_655215_2.PrimesBelow3_1_655215_2F1
import IdealArithmetic.Examples.NF3_1_655215_2.ClassGroupData3_1_655215_2

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 4 ![![37, 0, 0], ![5, 1, 0]]
  ![4884230983654580459, 199420943819518822, 127411273218720933] ![![4, 0, 0], ![-24, 1, -1]] where
    su := ![![148, 0, 0], ![20, 4, 0]]
    hsu := by decide
    w := ![![19536923934618321836, 797683775278075288, 509645092874883732], ![-118218027686682421716, -4826788646289682312, -3083865090609612552]]
    hw := by decide
    g := ![![![-29364946, 235397170, 147450749], ![198176341, 0, 0]], ![![270394, -72979211, 22273974], ![-25435531, 7, 0]]]
    h := ![![![-2032852661847823048, -377157598900069523, 20251690188638543], ![16019955894404806647, -310950631880452579, 0]], ![![12300801961737634738, 2282182579930392787, -122543081983359224], ![-96936835901192618147, 1881563880365944075, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {4} * I37N1 =  Ideal.span {B.equivFun.symm ![4884230983654580459, 199420943819518822, 127411273218720933]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 4 ![![41, 0, 0], ![12, 1, 0]]
  ![196157, 8009, 5117] ![![4, 0, 0], ![24, 1, 1]] where
    su := ![![164, 0, 0], ![48, 4, 0]]
    hsu := by decide
    w := ![![784628, 32036, 20468], ![5975868, 243992, 155888]]
    hw := by decide
    g := ![![![-8, -26, -44], ![31, 0, 0]], ![![-18, 31, -10], ![-6, 0, 0]]]
    h := ![![![8071417, 736493, 9983], ![-27560995, -202093, 0]], ![![61473435, 5609345, 76044], ![-209909739, -1539416, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {4} * I41N1 =  Ideal.span {B.equivFun.symm ![196157, 8009, 5117]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 2 ![![43, 0, 0], ![8, 1, 0]]
  ![-306586, 74359, 22138] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![86, 0, 0], ![16, 2, 0]]
    hsu := by decide
    w := ![![-613172, 148718, 44276], ![2349974, -932698, 170856]]
    hw := by decide
    g := ![![![-264191576221, 42397928561, -8338194247], ![-110896823829, 0, 13680]], ![![-68384718520, 10974486884, -2158302409], ![-28705115816, 0, 2736]]]
    h := ![![![-3020318, -395902, -4148], ![16195886, 100251, 0]], ![![11554097, 1510539, 19884], ![-61956398, -384792, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {2} * I43N1 =  Ideal.span {B.equivFun.symm ![-306586, 74359, 22138]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E43RS1 


noncomputable def E59RS1 : RelationCertificate Table 2 ![![59, 0, 0], ![-16, 1, 0]]
  ![5468858, 223291, 142662] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![118, 0, 0], ![-32, 2, 0]]
    hsu := by decide
    w := ![![10937716, 446582, 285324], ![22588298, 922270, 589244]]
    hw := by decide
    g := ![![![1092772, -507483, 10156], ![292647, 0, -20680]], ![![-273488, 126991, -2510], ![-73248, 0, 5170]]]
    h := ![![![347262, 60937854, -8124246], ![938725, 239736588, 0]], ![![717135, 125847336, -16777990], ![1938551, 495098016, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {2} * I59N1 =  Ideal.span {B.equivFun.symm ![5468858, 223291, 142662]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E59RS1 


noncomputable def E67RS1 : RelationCertificate Table 2 ![![67, 0, 0], ![-21, 1, 0]]
  ![-23924263103, 6326429557, 1235712595] ![![2, 0, 0], ![24, 1, 1]] where
    su := ![![134, 0, 0], ![-42, 2, 0]]
    hsu := by decide
    w := ![![-47848526206, 12652859114, 2471425190], ![259131988068, -56295743798, -24864242534]]
    hw := by decide
    g := ![![![-22464404053980031799, 1554805523713498092, 45423065135429718906], ![-246083913318188773055, 0, 0]], ![![5991508005988315581, -414684036162260181, -12114839893437477850], ![65633334107059918183, 0, 0]]]
    h := ![![![-506945640605, 24677176367, -27505247], ![-1616258745592, 1539282072, 0]], ![![2743525171788, -133468679323, 64105225], ![8746981929322, -8363585671, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {2} * I67N1 =  Ideal.span {B.equivFun.symm ![-23924263103, 6326429557, 1235712595]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 2 ![![71, 0, 0], ![-13, 1, 0]]
  ![-40450313, -1651568, -1055197] ![![2, 0, 0], ![24, 2, 1]] where
    su := ![![142, 0, 0], ![-26, 2, 0]]
    hsu := by decide
    w := ![![-80900626, -3303136, -2110394], ![-1358931132, -55484544, -35449418]]
    hw := by decide
    g := ![![![-421, 3824, 380], ![-763, 0, 0]], ![![71, -763, 18], ![125, 3, 0]]]
    h := ![![![-94274894, 7359327, -43945], ![-511774397, 1032449, 0]], ![![-1583586134, 123618452, -738147], ![-8596549996, 17341864, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {2} * I71N1 =  Ideal.span {B.equivFun.symm ![-40450313, -1651568, -1055197]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 2 ![![73, 0, 0], ![-20, 1, 0]]
  ![-356810611, -14568416, -9307851] ![![2, 0, 0], ![24, 2, 1]] where
    su := ![![146, 0, 0], ![-40, 2, 0]]
    hsu := by decide
    w := ![![-713621222, -29136832, -18615702], ![-11987077764, -489426968, -312697914]]
    hw := by decide
    g := ![![![827, -8946, 720], ![1475, 0, 0]], ![![-148, 1739, -497], ![-226, 3, 0]]]
    h := ![![![-6020181967, 303985712, -487565], ![-21955823649, 13142197, 0]], ![![-101124220354, 5106210740, -8189885], ![-368803727348, 220756324, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {2} * I73N1 =  Ideal.span {B.equivFun.symm ![-356810611, -14568416, -9307851]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E73RS1 
