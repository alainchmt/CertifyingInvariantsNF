import IdealArithmetic.Examples.NF3_1_538412_3.PrimesBelow3_1_538412_3F2
import IdealArithmetic.Examples.NF3_1_538412_3.ClassGroupData3_1_538412_3

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 5 ![![89, 0, 0], ![13, 1, 0]]
  ![13, 1, 0] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![445, 0, 0], ![65, 5, 0]]
    hsu := by decide
    w := ![![65, 5, 0], ![-15, 10, 10]]
    hw := by decide
    g := ![![![5848760, 657776, 40922], ![-1038195, 0, -204608]], ![![953603, 107246, 6672], ![-169270, 0, -33360]]]
    h := ![![![6082, -33886, -30800], ![535, 274120, 0]], ![![-1428, 7941, 7218], ![-107, -64240, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {5} * I89N1 =  Ideal.span {B.equivFun.symm ![13, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E101RS0 : RelationCertificate Table 25 ![![101, 0, 0], ![40, 1, 0]]
  ![9831, -1393, 430] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![2525, 0, 0], ![1000, 25, 0]]
    hsu := by decide
    w := ![![245775, -34825, 10750], ![105750, 11775, -11350]]
    hw := by decide
    g := ![![![168277, 19137, 9950], ![27713, 18122, -13]], ![![90874, 10463, 5954], ![14966, 8364, -6]]]
    h := ![![![21553283, -440933015, -116024130], ![4170394, 1171843756, 0]], ![![9224998, -188723729, -49659494], ![1785028, 501560844, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {25} * I101N0 =  Ideal.span {B.equivFun.symm ![9831, -1393, 430]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 25 ![![101, 0, 0], ![-35, 1, 0]]
  ![-11841, -1652, 1470] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![2525, 0, 0], ![-875, 25, 0]]
    hsu := by decide
    w := ![![-296025, -41300, 36750], ![173500, 1025, -7700]]
    hw := by decide
    g := ![![![43844337997, -44888053000, -223396445246], ![5219571977, 558491157795, 291]], ![![-14765418659, 15116936566, 75233143952], ![-1757789521, -188082868875, -98]]]
    h := ![![![-700048, -13639709, 3686130], ![107615, -37229766, 0]], ![![411076, 8008479, -2164288], ![-63052, 21859278, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {25} * I101N1 =  Ideal.span {B.equivFun.symm ![-11841, -1652, 1470]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS1 


noncomputable def E101RS2 : RelationCertificate Table 25 ![![101, 0, 0], ![-5, 1, 0]]
  ![-2800314, -354808, -281295] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![2525, 0, 0], ![-125, 25, 0]]
    hsu := by decide
    w := ![![-70007850, -8870200, -7032375], ![-52123300, -6604175, -5235850]]
    hw := by decide
    g := ![![![1147327242, -1174645820, -5845911513], ![136586531, 14614778303, 398]], ![![-40358404, 41319198, 205635085], ![-4804552, -514087677, -14]]]
    h := ![![![53931202, 188998996, -269995075], ![-798508, 2726922128, 0]], ![![40153672, 140716382, -201020804], ![-594510, 2030289177, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {25} * I101N2 =  Ideal.span {B.equivFun.symm ![-2800314, -354808, -281295]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS2 


noncomputable def E109RS0 : RelationCertificate Table 25 ![![109, 0, 0], ![21, 1, 0]]
  ![4258, -149, -85] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![2725, 0, 0], ![525, 25, 0]]
    hsu := by decide
    w := ![![106450, -3725, -2125], ![4750, 3025, -2000]]
    hw := by decide
    g := ![![![18170349876, -18602983798, -92582287985], ![2163136652, 231455718060, -530]], ![![3771214360, -3861007715, -19215246451], ![448953998, 48038115468, -110]]]
    h := ![![![-85717, 830999, 437325], ![-8871, -4766851, 0]], ![![-3727, 36125, 19010], ![-381, -207217, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {25} * I109N0 =  Ideal.span {B.equivFun.symm ![4258, -149, -85]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 25 ![![109, 0, 0], ![35, 1, 0]]
  ![26560798, 3365331, 2668065] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![2725, 0, 0], ![875, 25, 0]]
    hsu := by decide
    w := ![![664019950, 84133275, 66701625], ![494386150, 62640175, 49661700]]
    hw := by decide
    g := ![![![-12591280719271076, 12891073117516393, 64155573189451469], ![-1498961990382695, -160388932973612408, -27032]], ![![-3985313622154224, 4080202041782293, 20306121789319889], ![-474442097873372, -50765304473294528, -8556]]]
    h := ![![![712090786, -12357294528, -3744299085], ![115283394, 40813126833, 0]], ![![530176587, -9200439333, -2787762038], ![85832491, 30386804861, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {25} * I109N1 =  Ideal.span {B.equivFun.symm ![26560798, 3365331, 2668065]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 25 ![![109, 0, 0], ![53, 1, 0]]
  ![-7712797, -977234, -774760] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![2725, 0, 0], ![1325, 25, 0]]
    hsu := by decide
    w := ![![-192819925, -24430850, -19369000], ![-143561200, -18189625, -14420900]]
    hw := by decide
    g := ![![![8562279155027660411, -8766142944465915863, -43626850932914220612], ![1019318947025789043, 109067127332282429436, 5203986]], ![![4258725234176071171, -4360123454053737545, -21699219050402409704], ![506991099306021892, 54248047626004471344, 2588370]]]
    h := ![![![-174141653, 4928421684, 966280860], ![-39459440, -10532538850, 0]], ![![-129654604, 3669382876, 719430006], ![-29378870, -7841844749, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {25} * I109N2 =  Ideal.span {B.equivFun.symm ![-7712797, -977234, -774760]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E109RS2 
