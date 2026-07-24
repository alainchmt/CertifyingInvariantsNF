import IdealArithmetic.Examples.NF3_1_116424_1.PrimesBelow3_1_116424_1F0
import IdealArithmetic.Examples.NF3_1_116424_1.ClassGroupData3_1_116424_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 16 ![![2, 0, 0], ![1, 1, 0]]
  ![3, 0, -1] ![![16, 0, 0], ![2, 1, 0]] where
    su := ![![32, 0, 0], ![16, 16, 0]]
    hsu := by decide
    w := ![![48, 0, -16], ![-48, 16, 0]]
    hw := by decide
    g := ![![![1325, -2652, -3314], ![13, 10605, 0]], ![![1642, -3283, -4103], ![11, 13130, 0]]]
    h := ![![![102, -132, -233], ![-15, 93, 0]], ![![-136, 176, 310], ![21, -124, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {16} * I2N1 =  Ideal.span {B.equivFun.symm ![3, 0, -1]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 200 ![![3, 0, 0], ![1, 1, 0]]
  ![-65, 16, 3] ![![200, 0, 0], ![-690, -115, -86]] where
    su := ![![600, 0, 0], ![200, 200, 0]]
    hsu := by decide
    w := ![![-13000, 3200, 600], ![-34600, 11000, 600]]
    hw := by decide
    g := ![![![77960603, -137626275, -14021621], ![-183799630, 32264129, 0]], ![![51877678, -91580218, -9330304], ![-122305171, 21469439, 0]]]
    h := ![![![-77, 85, 136], ![4, -81, 0]], ![![-213, 243, 381], ![10, -228, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {200} * I3N0 =  Ideal.span {B.equivFun.symm ![-65, 16, 3]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 16 ![![5, 0, 0], ![1, 1, 0]]
  ![13, 0, 1] ![![16, 0, 0], ![2, 1, 0]] where
    su := ![![80, 0, 0], ![16, 16, 0]]
    hsu := by decide
    w := ![![208, 0, 16], ![80, 0, 0]]
    hw := by decide
    g := ![![![0, 0, 0], ![1, 0, 0]], ![![-150, 36, 111], ![845, -355, 0]]]
    h := ![![![275, -76, -5], ![42, 0, -26]], ![![105, -30, -2], ![20, 0, -10]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {16} * I5N0 =  Ideal.span {B.equivFun.symm ![13, 0, 1]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 800 ![![5, 0, 0], ![8, 1, 1]]
  ![135, 16, 3] ![![800, 0, 0], ![810, 320, 107]] where
    su := ![![4000, 0, 0], ![6400, 800, 800]]
    hsu := by decide
    w := ![![108000, 12800, 2400], ![231200, 36800, 33600]]
    hw := by decide
    g := ![![![16765289668, -5840178860, 6687488131], ![15533236567, -5059196838, 0]], ![![-11506435430781399, 4008259875186455, -4589789427464004], ![-10660846259513325, 3472252591442373, 0]]]
    h := ![![![1571, -769, -162], ![2337, -508, 0]], ![![3293, -1608, -332], ![4894, -1064, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {800} * I5N1 =  Ideal.span {B.equivFun.symm ![135, 16, 3]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 1 ![![5, 0, 0], ![7, 1, 1]]
  ![1, 0, 0] ![![5, 0, 0], ![7, 1, 1]] where
    su := ![![5, 0, 0], ![7, 1, 1]]
    hsu := by decide
    w := ![![5, 0, 0], ![7, 1, 1]]
    hw := by decide
    g := ![![![161, -80, -17], ![220, -45, 0]], ![![218, -106, -22], ![291, -60, 0]]]
    h := ![![![161, -80, -17], ![220, -45, 0]], ![![218, -106, -22], ![291, -60, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {1} * I5N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 320 ![![7, 0, 0], ![0, 1, 0]]
  ![25, -16, -3] ![![320, 0, 0], ![-1082, -66, -133]] where
    su := ![![2240, 0, 0], ![0, 320, 0]]
    hsu := by decide
    w := ![![8000, -5120, -960], ![81280, -6080, -3840]]
    hw := by decide
    g := ![![![2761714899, -3567061997, -2832987420], ![-7424878732, 1264889015, 0]], ![![240966066, -311233703, -247184101], ![-647836275, 110364254, 0]]]
    h := ![![![-15975, 15656, 39946], ![2242, -55925, 0]], ![![-162306, 159092, 405854], ![22733, -568198, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {320} * I7N0 =  Ideal.span {B.equivFun.symm ![25, -16, -3]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 640 ![![11, 0, 0], ![1, 1, 0]]
  ![-235, -16, -23] ![![640, 0, 0], ![-1830, -200, -197]] where
    su := ![![7040, 0, 0], ![640, 640, 0]]
    hsu := by decide
    w := ![![-150400, -10240, -14720], ![670080, 54400, 39040]]
    hw := by decide
    g := ![![![-42932801853, 44026352760, 12048563516], ![105294051992, -21504698997, 0]], ![![-5945648202, 6097091875, 1668573397], ![14581891781, -2978128229, 0]]]
    h := ![![![281358, -419223, -700603], ![-12529, 1541322, 0]], ![![-1235920, 1841518, 3077531], ![55055, -6770556, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {640} * I11N0 =  Ideal.span {B.equivFun.symm ![-235, -16, -23]} * (J0 ^ 7*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 80 ![![11, 0, 0], ![-2, 1, 0]]
  ![-185, -16, -13] ![![80, 0, 0], ![-330, -60, -39]] where
    su := ![![880, 0, 0], ![-160, 80, 0]]
    hsu := by decide
    w := ![![-14800, -1280, -1040], ![115680, 8160, 7920]]
    hw := by decide
    g := ![![![-51456825, 113123287, -2358153], ![128566969, -23435874, 0]], ![![-3868843202092, 8505293295006, -177301078574], ![9666442514380, -1762051100661, 0]]]
    h := ![![![140647, 2304, -363188], ![-25360, 799011, 0]], ![![-1102892, -18071, 2847969], ![198883, -6265512, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {80} * I11N1 =  Ideal.span {B.equivFun.symm ![-185, -16, -13]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E11RS1 


noncomputable def E19RS0 : RelationCertificate Table 100 ![![19, 0, 0], ![0, 1, 0]]
  ![115, 4, 7] ![![100, 0, 0], ![-206, -33, -22]] where
    su := ![![1900, 0, 0], ![0, 100, 0]]
    hsu := by decide
    w := ![![11500, 400, 700], ![-34800, -3200, -2300]]
    hw := by decide
    g := ![![![28213063, -19037468, 3155887], ![-52530835, 12159232, 0]], ![![761476686360, -513825435999, 85178075258], ![-1417818756156, 328180331911, 0]]]
    h := ![![![-22885, 22828, 57228], ![1202, -217465, 0]], ![![69252, -69081, -173177], ![-3629, 658068, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {100} * I19N0 =  Ideal.span {B.equivFun.symm ![115, 4, 7]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E19RS0 


noncomputable def E29RS1 : RelationCertificate Table 20 ![![29, 0, 0], ![-5, 1, 0]]
  ![25, -8, 1] ![![20, 0, 0], ![42, 11, 4]] where
    su := ![![580, 0, 0], ![-100, 20, 0]]
    hsu := by decide
    w := ![![500, -160, 20], ![-60, 100, -300]]
    hw := by decide
    g := ![![![-1515, 1090, -1235], ![-2818, 765, 0]], ![![222, -169, 188], ![435, -117, 0]]]
    h := ![![![83, 120, -201], ![10, 1166, 0]], ![![-6, -16, 25], ![25, -148, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {20} * I29N1 =  Ideal.span {B.equivFun.symm ![25, -8, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 25 ![![31, 0, 0], ![-10, 1, 0]]
  ![-5, -3, 1] ![![25, 0, 0], ![2, 1, 1]] where
    su := ![![775, 0, 0], ![-250, 25, 0]]
    hsu := by decide
    w := ![![-125, -75, 25], ![-150, 25, -25]]
    hw := by decide
    g := ![![![-26994377, 4781288, -1485618], ![-2027715, 13056054, 0]], ![![8490812, -1503907, 467286], ![637807, -4106652, 0]]]
    h := ![![![-555, -2357, 1471], ![104, -9120, 0]], ![![-876, -3732, 2329], ![173, -14440, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {25} * I31N1 =  Ideal.span {B.equivFun.symm ![-5, -3, 1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E31RS1 
