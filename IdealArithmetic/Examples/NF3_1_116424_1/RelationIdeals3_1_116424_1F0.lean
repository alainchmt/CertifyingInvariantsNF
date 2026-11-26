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
  ![-65, 16, 3] ![![200, 0, 0], ![-214, 13, -36]] where
    su := ![![600, 0, 0], ![200, 200, 0]]
    hsu := by decide
    w := ![![-13000, 3200, 600], ![-11400, 1400, 5000]]
    hw := by decide
    g := ![![![-29859835, 6910745, 9867437], ![30623224, -6358039, 0]], ![![-43381254, 10040138, 14335713], ![44490359, -9237151, 0]]]
    h := ![![![-77, 85, 136], ![4, -81, 0]], ![![-63, 65, 115], ![4, -64, 0]]]
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
  ![135, 16, 3] ![![800, 0, 0], ![46, 128, -23]] where
    su := ![![4000, 0, 0], ![6400, 800, 800]]
    hsu := by decide
    w := ![![108000, 12800, 2400], ![5600, 20800, 8000]]
    hw := by decide
    g := ![![![-189042, 75969, 86569], ![-683, -100978, 0]], ![![27803875049, -11186970444, -12732192829], ![174858729, 14853900895, 0]]]
    h := ![![![1571, -769, -162], ![2337, -508, 0]], ![![-77, 41, 9], ![-107, 24, 0]]]
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
  ![25, -16, -3] ![![320, 0, 0], ![558, 179, 84]] where
    su := ![![2240, 0, 0], ![0, 320, 0]]
    hsu := by decide
    w := ![![8000, -5120, -960], ![-72320, 10240, -7360]]
    hw := by decide
    g := ![![![-10554833254512765, 9225551132377062, -2404460121977029], ![-13875618604901105, 2661594500473648, 0]], ![![31413194141928, -27456997358728, 7156131299953], ![41296483854352, -7921412186727, 0]]]
    h := ![![![-15975, 15656, 39946], ![2242, -55925, 0]], ![![144414, -141553, -361119], ![-20221, 505562, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {320} * I7N0 =  Ideal.span {B.equivFun.symm ![25, -16, -3]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 640 ![![11, 0, 0], ![1, 1, 0]]
  ![-235, -16, -23] ![![640, 0, 0], ![-2094, -387, -292]] where
    su := ![![7040, 0, 0], ![640, 640, 0]]
    hsu := by decide
    w := ![![-150400, -10240, -14720], ![957440, 67840, 46720]]
    hw := by decide
    g := ![![![-964407, 1693681, 239918], ![2024301, -323870, 0]], ![![-534787002863, 938472813459, 132897475576], ![1121638978101, -179470168199, 0]]]
    h := ![![![281358, -419223, -700603], ![-12529, 1541322, 0]], ![![-1785791, 2660819, 4446743], ![79557, -9782820, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {640} * I11N0 =  Ideal.span {B.equivFun.symm ![-235, -16, -23]} * (J0 ^ 7*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 80 ![![11, 0, 0], ![-2, 1, 0]]
  ![-185, -16, -13] ![![80, 0, 0], ![-234, 3, -32]] where
    su := ![![880, 0, 0], ![-160, 80, 0]]
    hsu := by decide
    w := ![![-14800, -1280, -1040], ![53120, 3600, 3200]]
    hw := by decide
    g := ![![![-46261659, 36321268, 61808593], ![111954394, -17242365, 0]], ![![-3398710, 2668500, 4541054], ![8225257, -1266786, 0]]]
    h := ![![![140647, 2304, -363188], ![-25360, 799011, 0]], ![![-506730, -8303, 1308515], ![91378, -2878725, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {80} * I11N1 =  Ideal.span {B.equivFun.symm ![-185, -16, -13]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E11RS1 


noncomputable def E19RS0 : RelationCertificate Table 100 ![![19, 0, 0], ![0, 1, 0]]
  ![115, 4, 7] ![![100, 0, 0], ![114, 37, 16]] where
    su := ![![1900, 0, 0], ![0, 100, 0]]
    hsu := by decide
    w := ![![11500, 400, 700], ![26000, 2600, 1500]]
    hw := by decide
    g := ![![![5912433368313925, -2557178120387580, 1511959165661274], ![6035931601840399, -1619417138533162, 0]], ![![-570057530, 246554740, -145778164], ![-581964754, 156138905, 0]]]
    h := ![![![-22885, 22828, 57228], ![1202, -217465, 0]], ![![-51740, 51612, 129385], ![2718, -491660, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {100} * I19N0 =  Ideal.span {B.equivFun.symm ![115, 4, 7]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E19RS0 


noncomputable def E29RS1 : RelationCertificate Table 20 ![![29, 0, 0], ![-5, 1, 0]]
  ![25, -8, 1] ![![20, 0, 0], ![-66, -8, -9]] where
    su := ![![580, 0, 0], ![-100, 20, 0]]
    hsu := by decide
    w := ![![500, -160, 20], ![2020, -520, 0]]
    hw := by decide
    g := ![![![-724, 1228, 504], ![1821, -286, 0]], ![![-96628, 154886, 63069], ![228713, -36229, 0]]]
    h := ![![![83, 120, -201], ![10, 1166, 0]], ![![323, 486, -810], ![-26, 4698, 0]]]
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
