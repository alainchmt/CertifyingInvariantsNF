import IdealArithmetic.Examples.NF3_1_817452_1.PrimesBelow3_1_817452_1F0
import IdealArithmetic.Examples.NF3_1_817452_1.ClassGroupData3_1_817452_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 25 ![![3, 0, 0], ![0, 1, 0]]
  ![-21, 121, -21] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![75, 0, 0], ![0, 25, 0]]
    hsu := by decide
    w := ![![-525, 3025, -525], ![-3675, 100, 100]]
    hw := by decide
    g := ![![![707, -49, -152], ![28, 4368, 0]], ![![1315, -216, -407], ![69, 11232, 0]]]
    h := ![![![-7, 36, 0], ![13, -21, 0]], ![![-49, 2, 1], ![-2, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {25} * I3N0 =  Ideal.span {B.equivFun.symm ![-21, 121, -21]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 3125 ![![5, 0, 0], ![1, -1, 1]]
  ![6889, -2289, 189] ![![3125, 0, 0], ![1401, 1, 0]] where
    su := ![![15625, 0, 0], ![3125, -3125, 3125]]
    hsu := by decide
    w := ![![21528125, -7153125, 590625], ![9684375, -3200000, 262500]]
    hw := by decide
    g := ![![![-124845294820, 1045138330447192, 745994589264], ![278473623355, -2331233091449748, 0]], ![![-26009373953, 217736623169576, 155415161838], ![58015198890, -485672380742410, 0]]]
    h := ![![![1310, -390, -30], ![339, 0, 0]], ![![589, -174, -14], ![154, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3125} * I5N0 =  Ideal.span {B.equivFun.symm ![6889, -2289, 189]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![5, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 625 ![![7, 0, 0], ![1, 1, 0]]
  ![-1591, -184, 84] ![![625, 0, 0], ![151, 1, 0]] where
    su := ![![4375, 0, 0], ![625, 625, 0]]
    hsu := by decide
    w := ![![-994375, -115000, 52500], ![-225625, -29375, 12500]]
    hw := by decide
    g := ![![![-439024, 1201573766, 7957461], ![1817097, -4973413393, 0]], ![![-142652, 390395873, 2585409], ![590395, -1615880877, 0]]]
    h := ![![![-219, -219, -189], ![-58, 1407, 0]], ![![-50, -50, -42], ![-11, 314, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {625} * I7N0 =  Ideal.span {B.equivFun.symm ![-1591, -184, 84]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 26 ![![7, 0, 0], ![2, 1, 0]]
  ![22, 2, -1] ![![26, 0, 0], ![2, 1, 0]] where
    su := ![![182, 0, 0], ![52, 26, 0]]
    hsu := by decide
    w := ![![572, 52, -26], ![-130, 26, 0]]
    hw := by decide
    g := ![![![-11617, 3949517, 1977663], ![151037, -51419237, 0]], ![![-1651, 561572, 281199], ![21480, -7311173, 0]]]
    h := ![![![802, 440, 20], ![-2796, -141, 0]], ![![-177, -98, -5], ![617, 35, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {26} * I7N1 =  Ideal.span {B.equivFun.symm ![22, 2, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS1 


noncomputable def E7RS2 : RelationCertificate Table 650 ![![7, 0, 0], ![-3, 1, 0]]
  ![74, -24, -1] ![![650, 0, 0], ![-24, 1, 0]] where
    su := ![![4550, 0, 0], ![-1950, 650, 0]]
    hsu := by decide
    w := ![![48100, -15600, -650], ![-1950, 650, 0]]
    hw := by decide
    g := ![![![-1, -327264, 13636], ![-27, -8863401, 0]], ![![24, 187031, -7793], ![651, 5065450, 0]]]
    h := ![![![178340, -66779, 2444], ![416102, -17109, 0]], ![![-7233, 2711, -100], ![-16876, 700, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N2 : Ideal.span {650} * I7N2 =  Ideal.span {B.equivFun.symm ![74, -24, -1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E7RS2 


noncomputable def E11RS0 : RelationCertificate Table 5 ![![11, 0, 0], ![5, 4, 1]]
  ![12997, 2328, 417] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![55, 0, 0], ![25, 20, 5]]
    hsu := by decide
    w := ![![64985, 11640, 2085], ![85555, 15325, 2745]]
    hw := by decide
    g := ![![![23, 14, 17], ![12, -88, 0]], ![![-44, 9, 10], ![-7, -42, 0]]]
    h := ![![![972, 44, -4], ![461, 0, 0]], ![![1281, 59, -5], ![604, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {5} * I11N0 =  Ideal.span {B.equivFun.symm ![12997, 2328, 417]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 3125 ![![11, 0, 0], ![-4, 1, 0]]
  ![-44063, -7887, -1413] ![![3125, 0, 0], ![1401, 1, 0]] where
    su := ![![34375, 0, 0], ![-12500, 3125, 0]]
    hsu := by decide
    w := ![![-137696875, -24646875, -4415625], ![-61978125, -11093750, -1987500]]
    hw := by decide
    g := ![![![80, -10910996, -7788], ![-179, 24337518, 0]], ![![-445, 2909878, 2077], ![993, -6490628, 0]]]
    h := ![![![-72977, 18000, -497], ![-189671, 4054, 0]], ![![-32847, 8103, -224], ![-85371, 1828, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {3125} * I11N1 =  Ideal.span {B.equivFun.symm ![-44063, -7887, -1413]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 2 ![![13, 0, 0], ![2, 1, 0]]
  ![-20, -2, 1] ![![26, 0, 0], ![2, 1, 0]] where
    su := ![![26, 0, 0], ![4, 2, 0]]
    hsu := by decide
    w := ![![-520, -52, 26], ![134, -24, 0]]
    hw := by decide
    g := ![![![144, 10, 5], ![559, 26, 0]], ![![100, 14, 3], ![118, 13, 0]]]
    h := ![![![-696, -350, -4], ![4394, 65, 0]], ![![175, 86, 1], ![-1104, -13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {2} * I13N0 =  Ideal.span {B.equivFun.symm ![-20, -2, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 3250 ![![13, 0, 0], ![5, 1, 0]]
  ![-808, -142, -33] ![![3250, 0, 0], ![1276, 1, 0]] where
    su := ![![42250, 0, 0], ![16250, 3250, 0]]
    hsu := by decide
    w := ![![-2626000, -461500, -107250], ![-1036750, -182000, -42250]]
    hw := by decide
    g := ![![![-265, -1, 0], ![675, 2, 0]], ![![-499, 0, 0], ![1271, -1, 0]]]
    h := ![![![-7860786, -1908783, -67328], ![20437882, 875231, 0]], ![![-3103408, -753586, -26582], ![8068797, 345553, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {3250} * I13N1 =  Ideal.span {B.equivFun.symm ![-808, -142, -33]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 125 ![![13, 0, 0], ![6, 1, 0]]
  ![227, -52, 2] ![![125, 0, 0], ![26, 1, 0]] where
    su := ![![1625, 0, 0], ![750, 125, 0]]
    hsu := by decide
    w := ![![28375, -6500, 250], ![6250, -1125, 0]]
    hw := by decide
    g := ![![![-52289, 32774788, 1260646], ![251368, -157580768, 0]], ![![-27762, 17401047, 669312], ![133452, -83664016, 0]]]
    h := ![![![58817, 14745, 825], ![-127399, -10723, 0]], ![![13058, 3261, 181], ![-28284, -2353, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {125} * I13N2 =  Ideal.span {B.equivFun.symm ![227, -52, 2]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E13RS2 


noncomputable def E17RS1 : RelationCertificate Table 16250 ![![17, 0, 0], ![4, 1, 0]]
  ![100238, 17962, 3213] ![![16250, 0, 0], ![4526, 1, 0]] where
    su := ![![276250, 0, 0], ![65000, 16250, 0]]
    hsu := by decide
    w := ![![1628867500, 291882500, 52211250], ![454236250, 81396250, 14560000]]
    hw := by decide
    g := ![![![-898629801485, 56496370275648641, 12482627148519], ![3226410577581, -202842691163433715, 0]], ![![-158581729779, 9969947696408761, 2202816555777], ![569366572892, -35795769031376257, 0]]]
    h := ![![![4331528086, 1168049852, 21292251], ![-18408969306, -361965054, 0]], ![![1207917209, 325729739, 5937691], ![-5133641150, -100939851, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {16250} * I17N1 =  Ideal.span {B.equivFun.symm ![100238, 17962, 3213]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E17RS1 


noncomputable def E23RS1 : RelationCertificate Table 3250 ![![23, 0, 0], ![5, 1, 0]]
  ![-4305362, -771188, -138137] ![![3250, 0, 0], ![1276, 1, 0]] where
    su := ![![74750, 0, 0], ![16250, 3250, 0]]
    hsu := by decide
    w := ![![-13992426500, -2506361000, -448945250], ![-5517677750, -988341250, -177034000]]
    hw := by decide
    g := ![![![21514220419207, -205543017654830744, -161083882849142], ![-54797191506599, 523522619259711149, 0]], ![![3741603550706, -35746611766247776, -28014588321739], ![-9529946347803, 91047412045651740, 0]]]
    h := ![![![-52533669154, -11136941953, -126048412], ![241654017036, 2898975339, 0]], ![![-20715767734, -4391665509, -49705069], ![95292192027, 1143162115, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {3250} * I23N1 =  Ideal.span {B.equivFun.symm ![-4305362, -771188, -138137]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 625 ![![29, 0, 0], ![0, 1, 0]]
  ![-1363, 38, 37] ![![625, 0, 0], ![151, 1, 0]] where
    su := ![![18125, 0, 0], ![0, 625, 0]]
    hsu := by decide
    w := ![![-851875, 23750, 23125], ![-199375, 4375, 5625]]
    hw := by decide
    g := ![![![-100, 12966, 86], ![431, -53667, 0]], ![![-41, 1204, 8], ![173, -4984, 0]]]
    h := ![![![-47, 2, 1], ![-20, 8, 0]], ![![-11, 0, 0], ![7, 9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {625} * I29N0 =  Ideal.span {B.equivFun.symm ![-1363, 38, 37]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E29RS0 
