import IdealArithmetic.Examples.NF3_1_237175_1.PrimesBelow3_1_237175_1F0
import IdealArithmetic.Examples.NF3_1_237175_1.ClassGroupData3_1_237175_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0], ![16, -1, 1]]
  ![-14980566, 521153, -615829] ![![2, 0, 0], ![17, -1, 1]] where
    su := ![![4, 0, 0], ![32, -2, 2]]
    hsu := by decide
    w := ![![-29961132, 1042306, -1231658], ![-269925508, 9390332, -11096240]]
    hw := by decide
    g := ![![![1, 113, 141], ![23, 0, 0]], ![![9, -176, -662], ![-55, 0, 0]]]
    h := ![![![1711855, 15247884, 54035], ![6097993, 3410946, 0]], ![![15422497, 137371068, 486816], ![54937964, 30729858, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![-14980566, 521153, -615829]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![17, 0, 1]]
  ![1, 0, 0] ![![4, 0, 0], ![34, 0, 2]] where
    su := ![![4, 0, 0], ![34, 0, 2]]
    hsu := by decide
    w := ![![4, 0, 0], ![34, 0, 2]]
    hw := by decide
    g := ![![![-16, 0, -1], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-16, 0, -1], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E2RS1 


noncomputable def E2RS2 : RelationCertificate Table 2 ![![2, 0, 0], ![1, 1, 0]]
  ![97442509, -3389889, 4005718] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![4, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![194885018, -6779778, 8011436], ![-134962754, 4695166, -5548120]]
    hw := by decide
    g := ![![![1071, 672, -254], ![337, 0, 0]], ![![5440, 2866, 1300], ![1435, 0, 0]]]
    h := ![![![-95310876, -97658459, 20028590], ![-96484667, 0, -12017154]], ![![66005167, 67630927, -13870300], ![66818049, 0, 8322180]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N2 : Ideal.span {2} * I2N2 =  Ideal.span {B.equivFun.symm ![97442509, -3389889, 4005718]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E2RS2 


noncomputable def E3RS0 : RelationCertificate Table 2 ![![3, 0, 0], ![16, -2, 1]]
  ![316, -11, 13] ![![2, 0, 0], ![17, -1, 1]] where
    su := ![![6, 0, 0], ![32, -4, 2]]
    hsu := by decide
    w := ![![632, -22, 26], ![5694, -198, 234]]
    hw := by decide
    g := ![![![-9, 0, 0], ![1, 0, 0]], ![![-9, 7, -2], ![2, 0, 0]]]
    h := ![![![4, 9, -2], ![19, 0, 0]], ![![37, 81, -18], ![171, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {2} * I3N0 =  Ideal.span {B.equivFun.symm ![316, -11, 13]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 2 ![![3, 0, 0], ![0, 1, 0]]
  ![137660, -4789, 5659] ![![2, 0, 0], ![17, -1, 1]] where
    su := ![![6, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![275320, -9578, 11318], ![2480410, -86290, 101966]]
    hw := by decide
    g := ![![![-16, 17, 15], ![5, 0, 0]], ![![-24, -145, 40], ![-18, 0, 0]]]
    h := ![![![-412980, 205053, -915847], ![68352, 688300, 0]], ![![-3720615, 1847364, -8251039], ![615788, 6201025, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {2} * I3N1 =  Ideal.span {B.equivFun.symm ![137660, -4789, 5659]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![13, -2, 1]]
  ![-361, -3501, 12240] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![26, -4, 2]]
    hsu := by decide
    w := ![![-722, -7002, 24480], ![-398682, -290620, 10476]]
    hw := by decide
    g := ![![![6117104774, -170244436, 251465166], ![-85122217, 0, 0]], ![![13460626616, -374621143, 553346531], ![-187310571, 0, 0]]]
    h := ![![![-176, -481, 1739], ![67, 0, 0]], ![![-9371, -23698, 2218], ![-10288, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![-361, -3501, 12240]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 2 ![![7, 0, 0], ![-1, 1, 0]]
  ![-1999339, 1213617, -10036936] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![-3998678, 2427234, -20073872], ![323609186, 237673508, -15219404]]
    hw := by decide
    g := ![![![28790173732775166, -801255995940250, 1183521630633610], ![-400627997970123, 0, 0]], ![![-9809429414700187, 273005095705045, -403251192723948], ![136502547852524, 0, 0]]]
    h := ![![![5233855, -5346101, 10036936], ![-1511420, -20073872, 0]], ![![27172460, 12919161, 7609702], ![-2036181, -15219404, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![-1999339, 1213617, -10036936]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 4 ![![11, 0, 0], ![0, 1, 0]]
  ![7343521842, -255470884, 301881365] ![![4, 0, 0], ![34, 0, 2]] where
    su := ![![44, 0, 0], ![0, 4, 0]]
    hsu := by decide
    w := ![![29374087368, -1021883536, 1207525460], ![244294420924, -8498662224, 10042583768]]
    hw := by decide
    g := ![![![137, -5606, -4693], ![-1157, 0, 0]], ![![400, 11105, -3802], ![1624, -7, 0]]]
    h := ![![![-51404652894, 25799677790, -104117047817], ![2345425264, 286397351838, 0]], ![![-427515236617, 214567256745, -865906524554], ![19506114258, 2381870604009, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {4} * I11N0 =  Ideal.span {B.equivFun.symm ![7343521842, -255470884, 301881365]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 4 ![![11, 0, 0], ![18, -6, 1]]
  ![-2186578, 76068, -89887] ![![4, 0, 0], ![34, 0, 2]] where
    su := ![![44, 0, 0], ![72, -24, 4]]
    hsu := by decide
    w := ![![-8746312, 304272, -359548], ![-72740140, 2530528, -2990240]]
    hw := by decide
    g := ![![![-520, -5549, 3030], ![-2897, -1566, 0]], ![![-868, -8912, 5099], ![-4770, -2610, 0]]]
    h := ![![![-63320, -38238, -646], ![-82781, 0, 0]], ![![-526493, -318052, -5366], ![-688534, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {4} * I11N1 =  Ideal.span {B.equivFun.symm ![-2186578, 76068, -89887]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E11RS1 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![1, 1, 0]]
  ![1, 1, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![38, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![2, 2, 0], ![2, 0, 4]]
    hw := by decide
    g := ![![![-48, 1, -2], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![-3, 0, -6], ![0, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![1, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E19RS1 


noncomputable def E31RS1 : RelationCertificate Table 2 ![![31, 0, 0], ![-14, 1, 0]]
  ![-24, 1, -1] ![![2, 0, 0], ![17, -1, 1]] where
    su := ![![62, 0, 0], ![-28, 2, 0]]
    hsu := by decide
    w := ![![-48, 2, -2], ![-438, 14, -18]]
    hw := by decide
    g := ![![![-12, -1, -1], ![1, 0, 0]], ![![-15, 2, -1], ![2, 0, 0]]]
    h := ![![![-56, 639, -171], ![67, 1325, 0]], ![![-571, 5830, -1559], ![477, 12080, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {2} * I31N1 =  Ideal.span {B.equivFun.symm ![-24, 1, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E31RS1 
