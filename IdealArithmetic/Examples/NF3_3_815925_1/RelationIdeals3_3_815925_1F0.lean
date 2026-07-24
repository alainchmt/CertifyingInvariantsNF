import IdealArithmetic.Examples.NF3_3_815925_1.PrimesBelow3_3_815925_1F0
import IdealArithmetic.Examples.NF3_3_815925_1.ClassGroupData3_3_815925_1

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

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![1, 1, 0]]
  ![-1, 5, 2] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![4, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![-2, 10, 4], ![-14, 66, 24]]
    hw := by decide
    g := ![![![-219, -2, 6], ![-1, 0, 0]], ![![-148, -2, 4], ![1, 0, 0]]]
    h := ![![![-49, 98, 10], ![25, 0, -6]], ![![-294, 590, 60], ![149, 0, -36]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![-1, 5, 2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E3RS1 : RelationCertificate Table 2 ![![3, 0, 0], ![-1, 1, 0]]
  ![-5, 11, -3] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![6, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![-10, 22, -6], ![58, -124, 38]]
    hw := by decide
    g := ![![![841, 7, -23], ![5, 0, 0]], ![![-182, -2, 5], ![0, 0, 0]]]
    h := ![![![-9, 11, -21], ![8, 15, 0]], ![![59, -70, 133], ![-42, -95, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {2} * I3N1 =  Ideal.span {B.equivFun.symm ![-5, 11, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![-21, -1, 1]]
  ![0, 10, -3] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![-42, -2, 2]]
    hsu := by decide
    w := ![![0, 20, -6], ![56, -118, 34]]
    hw := by decide
    g := ![![![0, -270062, -292570], ![-135029, 135032, 22505]], ![![0, 539792, 584786], ![269896, -269902, -44983]]]
    h := ![![![12, 2, -1], ![4, 0, 0]], ![![13, -8, 2], ![3, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![0, 10, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 2 ![![7, 0, 0], ![2, 1, 0]]
  ![75, -365, -139] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![4, 2, 0]]
    hsu := by decide
    w := ![![150, -730, -278], ![938, -4564, -1738]]
    hw := by decide
    g := ![![![-511, -2, 13], ![-1, 0, 0]], ![![-169, -6, 6], ![-1, 0, 0]]]
    h := ![![![83, -16, 139], ![25, -278, 0]], ![![523, -98, 869], ![142, -1738, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![75, -365, -139]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 2 ![![11, 0, 0], ![1, 1, 0]]
  ![13, -63, -24] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![22, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![26, -126, -48], ![162, -788, -300]]
    hw := by decide
    g := ![![![194, 3, -6], ![3, 0, 0]], ![![25, -2, 0], ![0, 0, 0]]]
    h := ![![![-232, -4, -472], ![-19, 1292, 0]], ![![-1449, -24, -2950], ![-130, 8075, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {2} * I11N0 =  Ideal.span {B.equivFun.symm ![13, -63, -24]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS0 


noncomputable def E13RS0 : RelationCertificate Table 2 ![![13, 0, 0], ![0, 1, 0]]
  ![7, -33, -12] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![26, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![14, -66, -24], ![78, -392, -156]]
    hw := by decide
    g := ![![![8116, 73, -222], ![37, 0, 0]], ![![219, 2, -6], ![1, 0, 0]]]
    h := ![![![-21, 8, -44], ![3, 140, 0]], ![![-117, 44, -246], ![12, 780, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {2} * I13N0 =  Ideal.span {B.equivFun.symm ![7, -33, -12]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 2 ![![13, 0, 0], ![-30, 6, 1]]
  ![73, 1, -2] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![26, 0, 0], ![-60, 12, 2]]
    hsu := by decide
    w := ![![146, 2, -4], ![26, 0, 0]]
    hw := by decide
    g := ![![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0]]]
    h := ![![![31, -5, -1], ![11, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {2} * I13N1 =  Ideal.span {B.equivFun.symm ![73, 1, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 2 ![![17, 0, 0], ![-3, 1, 0]]
  ![137, -667, -254] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![34, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![274, -1334, -508], ![1714, -8340, -3176]]
    hw := by decide
    g := ![![![-186, -31, 16], ![-15, 0, 0]], ![![17, 26, -10], ![12, 0, 0]]]
    h := ![![![7784, -16272, 16354], ![-2315, -69568, 0]], ![![48669, -101766, 102284], ![-14564, -435104, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {2} * I17N1 =  Ideal.span {B.equivFun.symm ![137, -667, -254]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![-8, 1, 0]]
  ![313, -1523, -580] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![38, 0, 0], ![-16, 2, 0]]
    hsu := by decide
    w := ![![626, -3046, -1160], ![3914, -19044, -7252]]
    hw := by decide
    g := ![![![13218, 120, -362], ![61, 0, 0]], ![![-5321, -50, 146], ![-23, 0, 0]]]
    h := ![![![9887, -57757, 25772], ![-7198, -122562, 0]], ![![61813, -361113, 161134], ![-45012, -766293, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![313, -1523, -580]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E29RS1 : RelationCertificate Table 2 ![![29, 0, 0], ![7, 1, 0]]
  ![-196, 426, -123] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![58, 0, 0], ![14, 2, 0]]
    hsu := by decide
    w := ![![-392, 852, -246], ![2328, -5050, 1458]]
    hw := by decide
    g := ![![![64, 49, 21], ![25, 0, 0]], ![![11, 32, 15], ![18, 0, 0]]]
    h := ![![![-18963, -61463, -41143], ![-6683, 298256, 0]], ![![112576, 364955, 244301], ![39780, -1771000, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {2} * I29N1 =  Ideal.span {B.equivFun.symm ![-196, 426, -123]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 
