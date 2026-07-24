import IdealArithmetic.Examples.NF3_3_418605_1.PrimesBelow3_3_418605_1F2
import IdealArithmetic.Examples.NF3_3_418605_1.ClassGroupData3_3_418605_1

set_option linter.all false

noncomputable section


noncomputable def E101RS1 : RelationCertificate Table 2 ![![101, 0, 0], ![13, 1, 0]]
  ![-127, 0, 5] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![202, 0, 0], ![26, 2, 0]]
    hsu := by decide
    w := ![![-254, 0, 10], ![3228, 180, -62]]
    hw := by decide
    g := ![![![19, 450, -88], ![-89, 0, 0]], ![![17, 17, -4], ![-2, 0, 0]]]
    h := ![![![16347, -196462, -49115], ![182, 1653540, 0]], ![![-207622, 2494778, 623689], ![-2008, -20997540, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {2} * I101N1 =  Ideal.span {B.equivFun.symm ![-127, 0, 5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 2 ![![103, 0, 0], ![21, 1, 0]]
  ![482, 11, -15] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![206, 0, 0], ![42, 2, 0]]
    hsu := by decide
    w := ![![964, 22, -30], ![-11316, -408, 298]]
    hw := by decide
    g := ![![![9, -1421, 275], ![287, 0, 0]], ![![14, -163, 31], ![34, 0, 0]]]
    h := ![![![-43864, 879025, 131853], ![-404, -4526958, 0]], ![![514761, -10315985, -1547389], ![4811, 53127072, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {2} * I103N0 =  Ideal.span {B.equivFun.symm ![482, 11, -15]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 2 ![![103, 0, 0], ![38, 1, 0]]
  ![2408, 71, -69] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![206, 0, 0], ![76, 2, 0]]
    hsu := by decide
    w := ![![4816, 142, -138], ![-55164, -1632, 1582]]
    hw := by decide
    g := ![![![-3, -143, -51], ![21, 0, 0]], ![![11, -68, -25], ![11, 0, 0]]]
    h := ![![![-20338, 754847, 61203], ![-108, -2101326, 0]], ![![232690, -8646220, -701035], ![1960, 24069132, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {2} * I103N1 =  Ideal.span {B.equivFun.symm ![2408, 71, -69]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 2 ![![107, 0, 0], ![24, 1, 0]]
  ![-1141, -472, 139] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![214, 0, 0], ![48, 2, 0]]
    hsu := by decide
    w := ![![-2282, -944, 278], ![-1596, -660, 194]]
    hw := by decide
    g := ![![![27, 86, 37], ![-253, 0, 0]], ![![14, 17, 7], ![-51, 0, 0]]]
    h := ![![![22663, -522584, -68161], ![210, 2431122, 0]], ![![15828, -365490, -47671], ![246, 1700298, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {2} * I107N1 =  Ideal.span {B.equivFun.symm ![-1141, -472, 139]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS1 
