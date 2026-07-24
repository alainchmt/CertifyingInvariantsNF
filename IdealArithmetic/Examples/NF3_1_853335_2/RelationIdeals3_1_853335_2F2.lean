import IdealArithmetic.Examples.NF3_1_853335_2.PrimesBelow3_1_853335_2F2
import IdealArithmetic.Examples.NF3_1_853335_2.ClassGroupData3_1_853335_2

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 169 ![![83, 0, 0], ![-32, 1, 0]]
  ![811, 111, -74] ![![169, 0, 0], ![-74, 1, 0]] where
    su := ![![14027, 0, 0], ![-5408, 169, 0]]
    hsu := by decide
    w := ![![137059, 18759, -12506], ![-75036, -8957, 6253]]
    hw := by decide
    g := ![![![34, -5346, 507], ![45, -12214, 0]], ![![23, 610, -58], ![59, 1395, 0]]]
    h := ![![![6377, -188, -3], ![16515, 25, 0]], ![![-3476, 119, -2], ![-9002, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {169} * I83N1 =  Ideal.span {B.equivFun.symm ![811, 111, -74]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 845 ![![89, 0, 0], ![40, 1, 0]]
  ![4161, 706, 318] ![![845, 0, 0], ![-74, 1, 0]] where
    su := ![![75205, 0, 0], ![33800, 845, 0]]
    hsu := by decide
    w := ![![3516045, 596570, 268710], ![-243360, -41405, -18590]]
    hw := by decide
    g := ![![![37367179, 363320006219, -34368156463], ![426692809, 4148727458755, 0]], ![![17060666, 165880055531, -15691378413], ![194814370, 1894173537001, 0]]]
    h := ![![![59295009, 2070053, 102846], ![-131931291, -1307568, 0]], ![![-4104112, -143299, -7122], ![9131642, 90548, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {845} * I89N1 =  Ideal.span {B.equivFun.symm ![4161, 706, 318]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 169 ![![97, 0, 0], ![-21, 1, 0]]
  ![179, 27, -18] ![![169, 0, 0], ![-74, 1, 0]] where
    su := ![![16393, 0, 0], ![-3549, 169, 0]]
    hsu := by decide
    w := ![![30251, 4563, -3042], ![-16900, -2197, 1521]]
    hw := by decide
    g := ![![![-34076304, -15673743743, 1482694995], ![-77822908, -35796493452, 0]], ![![7131233, 3280071440, -310286144], ![16286194, 7491194048, 0]]]
    h := ![![![1802, -77, -3], ![8315, 39, 0]], ![![-1006, 54, -2], ![-4642, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {169} * I97N1 =  Ideal.span {B.equivFun.symm ![179, 27, -18]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E97RS1 


noncomputable def E103RS1 : RelationCertificate Table 5 ![![103, 0, 0], ![48, 1, 0]]
  ![17, 2, 1] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![515, 0, 0], ![240, 5, 0]]
    hsu := by decide
    w := ![![85, 10, 5], ![220, 40, 15]]
    hw := by decide
    g := ![![![-5303, 138308, 1005404], ![26605, -718146, 0]], ![![-2510, 65436, 475675], ![12588, -339768, 0]]]
    h := ![![![1319, 0, -4], ![-2830, 59, 0]], ![![3476, 86, 2], ![-7458, -29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {5} * I103N1 =  Ideal.span {B.equivFun.symm ![17, 2, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 845 ![![107, 0, 0], ![-32, 1, 0]]
  ![-5098, -853, -389] ![![845, 0, 0], ![-74, 1, 0]] where
    su := ![![90415, 0, 0], ![-27040, 845, 0]]
    hsu := by decide
    w := ![![-4307810, -720785, -328705], ![298285, 49855, 22815]]
    hw := by decide
    g := ![![![-17, -286696, 27120], ![-167, -3273760, 0]], ![![72, 80331, -7599], ![812, 917304, 0]]]
    h := ![![![-144788222, 4876871, -77058], ![-484135458, 1177831, 0]], ![![10025603, -337664, 5330], ![33523099, -81469, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {845} * I107N1 =  Ideal.span {B.equivFun.symm ![-5098, -853, -389]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E107RS1 


noncomputable def E131RS1 : RelationCertificate Table 5 ![![131, 0, 0], ![28, 1, 0]]
  ![19, 4, 2] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![655, 0, 0], ![140, 5, 0]]
    hsu := by decide
    w := ![![95, 20, 10], ![425, 65, 30]]
    hw := by decide
    g := ![![![-13, 65, 463], ![14, -331, 0]], ![![-4, 14, 105], ![6, -75, 0]]]
    h := ![![![1653, 55, -1], ![-7733, 19, 0]], ![![7395, 280, 4], ![-34595, -74, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {5} * I131N1 =  Ideal.span {B.equivFun.symm ![19, 4, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E131RS1 
