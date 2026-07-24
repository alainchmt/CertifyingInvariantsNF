import IdealArithmetic.Examples.NF3_1_244068_1.PrimesBelow3_1_244068_1F2
import IdealArithmetic.Examples.NF3_1_244068_1.ClassGroupData3_1_244068_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 3 ![![83, 0, 0], ![35, 1, 0]]
  ![378131420931263, 4788135878738, 17260834173768] ![![3, 0, 0], ![14, 1, 1]] where
    su := ![![249, 0, 0], ![105, 3, 0]]
    hsu := by decide
    w := ![![1134394262793789, 14364407636214, 51782502521304], ![5404971735445026, 68441122999809, 246724592761041]]
    hw := by decide
    g := ![![![423119, -4637343, 656291], ![647567, 0, 104440]], ![![212183, -2109134, -81163], ![260119, 0, 45506]]]
    h := ![![![-27755391951063972, -647495782339632157, -107954932514593608], ![-19505234947311623, 1493379443257573872, 0]], ![![-132244241638032006, -3085079427100164863, -514365576485043911], ![-92935275716039528, 7115404181631594160, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {3} * I83N1 =  Ideal.span {B.equivFun.symm ![378131420931263, 4788135878738, 17260834173768]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 3 ![![89, 0, 0], ![39, 1, 0]]
  ![301, -530, -138] ![![3, 0, 0], ![14, 1, 1]] where
    su := ![![267, 0, 0], ![117, 3, 0]]
    hsu := by decide
    w := ![![903, -1590, -414], ![-4542, 6219, -1107]]
    hw := by decide
    g := ![![![239299, -267566, -107613], ![991676, 0, 255]], ![![106641, -119244, -47959], ![441959, 0, 114]]]
    h := ![![![23255, 614892, 92262], ![17122, -1368576, 0]], ![![-114441, -3024664, -453849], ![-84111, 6732032, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {3} * I89N1 =  Ideal.span {B.equivFun.symm ![301, -530, -138]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E103RS1 : RelationCertificate Table 3 ![![103, 0, 0], ![18, 1, 0]]
  ![19255883, 243830, 878987] ![![3, 0, 0], ![16, 0, 1]] where
    su := ![![309, 0, 0], ![54, 3, 0]]
    hsu := by decide
    w := ![![57767649, 731490, 2636961], ![300959904, 3810942, 13738131]]
    hw := by decide
    g := ![![![69, -1992, -672], ![193, 0, 0]], ![![12, -227, -220], ![11, 0, 0]]]
    h := ![![![6363383593, 63300118254, 19994812463], ![1726611891, -343244134117, 0]], ![![33152176852, 329783154460, 104169668379], ![8995362524, -1788245210610, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {3} * I103N1 =  Ideal.span {B.equivFun.symm ![19255883, 243830, 878987]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E103RS1 


noncomputable def E109RS1 : RelationCertificate Table 3 ![![109, 0, 0], ![30, 1, 0]]
  ![-34034269, 34290116, -30370515] ![![3, 0, 0], ![14, 1, 1]] where
    su := ![![327, 0, 0], ![90, 3, 0]]
    hsu := by decide
    w := ![![-102102807, 102870348, -91111545], ![11421060, 211863159, 410750946]]
    hw := by decide
    g := ![![![3400410115057341, -3818961856078328, -1539062874544504], ![14082572293393334, 0, 105]], ![![956619384019164, -1074368330507325, -432976414372511], ![3961775543796220, 0, 30]]]
    h := ![![![7021937615, 121830169684, 23585109753], ![3050351452, -428467888932, 0]], ![![-410837792, -7127584641, -1378718688], ![-178465277, 25069542329, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {3} * I109N1 =  Ideal.span {B.equivFun.symm ![-34034269, 34290116, -30370515]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS1 
