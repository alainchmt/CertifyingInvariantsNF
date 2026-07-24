import IdealArithmetic.Examples.NF3_1_311467_2.PrimesBelow3_1_311467_2F3
import IdealArithmetic.Examples.NF3_1_311467_2.ClassGroupData3_1_311467_2

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 4 ![![139, 0, 0], ![32, 1, 0]]
  ![-36191, -757, 529] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![556, 0, 0], ![128, 4, 0]]
    hsu := by decide
    w := ![![-144764, -3028, 2116], ![-88872, -13444, -228]]
    hw := by decide
    g := ![![![10081765, -3679372, 162955], ![-919839, 1169298, 0]], ![![1770716, -646229, 11606], ![-161554, 273429, 0]]]
    h := ![![![-2731613, -92490, -219], ![11864313, 30970, 0]], ![![-1678110, -56831, -137], ![7288596, 18986, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {4} * I139N1 =  Ideal.span {B.equivFun.symm ![-36191, -757, 529]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 4 ![![149, 0, 0], ![13, 1, 0]]
  ![2509837, -973221, 113341] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![596, 0, 0], ![52, 4, 0]]
    hsu := by decide
    w := ![![10039348, -3892884, 453364], ![-19041288, 7383500, -859880]]
    hw := by decide
    g := ![![![7835, 963, 90], ![241, -365, 0]], ![![685, 133, 15], ![34, -33, 0]]]
    h := ![![![4916200, 373310, 989], ![-56154151, -34020, 0]], ![![-9324442, -708064, -1877], ![106506272, 64703, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {4} * I149N1 =  Ideal.span {B.equivFun.symm ![2509837, -973221, 113341]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E149RS1 
