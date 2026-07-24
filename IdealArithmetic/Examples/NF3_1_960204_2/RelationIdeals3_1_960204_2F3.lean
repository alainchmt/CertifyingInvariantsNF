import IdealArithmetic.Examples.NF3_1_960204_2.PrimesBelow3_1_960204_2F3
import IdealArithmetic.Examples.NF3_1_960204_2.ClassGroupData3_1_960204_2

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 363 ![![139, 0, 0], ![-39, 1, 0]]
  ![-1707, 6, -40] ![![363, 0, 0], ![62, 0, 1]] where
    su := ![![50457, 0, 0], ![-14157, 363, 0]]
    hsu := by decide
    w := ![![-619641, 2178, -14520], ![-107448, 0, -2541]]
    hw := by decide
    g := ![![![-123092, -49674, -2426], ![-20939, 901581, 0]], ![![344207768, 138922477, 6784115], ![58809210, -2521442957, 0]]]
    h := ![![![35353449, 1411494836, -105862240], ![235402, 4904950440, 0]], ![![6130039, 244743239, -18355765], ![40819, 850483776, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {363} * I139N1 =  Ideal.span {B.equivFun.symm ![-1707, 6, -40]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 9 ![![149, 0, 0], ![43, 1, 0]]
  ![60, 6, -55] ![![9, 0, 0], ![26, 0, 1]] where
    su := ![![1341, 0, 0], ![387, 9, 0]]
    hsu := by decide
    w := ![![540, 54, -495], ![-774, -261, 891]]
    hw := by decide
    g := ![![![8691, -4127, -916], ![25050, -2384, 0]], ![![2560, -1183, -270], ![7393, -684, 0]]]
    h := ![![![-1367, 57055, 4075], ![31, -202410, 0]], ![![1916, -81406, -5814], ![75, 288795, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {9} * I149N1 =  Ideal.span {B.equivFun.symm ![60, 6, -55]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E149RS1 


noncomputable def E151RS0 : RelationCertificate Table 1089 ![![151, 0, 0], ![-66, 1, 0]]
  ![-447, 318, 58] ![![1089, 0, 0], ![62, 0, 1]] where
    su := ![![164439, 0, 0], ![-71874, 1089, 0]]
    hsu := by decide
    w := ![![-486783, 346302, 63162], ![-8712, 6534, 1089]]
    hw := by decide
    g := ![![![-79417, -31250, -1558], ![-4436, 1701564, 0]], ![![34813, 13703, 683], ![2142, -746129, 0]]]
    h := ![![![-8150883, -544788036, 24393508], ![-45096, -1227806550, 0]], ![![-146200, -9772637, 437581], ![-777, -22024910, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N0 : Ideal.span {1089} * I151N0 =  Ideal.span {B.equivFun.symm ![-447, 318, 58]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E151RS0 


noncomputable def E151RS1 : RelationCertificate Table 1089 ![![151, 0, 0], ![-49, 1, 0]]
  ![24614940, 40530, 583939] ![![1089, 0, 0], ![62, 0, 1]] where
    su := ![![164439, 0, 0], ![-53361, 1089, 0]]
    hsu := by decide
    w := ![![26805669660, 44137170, 635909571], ![1556222382, 2562417, 36918189]]
    hw := by decide
    g := ![![![43316868471431386, 17042085717387813, 849838961548300], ![2466938185666229, -927941567311766371, 0]], ![![-14056466381513869, -5530212903440365, -275775539974291], ![-800529560324503, 301120092592327879, 0]]]
    h := ![![![-1098392736, -54820384776, 3289229599], ![-6616794, -165557695170, 0]], ![![-63767942, -3182636766, 190958584], ![-384031, -9611570761, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {1089} * I151N1 =  Ideal.span {B.equivFun.symm ![24614940, 40530, 583939]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E151RS1 


noncomputable def E151RS2 : RelationCertificate Table 1089 ![![151, 0, 0], ![-36, 1, 0]]
  ![-5295, 3840, 536] ![![1089, 0, 0], ![62, 0, 1]] where
    su := ![![164439, 0, 0], ![-39204, 1089, 0]]
    hsu := by decide
    w := ![![-5766255, 4181760, 583704], ![-106722, 78408, 9801]]
    hw := by decide
    g := ![![![-250973, -97848, -4933], ![-13673, 5327622, 0]], ![![-56791, -22539, -1112], ![-2943, 1227295, 0]]]
    h := ![![![59649, 2204946, -178774], ![384, 8998470, 0]], ![![1110, 40812, -3309], ![32, 166556, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N2 : Ideal.span {1089} * I151N2 =  Ideal.span {B.equivFun.symm ![-5295, 3840, 536]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E151RS2 


noncomputable def E157RS1 : RelationCertificate Table 3 ![![157, 0, 0], ![76, 1, 0]]
  ![36, 0, 1] ![![3, 0, 0], ![29, 0, 1]] where
    su := ![![471, 0, 0], ![228, 3, 0]]
    hsu := by decide
    w := ![![108, 0, 3], ![1092, 3, 24]]
    hw := by decide
    g := ![![![4, -680, -39], ![276, -157, 0]], ![![-9, -325, -19], ![133, -75, 0]]]
    h := ![![![-348, 21324, 853], ![132, -44640, 0]], ![![-2928, 215598, 8624], ![115, -451320, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {3} * I157N1 =  Ideal.span {B.equivFun.symm ![36, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E157RS1 


noncomputable def E163RS1 : RelationCertificate Table 9 ![![163, 0, 0], ![-80, 1, 0]]
  ![368040, 606, 8731] ![![9, 0, 0], ![26, 0, 1]] where
    su := ![![1467, 0, 0], ![-720, 9, 0]]
    hsu := by decide
    w := ![![3312360, 5454, 78579], ![10019034, 16497, 237681]]
    hw := by decide
    g := ![![![2420473, -7063459, -331371], ![6955717, -3973200, 0]], ![![519290054377, -1515387338722, -71096256255], ![1492271684236, -852405378026, 0]]]
    h := ![![![8591182, 694050478, -25705529], ![41558, 1396669986, 0]], ![![25985993, 2099323546, -77752590], ![125468, 4224566193, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {9} * I163N1 =  Ideal.span {B.equivFun.symm ![368040, 606, 8731]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E163RS1 


noncomputable def E179RS1 : RelationCertificate Table 1089 ![![179, 0, 0], ![-44, 1, 0]]
  ![1611177, 2652, 38222] ![![1089, 0, 0], ![62, 0, 1]] where
    su := ![![194931, 0, 0], ![-47916, 1089, 0]]
    hsu := by decide
    w := ![![1754571753, 2888028, 41623758], ![101862882, 167706, 2416491]]
    hw := by decide
    g := ![![![142133542819242, 55919370571300, 2788535429572], ![8094644803413, -3044809727607215, 0]], ![![-35731896238751, -14057942322103, -701028459934], ![-2034966570365, 765454959438489, 0]]]
    h := ![![![-30777861, -1383593736, 92239858], ![-164004, -5503632120, 0]], ![![-1786830, -80325495, 5355049], ![-9521, -319517184, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {1089} * I179N1 =  Ideal.span {B.equivFun.symm ![1611177, 2652, 38222]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E179RS1 


noncomputable def E193RS1 : RelationCertificate Table 3 ![![193, 0, 0], ![-96, 1, 0]]
  ![48, 0, 1] ![![3, 0, 0], ![29, 0, 1]] where
    su := ![![579, 0, 0], ![-288, 3, 0]]
    hsu := by decide
    w := ![![144, 0, 3], ![1440, 3, 36]]
    hw := by decide
    g := ![![![18, -836, -49], ![338, -193, 0]], ![![-20, 416, 24], ![-167, 96, 0]]]
    h := ![![![336, 24799, -767], ![161, 49344, 0]], ![![2654, 247739, -7662], ![196, 492926, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {3} * I193N1 =  Ideal.span {B.equivFun.symm ![48, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E193RS1 
