import IdealArithmetic.Examples.NF3_1_672300_4.PrimesBelow3_1_672300_4F3
import IdealArithmetic.Examples.NF3_1_672300_4.ClassGroupData3_1_672300_4

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 49 ![![139, 0, 0], ![69, 1, 0]]
  ![-70113, -3913, -3714] ![![49, 0, 0], ![-7, 0, 1]] where
    su := ![![6811, 0, 0], ![3381, 49, 0]]
    hsu := by decide
    w := ![![-3435537, -191737, -181986], ![-275625, -15386, -14602]]
    hw := by decide
    g := ![![![-4289899095, 448956902, -40549909], ![612015200, 1374930520, 0]], ![![-2156403157, 225677122, -20383219], ![307641624, 691136191, 0]]]
    h := ![![![-5453897, -263008457, -27077830], ![-4599334, 537687808, 0]], ![![-437557, -21100544, -2172390], ![-368986, 43137416, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {49} * I139N1 =  Ideal.span {B.equivFun.symm ![-70113, -3913, -3714]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 49 ![![149, 0, 0], ![19, 1, 0]]
  ![-43, 56, -39] ![![49, 0, 0], ![-7, 0, 1]] where
    su := ![![7301, 0, 0], ![931, 49, 0]]
    hsu := by decide
    w := ![![-2107, 2744, -1911], ![7399, -1715, 637]]
    hw := by decide
    g := ![![![17660, -1885, 156], ![-2515, -5733, 0]], ![![241541, -25285, 2281], ![-34452, -77428, 0]]]
    h := ![![![-237, -2146, -835], ![-14, 17768, 0]], ![![806, 7458, 2901], ![187, -61748, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {49} * I149N1 =  Ideal.span {B.equivFun.symm ![-43, 56, -39]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E149RS1 


noncomputable def E157RS1 : RelationCertificate Table 49 ![![157, 0, 0], ![-32, 1, 0]]
  ![-1202539, -67116, -63701] ![![49, 0, 0], ![-7, 0, 1]] where
    su := ![![7693, 0, 0], ![-1568, 49, 0]]
    hsu := by decide
    w := ![![-58924411, -3288684, -3121349], ![-4727765, -263865, -250439]]
    hw := by decide
    g := ![![![-8920719579, 933592759, -84322371], ![1272667648, 2859127825, 0]], ![![1813546411, -189795652, 17142398], ![-258728173, -581249190, 0]]]
    h := ![![![-99279141, 1743172071, -369806610], ![31338348, 8294224867, 0]], ![![-7965589, 139862372, -29671213], ![2514481, 665482190, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {49} * I157N1 =  Ideal.span {B.equivFun.symm ![-1202539, -67116, -63701]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E157RS1 


noncomputable def E167RS0 : RelationCertificate Table 49 ![![167, 0, 0], ![48, 1, 0]]
  ![-229, 35, -6] ![![49, 0, 0], ![-7, 0, 1]] where
    su := ![![8183, 0, 0], ![2352, 49, 0]]
    hsu := by decide
    w := ![![-11221, 1715, -294], ![6811, -686, -98]]
    hw := by decide
    g := ![![![-1271001121, 133015878, -12014035], ![181326434, 407361136, 0]], ![![4634900549, -485062836, 43811008], ![-661234509, -1485504932, 0]]]
    h := ![![![1718509, 45559881, 6786198], ![766820, -161899296, 0]], ![![-1042531, -27637714, -4116670], ![-465024, 98211984, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N0 : Ideal.span {49} * I167N0 =  Ideal.span {B.equivFun.symm ![-229, 35, -6]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E167RS0 


noncomputable def E167RS1 : RelationCertificate Table 49 ![![167, 0, 0], ![-31, 1, 0]]
  ![-37267, -2080, -1974] ![![49, 0, 0], ![-19, 1, 0]] where
    su := ![![8183, 0, 0], ![-1519, 49, 0]]
    hsu := by decide
    w := ![![-1826083, -101920, -96726], ![395969, 22099, 20972]]
    hw := by decide
    g := ![![![150556673092, -1878101785982, 658019842842], ![-96707725981, -4606177931446, -15178935]], ![![-24998089098, 311835768240, -109256124850], ![16057131911, 764799354662, 2520276]]]
    h := ![![![-240561733, 4053287232, -886746882], ![68926496, 21155246760, 0]], ![![52163574, -878917428, 192282768], ![-14946001, -4587317404, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {49} * I167N1 =  Ideal.span {B.equivFun.symm ![-37267, -2080, -1974]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E167RS1 


noncomputable def E167RS2 : RelationCertificate Table 7 ![![167, 0, 0], ![-17, 1, 0]]
  ![1039, 58, 55] ![![7, 0, 0], ![3, -3, 1]] where
    su := ![![1169, 0, 0], ![-119, 7, 0]]
    hsu := by decide
    w := ![![7273, 406, 385], ![-11613, -651, -616]]
    hw := by decide
    g := ![![![90, 4, -5], ![43, 0, 0]], ![![-11, 3, -1], ![2, 0, 0]]]
    h := ![![![1538926, -14069519, 5472041], ![-240877, -130547256, 0]], ![![-2457228, 22465140, -8737340], ![384735, 208447956, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N2 : Ideal.span {7} * I167N2 =  Ideal.span {B.equivFun.symm ![1039, 58, 55]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E167RS2 


noncomputable def E181RS1 : RelationCertificate Table 49 ![![181, 0, 0], ![87, 1, 0]]
  ![-1713, 322, -90] ![![49, 0, 0], ![-11, 4, 1]] where
    su := ![![8869, 0, 0], ![4263, 49, 0]]
    hsu := by decide
    w := ![![-83937, 15778, -4410], ![11711, -13230, 9065]]
    hw := by decide
    g := ![![![33539, 1974, 2371], ![-7300, -865, 0]], ![![17566, 1053, 1227], ![-3789, -420, 0]]]
    h := ![![![35098, 2102795, 171170], ![28707, -4425980, 0]], ![![-4966, -295525, -24055], ![-3965, 622020, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {49} * I181N1 =  Ideal.span {B.equivFun.symm ![-1713, 322, -90]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E181RS1 
