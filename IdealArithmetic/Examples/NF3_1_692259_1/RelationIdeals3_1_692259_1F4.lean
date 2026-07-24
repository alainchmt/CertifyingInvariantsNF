import IdealArithmetic.Examples.NF3_1_692259_1.PrimesBelow3_1_692259_1F4
import IdealArithmetic.Examples.NF3_1_692259_1.ClassGroupData3_1_692259_1

set_option linter.all false

noncomputable section


noncomputable def E211RS1 : RelationCertificate Table 2 ![![211, 0, 0], ![78, 1, 0]]
  ![-21000, 856, 1221] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![422, 0, 0], ![156, 2, 0]]
    hsu := by decide
    w := ![![-42000, 1712, 2442], ![166178, -40536, 5010]]
    hw := by decide
    g := ![![![294587654, -41962177, 13445754], ![126312741, 0, 0]], ![![116897995, -16651392, 5335536], ![50123304, -3, 0]]]
    h := ![![![1875698, -144661853, -5636169], ![7919, 396410960, 0]], ![![-7454359, 574897531, 22398615], ![-30969, -1575368420, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {2} * I211N1 =  Ideal.span {B.equivFun.symm ![-21000, 856, 1221]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E211RS1 


noncomputable def E223RS0 : RelationCertificate Table 2 ![![223, 0, 0], ![101, 1, 0]]
  ![-374062, 55798, 4127] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![446, 0, 0], ![202, 2, 0]]
    hsu := by decide
    w := ![![-748124, 111596, 8254], ![205698, -440094, 175648]]
    hw := by decide
    g := ![![![-63630624725, 9063786093, -2904267757], ![-27283419316, -669, 0]], ![![-30453908669, 4337969571, -1389995892], ![-13057969549, -300, 0]]]
    h := ![![![7652742, -766714326, -23001415], ![28096, 1709773224, 0]], ![![-2183069, 218702987, 6561512], ![-7748, -487709784, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N0 : Ideal.span {2} * I223N0 =  Ideal.span {B.equivFun.symm ![-374062, 55798, 4127]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E223RS0 


noncomputable def E223RS2 : RelationCertificate Table 4 ![![223, 0, 0], ![-27, 1, 0]]
  ![1580, 334, -265] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![892, 0, 0], ![-108, 4, 0]]
    hsu := by decide
    w := ![![6320, 1336, -1060], ![-39564, 5820, 472]]
    hw := by decide
    g := ![![![-16929303324, 995683749, 53766876842], ![-3983404892, -71689310785, 0]], ![![2125571050, -125018557, -6750997681], ![500138127, 9001343754, 0]]]
    h := ![![![-186629, -5223341, 559643], ![-727, -41600218, 0]], ![![1181190, 33056302, -3541748], ![5381, 263269974, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N2 : Ideal.span {4} * I223N2 =  Ideal.span {B.equivFun.symm ![1580, 334, -265]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E223RS2 


noncomputable def E227RS1 : RelationCertificate Table 4 ![![227, 0, 0], ![-15, 1, 0]]
  ![2769500972, 164076366, 104091267] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![908, 0, 0], ![-60, 4, 0]]
    hsu := by decide
    w := ![![11078003888, 656305464, 416365068], ![18635479724, 1104040700, 700411632]]
    hw := by decide
    g := ![![![-21930602834821658, 1290035460866795, 69661914886879110], ![-5160141843488714, -92882553182495279, 0]], ![![1545769362810526, -90927609577531, -4910090917133787], ![363710438308251, 6546787889510992, 0]]]
    h := ![![![-118064545774, -1888676696824, 354127903041], ![-518539466, -26795643299680, 0]], ![![-198608835257, -3177142438717, 595715927124], ![-872290346, -45075780118080, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {4} * I227N1 =  Ideal.span {B.equivFun.symm ![2769500972, 164076366, 104091267]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E227RS1 


noncomputable def E229RS1 : RelationCertificate Table 4 ![![229, 0, 0], ![-49, 1, 0]]
  ![-39884, 8414, -631] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![916, 0, 0], ![-196, 4, 0]]
    hsu := by decide
    w := ![![-159536, 33656, -2524], ![-145472, -29788, 23980]]
    hw := by decide
    g := ![![![-286359890, -120785, -11433142], ![-71620165, -3435, 0]], ![![54109756, 22821, 2160309], ![13533148, 735, 0]]]
    h := ![![![-173552, -8662690, 519761], ![-576, -39675300, 0]], ![![-153610, -7668011, 460105], ![-428, -35119350, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {4} * I229N1 =  Ideal.span {B.equivFun.symm ![-39884, 8414, -631]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E229RS1 
