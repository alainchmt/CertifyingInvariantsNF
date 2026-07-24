import IdealArithmetic.Examples.NF3_1_925444_2.PrimesBelow3_1_925444_2F5
import IdealArithmetic.Examples.NF3_1_925444_2.ClassGroupData3_1_925444_2

set_option linter.all false

noncomputable section


noncomputable def E263RS1 : RelationCertificate Table 3 ![![263, 0, 0], ![56, 1, 0]]
  ![-365609245467, -85989903157, -25615989449] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![789, 0, 0], ![168, 3, 0]]
    hsu := by decide
    w := ![![-1096827736401, -257969709471, -76847968347], ![-5770929745854, -1357300714149, -404333526336]]
    hw := by decide
    g := ![![![-6030969, 351754, -3644], ![117253, 263, 0]], ![![-1289962, 56584, 6670], ![18863, 56, 0]]]
    h := ![![![-2107801829365, 62392867285935, 5378556892077], ![-211574277942, -282917215721140, 0]], ![![-11090142846968, 328278399423962, 28299132970601], ![-1113192395359, -1488561349822035, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N1 : Ideal.span {3} * I263N1 =  Ideal.span {B.equivFun.symm ![-365609245467, -85989903157, -25615989449]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E263RS1 


noncomputable def E269RS0 : RelationCertificate Table 6 ![![269, 0, 0], ![44, 1, 0]]
  ![-2953818, -135400, 115927] ![![6, 0, 0], ![3, 1, 0]] where
    su := ![![1614, 0, 0], ![264, 6, 0]]
    hsu := by decide
    w := ![![-17722908, -812400, 695562], ![18304410, 78846, -445146]]
    hw := by decide
    g := ![![![29539978314, -31814142642, -33583790177], ![9467632057, 42004961151, 0]], ![![5720015560, -4876994511, -5279789319], ![2047175362, 6714547697, 0]]]
    h := ![![![-7392028994, 172159555638, 18712765703], ![-569106766, -1006746771636, 0]], ![![7636049021, -177842756249, -19330497104], ![587893700, 1039980729357, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R269N0 : Ideal.span {6} * I269N0 =  Ideal.span {B.equivFun.symm ![-2953818, -135400, 115927]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E269RS0 


noncomputable def E269RS1 : RelationCertificate Table 6 ![![269, 0, 0], ![66, 1, 0]]
  ![-5783682, -1360300, -405227] ![![6, 0, 0], ![3, 1, 0]] where
    su := ![![1614, 0, 0], ![396, 6, 0]]
    hsu := by decide
    w := ![![-34702092, -8161800, -2431362], ![-108643110, -25552446, -7611954]]
    hw := by decide
    g := ![![![1387340607064132, -3600850339672377, -3585262242962168], ![93528580253337, 4302314691554903, 0]], ![![335231001711608, -870093948259548, -866327307790530], ![22599842812552, 1039592769348685, 0]]]
    h := ![![![3523752122, -123201395920, -9058816173], ![406565964, 487364229062, 0]], ![![11031939779, -385711121085, -28360767471], ![1272850980, 1525809036208, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R269N1 : Ideal.span {6} * I269N1 =  Ideal.span {B.equivFun.symm ![-5783682, -1360300, -405227]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E269RS1 


noncomputable def E269RS2 : RelationCertificate Table 6 ![![269, 0, 0], ![-111, 1, 0]]
  ![-6, 2, 1] ![![6, 0, 0], ![3, 1, 0]] where
    su := ![![1614, 0, 0], ![-666, 6, 0]]
    hsu := by decide
    w := ![![-36, 12, 6], ![210, 36, 12]]
    hw := by decide
    g := ![![![-1473635, 3824812, 3808253], ![-99343, -4569904, 0]], ![![-29547503, 76690709, 76358716], ![-1991963, -91630459, 0]]]
    h := ![![![256, 14628, -671], ![-30, 36100, 0]], ![![-1355, -84651, 3883], ![480, -208905, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R269N2 : Ideal.span {6} * I269N2 =  Ideal.span {B.equivFun.symm ![-6, 2, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E269RS2 


noncomputable def E271RS1 : RelationCertificate Table 2 ![![271, 0, 0], ![-70, 1, 0]]
  ![-842, -198, -59] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![542, 0, 0], ![-140, 2, 0]]
    hsu := by decide
    w := ![![-1684, -396, -118], ![-14134, -3324, -990]]
    hw := by decide
    g := ![![![-726, 135, 24], ![-293, 0, 0]], ![![207, -44, -14], ![84, 3, 0]]]
    h := ![![![37486, 1315800, -96749], ![-4686, 5243784, 0]], ![![314355, 11043658, -812025], ![-40372, 44011656, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R271N1 : Ideal.span {2} * I271N1 =  Ideal.span {B.equivFun.symm ![-842, -198, -59]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E271RS1 
