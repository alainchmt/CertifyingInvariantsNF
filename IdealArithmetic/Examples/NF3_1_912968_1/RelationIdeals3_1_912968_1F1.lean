import IdealArithmetic.Examples.NF3_1_912968_1.PrimesBelow3_1_912968_1F1
import IdealArithmetic.Examples.NF3_1_912968_1.ClassGroupData3_1_912968_1

set_option linter.all false

noncomputable section


noncomputable def E47RS0 : RelationCertificate Table 2 ![![47, 0, 0], ![22, 1, 0]]
  ![-247, 15, 2] ![![2, 0, 0], ![-15, -2, 1]] where
    su := ![![94, 0, 0], ![44, 2, 0]]
    hsu := by decide
    w := ![![-494, 30, 4], ![5968, 758, -276]]
    hw := by decide
    g := ![![![-57892, 306178, -29523], ![113339, 0, -6732]], ![![-28936, 153164, -14672], ![56569, 0, -3366]]]
    h := ![![![-3769, -128759, -11714], ![-4472, 275280, 0]], ![![44808, 1536148, 139750], ![53691, -3284194, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {2} * I47N0 =  Ideal.span {B.equivFun.symm ![-247, 15, 2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS0 


noncomputable def E47RS1 : RelationCertificate Table 2 ![![47, 0, 0], ![-14, 1, 0]]
  ![-10103035643481, -2321608546399, -519211841026] ![![2, 0, 0], ![-15, -2, 1]] where
    su := ![![94, 0, 0], ![-28, 2, 0]]
    hsu := by decide
    w := ![![-20206071286962, -4643217092798, -1038423682052], ![-141888854606352, -32605089115510, -7291904732492]]
    hw := by decide
    g := ![![![1017972, -4147020, 1184881], ![-2895287, 0, 7480]], ![![-383513, 1673948, -458831], ![973041, 0, -1870]]]
    h := ![![![3318287837171, -58806955562493, 8389697440694], ![-2239637984736, -197417495776822, 0]], ![![23301316410478, -412947744722289, 58913211947442], ![-15726939882312, -1386283456948010, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {2} * I47N1 =  Ideal.span {B.equivFun.symm ![-10103035643481, -2321608546399, -519211841026]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS1 


noncomputable def E47RS2 : RelationCertificate Table 2 ![![47, 0, 0], ![-9, 1, 0]]
  ![-9, 1, 0] ![![2, 0, 0], ![-15, -2, 1]] where
    su := ![![94, 0, 0], ![-18, 2, 0]]
    hsu := by decide
    w := ![![-18, 2, 0], ![322, 28, -12]]
    hw := by decide
    g := ![![![-119121, 628508, -61709], ![234123, 0, -13838]], ![![22550, -118905, 11674], ![-44292, 0, 2618]]]
    h := ![![![423, -4047, 900], ![-140, -21150, 0]], ![![-7412, 71837, -15978], ![2995, 375480, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N2 : Ideal.span {2} * I47N2 =  Ideal.span {B.equivFun.symm ![-9, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS2 


noncomputable def E67RS1 : RelationCertificate Table 2 ![![67, 0, 0], ![-28, 1, 0]]
  ![-23901, 273, 433] ![![2, 0, 0], ![-16, -1, 1]] where
    su := ![![134, 0, 0], ![-56, 2, 0]]
    hsu := by decide
    w := ![![-47802, 546, 866], ![398234, 61864, -20710]]
    hw := by decide
    g := ![![![-692576, -9693785, -6526686], ![7124197, 0, 0]], ![![186661, 2612574, 1759008], ![-1920043, 0, 0]]]
    h := ![![![-1558543, 62067736, -4435085], ![1577753, 148575564, 0]], ![![12944836, -515512486, 36836169], ![-13103998, -1234016839, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {2} * I67N1 =  Ideal.span {B.equivFun.symm ![-23901, 273, 433]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E67RS1 


noncomputable def E73RS1 : RelationCertificate Table 2 ![![73, 0, 0], ![15, 1, 0]]
  ![-185283246017, -42576823703, -9522014835] ![![2, 0, 0], ![-16, -1, 1]] where
    su := ![![146, 0, 0], ![30, 2, 0]]
    hsu := by decide
    w := ![![-370566492034, -85153647406, -19044029670], ![-4259105703422, -978713383780, -218882540994]]
    hw := by decide
    g := ![![![117126, -208574, 210815], ![-727233, 0, 0]], ![![13425, 10042, 21545], ![-101576, 0, 0]]]
    h := ![![![12929370710811, 210999355612941, 28143326472325], ![5547122140804, -1027236177247280, 0]], ![![148603712747617, 2425120938422550, 323465302093609], ![63755844241615, -11806538247051977, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {2} * I73N1 =  Ideal.span {B.equivFun.symm ![-185283246017, -42576823703, -9522014835]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 2 ![![79, 0, 0], ![-38, 1, 0]]
  ![56988917520739, 13095663782157, 2928755458080] ![![2, 0, 0], ![-15, -2, 1]] where
    su := ![![158, 0, 0], ![-76, 2, 0]]
    hsu := by decide
    w := ![![113977835041478, 26191327564314, 5857510916160], ![800362635312594, 183917863890652, 41131969838908]]
    hw := by decide
    g := ![![![2267731, -6157284, 2639055], ![-9531141, 0, -9450]], ![![-1320272, 3887458, -1546179], ![5241603, 0, 4410]]]
    h := ![![![-1699198435524727, 103444031861937343, -5445793823555448], ![2126754081163028, 215110320408169236, 0]], ![![-11931924635002072, 726393319527878116, -38240855289133468], ![14934258932379256, 1510524066913231713, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {2} * I79N1 =  Ideal.span {B.equivFun.symm ![56988917520739, 13095663782157, 2928755458080]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS1 
