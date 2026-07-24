import IdealArithmetic.Examples.NF3_1_439052_1.PrimesBelow3_1_439052_1F0
import IdealArithmetic.Examples.NF3_1_439052_1.ClassGroupData3_1_439052_1

set_option linter.all false

noncomputable section


noncomputable def E5RS0 : RelationCertificate Table 5 ![![5, 0, 0], ![0, 1, 0]]
  ![47, -2, -1] ![![5, 0, 0], ![-39, 2, 1]] where
    su := ![![25, 0, 0], ![0, 5, 0]]
    hsu := by decide
    w := ![![235, -10, -5], ![-640, 65, 20]]
    hw := by decide
    g := ![![![37, -5, 0], ![3, 0, 0]], ![![29, 6, -3], ![8, 0, 0]]]
    h := ![![![9, -2, -1], ![8, 2, 0]], ![![-25, 4, 2], ![-7, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {5} * I5N0 =  Ideal.span {B.equivFun.symm ![47, -2, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![-39, 2, 1]]
  ![1, 0, 0] ![![5, 0, 0], ![-39, 2, 1]] where
    su := ![![5, 0, 0], ![-39, 2, 1]]
    hsu := by decide
    w := ![![5, 0, 0], ![-39, 2, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS1 


noncomputable def E11RS0 : RelationCertificate Table 38 ![![11, 0, 0], ![-37, -2, 1]]
  ![-48, -2, 1] ![![38, 0, 0], ![3, 1, 0]] where
    su := ![![418, 0, 0], ![-1406, -76, 38]]
    hsu := by decide
    w := ![![-1824, -76, 38], ![-418, 0, 0]]
    hw := by decide
    g := ![![![31364, 95148, 63520], ![5015, -1206880, 0]], ![![-105863, -321128, -214380], ![-16797, 4073220, 0]]]
    h := ![![![36, 2, -1], ![12, 0, 0]], ![![36, 2, -1], ![11, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {38} * I11N0 =  Ideal.span {B.equivFun.symm ![-48, -2, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 38 ![![11, 0, 0], ![3, 1, 0]]
  ![-10, -2, 1] ![![38, 0, 0], ![3, 1, 0]] where
    su := ![![418, 0, 0], ![114, 38, 0]]
    hsu := by decide
    w := ![![-380, -76, 38], ![-304, 38, 0]]
    hw := by decide
    g := ![![![-1, -5, -3], ![15, 56, 0]], ![![-1, -5, -3], ![16, 56, 0]]]
    h := ![![![2, 10, 7], ![2, -38, 0]], ![![-1, 8, 6], ![12, -33, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {38} * I11N1 =  Ideal.span {B.equivFun.symm ![-10, -2, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E17RS1 : RelationCertificate Table 190 ![![17, 0, 0], ![4, 1, 0]]
  ![-493, 137, -21] ![![190, 0, 0], ![-133, 9, 2]] where
    su := ![![3230, 0, 0], ![760, 190, 0]]
    hsu := by decide
    w := ![![-93670, 26030, -3990], ![48260, -13490, 2090]]
    hw := by decide
    g := ![![![15921023, 1630888, -768421], ![-11075548, 8407553, 0]], ![![5229596, 535689, -252402], ![-3637866, 2761605, 0]]]
    h := ![![![659, 3068, 1539], ![349, -13092, 0]], ![![-344, -1582, -793], ![-161, 6746, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {190} * I17N1 =  Ideal.span {B.equivFun.symm ![-493, 137, -21]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 2 ![![19, 0, 0], ![3, 1, 0]]
  ![35, -3, -1] ![![38, 0, 0], ![3, 1, 0]] where
    su := ![![38, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![1330, -114, -38], ![374, -28, -10]]
    hw := by decide
    g := ![![![137, 500, 329], ![57, -6270, 0]], ![![34, 72, 51], ![28, -960, 0]]]
    h := ![![![-839, -2737, -1833], ![-266, 17404, 0]], ![![-236, -769, -515], ![-73, 4890, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {2} * I19N0 =  Ideal.span {B.equivFun.symm ![35, -3, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E19RS0 


noncomputable def E29RS1 : RelationCertificate Table 38 ![![29, 0, 0], ![8, 1, 0]]
  ![-1269, -41, 11] ![![38, 0, 0], ![3, 1, 0]] where
    su := ![![1102, 0, 0], ![304, 38, 0]]
    hsu := by decide
    w := ![![-48222, -1558, 418], ![-6840, -798, -38]]
    hw := by decide
    g := ![![![-334, 89, -17], ![-14, 51, 0]], ![![42, -15, 1], ![37, 18, 0]]]
    h := ![![![4075, 38308, 9599], ![2467, -139180, 0]], ![![570, 5391, 1351], ![360, -19590, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {38} * I29N1 =  Ideal.span {B.equivFun.symm ![-1269, -41, 11]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E29RS1 
