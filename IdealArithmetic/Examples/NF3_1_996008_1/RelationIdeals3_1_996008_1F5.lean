import IdealArithmetic.Examples.NF3_1_996008_1.PrimesBelow3_1_996008_1F5
import IdealArithmetic.Examples.NF3_1_996008_1.ClassGroupData3_1_996008_1

set_option linter.all false

noncomputable section


noncomputable def E263RS1 : RelationCertificate Table 243 ![![263, 0, 0], ![61, 1, 0]]
  ![-22779, 883, 313] ![![243, 0, 0], ![-48, -1, 1]] where
    su := ![![63909, 0, 0], ![14823, 243, 0]]
    hsu := by decide
    w := ![![-5535297, 214569, 76059], ![1206252, 56619, -30861]]
    hw := by decide
    g := ![![![-15906927013, 1932597652, 70566394], ![3134446501, 20282012832, 0]], ![![-3747343789, 455280199, 16623994], ![738410900, 4778023952, 0]]]
    h := ![![![-322518, -5599, -4], ![1390155, 1365, 0]], ![![70270, 1182, 0], ![-302886, -127, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N1 : Ideal.span {243} * I263N1 =  Ideal.span {B.equivFun.symm ![-22779, 883, 313]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E263RS1 


noncomputable def E271RS1 : RelationCertificate Table 81 ![![271, 0, 0], ![12, 1, 0]]
  ![-387, -4, 8] ![![81, 0, 0], ![-48, -1, 1]] where
    su := ![![21951, 0, 0], ![972, 81, 0]]
    hsu := by decide
    w := ![![-31347, -324, 648], ![16200, 1863, -567]]
    hw := by decide
    g := ![![![-3164784639, 519355836, -1496576], ![1868997695, 1747774983, 0]], ![![-162048962, 26592992, -76631], ![95699832, 89492717, 0]]]
    h := ![![![-1881, -157, 0], ![42447, 8, 0]], ![![944, 67, -1], ![-21302, 264, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R271N1 : Ideal.span {81} * I271N1 =  Ideal.span {B.equivFun.symm ![-387, -4, 8]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E271RS1 


noncomputable def E281RS0 : RelationCertificate Table 2187 ![![281, 0, 0], ![47, 1, 0]]
  ![-2291067, -311149, 86753] ![![2187, 0, 0], ![681, -1, 1]] where
    su := ![![614547, 0, 0], ![102789, 2187, 0]]
    hsu := by decide
    w := ![![-5010563529, -680482863, 189728811], ![-1639001223, -202371858, 59267700]]
    hw := by decide
    g := ![![![-1534893, 83605, -67967], ![-476674, -1769940, 0]], ![![-299969, 1991, -13098], ![-92806, -297800, 0]]]
    h := ![![![-2291339, -50989, 281], ![13650536, 7792, 0]], ![![-749589, -16665, 87], ![4465640, 2653, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R281N0 : Ideal.span {2187} * I281N0 =  Ideal.span {B.equivFun.symm ![-2291067, -311149, 86753]} * (J0 ^ 7*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_1 E281RS0 


noncomputable def E281RS1 : RelationCertificate Table 3 ![![281, 0, 0], ![48, 1, 0]]
  ![-15, -5, 1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![843, 0, 0], ![144, 3, 0]]
    hsu := by decide
    w := ![![-45, -15, 3], ![213, 15, -6]]
    hw := by decide
    g := ![![![21958, 219110, -241001], ![65719, 723008, 0]], ![![3840, 38306, -42133], ![11490, 126400, 0]]]
    h := ![![![-183, -4, 0], ![1071, 1, 0]], ![![463, -38, -1], ![-2709, 279, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R281N1 : Ideal.span {3} * I281N1 =  Ideal.span {B.equivFun.symm ![-15, -5, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E281RS1 


noncomputable def E281RS2 : RelationCertificate Table 3 ![![281, 0, 0], ![-95, 1, 0]]
  ![-917, -18, 20] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![843, 0, 0], ![-285, 3, 0]]
    hsu := by decide
    w := ![![-2751, -54, 60], ![3960, -417, -18]]
    hw := by decide
    g := ![![![-26341, -6270, -957], ![-2088, -17, 0]], ![![8227, 1958, 299], ![653, 5, 0]]]
    h := ![![![-31952, 438, -1], ![-94501, 301, 0]], ![![46220, -489, 0], ![136700, -6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R281N2 : Ideal.span {3} * I281N2 =  Ideal.span {B.equivFun.symm ![-917, -18, 20]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E281RS2 
