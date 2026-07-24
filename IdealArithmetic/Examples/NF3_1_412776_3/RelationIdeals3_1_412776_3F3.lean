import IdealArithmetic.Examples.NF3_1_412776_3.PrimesBelow3_1_412776_3F3
import IdealArithmetic.Examples.NF3_1_412776_3.ClassGroupData3_1_412776_3

set_option linter.all false

noncomputable section


noncomputable def E139RS0 : RelationCertificate Table 22 ![![139, 0, 0], ![28, 1, 0]]
  ![-10, -21, 12] ![![22, 0, 0], ![7, 1, 1]] where
    su := ![![3058, 0, 0], ![616, 22, 0]]
    hsu := by decide
    w := ![![-220, -462, 264], ![-1078, 704, -220]]
    hw := by decide
    g := ![![![-11474905663804151, 1739043047237456, -62725107184989], ![-3574910077571653, 2477431208061074, -1394220]], ![![-2315112549185289, 350859562613443, -12655065500976], ![-721253788508386, 499832612795878, -281290]]]
    h := ![![![10, -29, -2], ![-50, 145, 0]], ![![-63, -29, -2], ![311, 134, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N0 : Ideal.span {22} * I139N0 =  Ideal.span {B.equivFun.symm ![-10, -21, 12]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E139RS0 


noncomputable def E139RS1 : RelationCertificate Table 22 ![![139, 0, 0], ![50, 1, 0]]
  ![314, -49, -16] ![![22, 0, 0], ![7, 1, 1]] where
    su := ![![3058, 0, 0], ![1100, 22, 0]]
    hsu := by decide
    w := ![![6908, -1078, -352], ![-5082, 440, 440]]
    hw := by decide
    g := ![![![-1985829254045279, 300956075291863, -10855109541661], ![-618668355116663, 428740376524248, -856100]], ![![-737593723981591, 111783685267612, -4031897835502], ![-229791103656312, 159246425792952, -317980]]]
    h := ![![![163326, 4019, 30], ![-454040, -2093, 0]], ![![-120279, -3009, -24], ![334371, 1678, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {22} * I139N1 =  Ideal.span {B.equivFun.symm ![314, -49, -16]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E139RS1 


noncomputable def E139RS2 : RelationCertificate Table 22 ![![139, 0, 0], ![61, 1, 0]]
  ![43882, 2995, 1532] ![![22, 0, 0], ![7, 1, 1]] where
    su := ![![3058, 0, 0], ![1342, 22, 0]]
    hsu := by decide
    w := ![![965404, 65890, 33704], ![814198, 55572, 28424]]
    hw := by decide
    g := ![![![1290578064589253581, -195589477757902071, 7054667678961669], ![402068711002083401, -278635699980406912, -1540980]], ![![573590250929111096, -86928656781373763, 3135407857319325], ![178697204889987437, -123838088880300448, -684880]]]
    h := ![![![27975624, 612383, 5052], ![-63747014, -350348, 0]], ![![23593988, 516447, 4260], ![-53762743, -295424, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N2 : Ideal.span {22} * I139N2 =  Ideal.span {B.equivFun.symm ![43882, 2995, 1532]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E139RS2 


noncomputable def E157RS1 : RelationCertificate Table 2 ![![157, 0, 0], ![-55, 1, 0]]
  ![-26, -2, -1] ![![2, 0, 0], ![15, 2, 1]] where
    su := ![![314, 0, 0], ![-110, 2, 0]]
    hsu := by decide
    w := ![![-52, -4, -2], ![-838, -54, -28]]
    hw := by decide
    g := ![![![-7, -5, -3], ![3, 0, 0]], ![![-14, 0, 0], ![1, 0, 0]]]
    h := ![![![-258, 32, -1], ![-736, 78, 0]], ![![-4437, 133, -2], ![-12658, 150, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {2} * I157N1 =  Ideal.span {B.equivFun.symm ![-26, -2, -1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E157RS1 


noncomputable def E163RS1 : RelationCertificate Table 22 ![![163, 0, 0], ![-30, 1, 0]]
  ![-62358, -4256, -2177] ![![22, 0, 0], ![5, 2, 1]] where
    su := ![![3586, 0, 0], ![-660, 22, 0]]
    hsu := by decide
    w := ![![-1371876, -93632, -47894], ![-1276110, -87098, -44550]]
    hw := by decide
    g := ![![![-19577, 3295, -546], ![-4153, 4050, 0]], ![![3550, -599, 98], ![770, -735, 0]]]
    h := ![![![-44094186, 1514252, -2979], ![-239576332, 241700, 0]], ![![-41016135, 1408547, -2771], ![-222852400, 224824, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {22} * I163N1 =  Ideal.span {B.equivFun.symm ![-62358, -4256, -2177]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E163RS1 


noncomputable def E173RS1 : RelationCertificate Table 2 ![![173, 0, 0], ![6, 1, 0]]
  ![6, 1, 0] ![![2, 0, 0], ![15, 1, 1]] where
    su := ![![346, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![12, 2, 0], ![202, 0, 8]]
    hw := by decide
    g := ![![![17010, 457744, -222198], ![245389, 0, -33168]], ![![698, 19072, -9259], ![10226, 0, -1382]]]
    h := ![![![-6, -1, 0], ![174, 0, 0]], ![![91, 15, 0], ![-2607, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {2} * I173N1 =  Ideal.span {B.equivFun.symm ![6, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E173RS1 
