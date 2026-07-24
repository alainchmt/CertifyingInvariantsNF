import IdealArithmetic.Examples.NF3_1_760455_3.PrimesBelow3_1_760455_3F3
import IdealArithmetic.Examples.NF3_1_760455_3.ClassGroupData3_1_760455_3

set_option linter.all false

noncomputable section


noncomputable def E149RS1 : RelationCertificate Table 5 ![![149, 0, 0], ![-71, 1, 0]]
  ![-100508, -111, -3342] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![745, 0, 0], ![-355, 5, 0]]
    hsu := by decide
    w := ![![-502540, -555, -16710], ![77140, 85, 2565]]
    hw := by decide
    g := ![![![521915, -941710, 2382641], ![-397105, -1701868, 0]], ![![-244392, 440971, -1115723], ![185952, 796936, 0]]]
    h := ![![![-92151844, 4599783773, -447250018], ![74782352, 9520035620, 0]], ![![14145345, -706067830, 68652977], ![-11479073, -1461327580, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {5} * I149N1 =  Ideal.span {B.equivFun.symm ![-100508, -111, -3342]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E149RS1 


noncomputable def E157RS1 : RelationCertificate Table 25 ![![157, 0, 0], ![-36, 1, 0]]
  ![-7186, 5863, -374] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![3925, 0, 0], ![-900, 25, 0]]
    hsu := by decide
    w := ![![-179650, 146575, -9350], ![-59600, 45075, 37675]]
    hw := by decide
    g := ![![![-2773599, 30687061, 30332899], ![339948, -109690334, 0]], ![![597743, -6861785, -6783672], ![-83177, 24528250, 0]]]
    h := ![![![-74382, 1487668, -281478], ![26539, 6313096, 0]], ![![-24652, 493274, -93321], ![8849, 2093272, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {25} * I157N1 =  Ideal.span {B.equivFun.symm ![-7186, 5863, -374]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E157RS1 


noncomputable def E181RS1 : RelationCertificate Table 25 ![![181, 0, 0], ![3, 1, 0]]
  ![17, -11, 3] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![4525, 0, 0], ![75, 25, 0]]
    hsu := by decide
    w := ![![425, -275, 75], ![225, -150, -50]]
    hw := by decide
    g := ![![![-798, -3378, -3392], ![-387, 12120, 0]], ![![-20, -75, -75], ![-1, 268, 0]]]
    h := ![![![1048, 1050, 3679], ![195, -95128, 0]], ![![555, 556, 1948], ![98, -50370, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {25} * I181N1 =  Ideal.span {B.equivFun.symm ![17, -11, 3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E181RS1 


noncomputable def E193RS1 : RelationCertificate Table 25 ![![193, 0, 0], ![46, 1, 0]]
  ![51546, 57, 1714] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![4825, 0, 0], ![1150, 25, 0]]
    hsu := by decide
    w := ![![1288650, 1425, 42850], ![475900, 525, 15825]]
    hw := by decide
    g := ![![![315, 1257, 1273], ![170, -4534, 0]], ![![79, 308, 312], ![38, -1112, 0]]]
    h := ![![![49128284, 1201465190, 186909049], ![17934592, -5153349249, 0]], ![![18143130, 443702600, 69025746], ![6623296, -1903138335, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {25} * I193N1 =  Ideal.span {B.equivFun.symm ![51546, 57, 1714]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E193RS1 
