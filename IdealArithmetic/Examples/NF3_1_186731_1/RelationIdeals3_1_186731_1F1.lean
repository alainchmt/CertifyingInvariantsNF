import IdealArithmetic.Examples.NF3_1_186731_1.PrimesBelow3_1_186731_1F1
import IdealArithmetic.Examples.NF3_1_186731_1.ClassGroupData3_1_186731_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 3 ![![37, 0, 0], ![11, 1, 0]]
  ![7799415, -611579, 756012] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![111, 0, 0], ![33, 3, 0]]
    hsu := by decide
    w := ![![23398245, -1834737, 2268036], ![-56784318, 4452654, -5504211]]
    hw := by decide
    g := ![![![-3656, 1034, 1107], ![-872, 0, 0]], ![![-3278, 413, 480], ![-955, 0, 0]]]
    h := ![![![1594814424, 7772903272, 5394074916], ![684212517, -22175557320, 0]], ![![-3870394982, -18863765690, -13090676901], ![-1660489452, 53817023400, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {3} * I37N1 =  Ideal.span {B.equivFun.symm ![7799415, -611579, 756012]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 2 ![![41, 0, 0], ![14, 1, 0]]
  ![13475865, -1056689, 1306241] ![![2, 0, 0], ![2, 1, 1]] where
    su := ![![82, 0, 0], ![28, 2, 0]]
    hsu := by decide
    w := ![![26951730, -2113378, 2612482], ![38337354, -3006164, 3716112]]
    hw := by decide
    g := ![![![8990, -1701, -3523], ![6379, 0, 0]], ![![3380, -354, -1105], ![2652, 0, 0]]]
    h := ![![![15882281, 96918231, 54669697], ![7787104, -248905704, 0]], ![![22591677, 137860855, 77764638], ![11076711, -354054678, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {2} * I41N1 =  Ideal.span {B.equivFun.symm ![13475865, -1056689, 1306241]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 6 ![![43, 0, 0], ![-2, 1, 0]]
  ![-447, -335, -255] ![![6, 0, 0], ![4, 1, 3]] where
    su := ![![258, 0, 0], ![-12, 6, 0]]
    hsu := by decide
    w := ![![-2682, -2010, -1530], ![81132, 6948, -2586]]
    hw := by decide
    g := ![![![-963919, 193720, 141485], ![-539575, 0, 0]], ![![230454, -46316, -33829], ![129008, 0, 0]]]
    h := ![![![-9461, -19, -28425], ![482, 135780, 0]], ![![295634, 346, 887863], ![-13720, -4242060, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {6} * I43N1 =  Ideal.span {B.equivFun.symm ![-447, -335, -255]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 3 ![![47, 0, 0], ![-15, 1, 0]]
  ![-7425, -1181, -258] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![141, 0, 0], ![-45, 3, 0]]
    hsu := by decide
    w := ![![-22275, -3543, -774], ![10446, -10452, -10629]]
    hw := by decide
    g := ![![![31054356, -5497408, 3285411], ![8518984, 0, 0]], ![![-15382206, 2723039, -1627368], ![-4219719, 0, 0]]]
    h := ![![![-83103, 407357, -282558], ![35216, 1475552, 0]], ![![40804, -200038, 138615], ![-17234, -724272, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {3} * I47N1 =  Ideal.span {B.equivFun.symm ![-7425, -1181, -258]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 6 ![![53, 0, 0], ![16, 1, 0]]
  ![-23274, 1825, -2256] ![![6, 0, 0], ![4, 1, 3]] where
    su := ![![318, 0, 0], ![96, 6, 0]]
    hsu := by decide
    w := ![![-139644, 10950, -13536], ![-537534, 42150, -52104]]
    hw := by decide
    g := ![![![327, -3, -109], ![167, 0, 0]], ![![127, 6, -38], ![70, 0, 0]]]
    h := ![![![3478454, 23552257, 11790168], ![1494524, -69431240, 0]], ![![13389703, 90660101, 45384092], ![5752792, -267262840, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {6} * I53N1 =  Ideal.span {B.equivFun.symm ![-23274, 1825, -2256]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E53RS1 


noncomputable def E61RS1 : RelationCertificate Table 3 ![![61, 0, 0], ![9, 1, 0]]
  ![9, 1, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![183, 0, 0], ![27, 3, 0]]
    hsu := by decide
    w := ![![27, 3, 0], ![12, 12, 9]]
    hw := by decide
    g := ![![![32, -6, 3], ![10, 0, 0]], ![![0, -1, 0], ![3, 0, 0]]]
    h := ![![![21, 109, 90], ![62, -610, 0]], ![![7, 47, 39], ![41, -264, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {3} * I61N1 =  Ideal.span {B.equivFun.symm ![9, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E61RS1 
