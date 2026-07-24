import IdealArithmetic.Examples.NF3_1_561295_1.PrimesBelow3_1_561295_1F4
import IdealArithmetic.Examples.NF3_1_561295_1.ClassGroupData3_1_561295_1

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 19683 ![![197, 0, 0], ![31, 1, 0]]
  ![3953, 1192, 954] ![![19683, 0, 0], ![-758, 1, 0]] where
    su := ![![3877551, 0, 0], ![610173, 19683, 0]]
    hsu := by decide
    w := ![![77806899, 23462136, 18777582], ![-3070548, -925101, -708588]]
    hw := by decide
    g := ![![![2532817773676981269946735, -1933211253167182718441496285, 22863208105143317920597874], ![-195757106417433039714297, -50001836125948441344454700092, -60303666240]], ![![408944536374925386136526, -312133066917615080538989343, 3691455475309563169287904], ![-31606616140314409533473, -8073213124502015466937446248, -9736529445]]]
    h := ![![![-71322, -2092955, -672768], ![-21673, 14726250, 0]], ![![2784, 82595, 26550], ![1050, -581154, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {19683} * I197N1 =  Ideal.span {B.equivFun.symm ![3953, 1192, 954]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E197RS1 


noncomputable def E197RS2 : RelationCertificate Table 27 ![![197, 0, 0], ![-61, 1, 0]]
  ![-74, -22, -9] ![![27, 0, 0], ![-2, 1, 0]] where
    su := ![![5319, 0, 0], ![-1647, 27, 0]]
    hsu := by decide
    w := ![![-1998, -594, -243], ![837, 243, -216]]
    hw := by decide
    g := ![![![9927, -40949, 74638], ![-2239, -224005, 538]], ![![-2940, 12102, -22059], ![673, 66203, -159]]]
    h := ![![![-253212, 19747764, -2777157], ![178790, 60788880, 0]], ![![106146, -8273086, 1163456], ![-74689, -25466760, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N2 : Ideal.span {27} * I197N2 =  Ideal.span {B.equivFun.symm ![-74, -22, -9]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E197RS2 


noncomputable def E199RS1 : RelationCertificate Table 81 ![![199, 0, 0], ![-77, 1, 0]]
  ![260, -11, 9] ![![81, 0, 0], ![-29, 1, 0]] where
    su := ![![16119, 0, 0], ![-6237, 81, 0]]
    hsu := by decide
    w := ![![21060, -891, 729], ![-8262, 405, -324]]
    hw := by decide
    g := ![![![14949632968, -628433815860, 176792534631], ![-13110779854, -1591132808968, 976]], ![![-5713413824, 240173284844, -67566134582], ![5010645516, 608095210202, -373]]]
    h := ![![![-1542, 168713, -18981], ![1462, 419692, 0]], ![![627, -66202, 7448], ![-517, -164684, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {81} * I199N1 =  Ideal.span {B.equivFun.symm ![260, -11, 9]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E199RS1 
