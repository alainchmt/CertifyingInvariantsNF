import IdealArithmetic.Examples.NF3_1_557179_1.PrimesBelow3_1_557179_1F4
import IdealArithmetic.Examples.NF3_1_557179_1.ClassGroupData3_1_557179_1

set_option linter.all false

noncomputable section


noncomputable def E199RS1 : RelationCertificate Table 12 ![![199, 0, 0], ![-24, 1, 0]]
  ![5, 0, 1] ![![12, 0, 0], ![0, 2, 0]] where
    su := ![![2388, 0, 0], ![-288, 12, 0]]
    hsu := by decide
    w := ![![60, 0, 12], ![-288, 12, 0]]
    hw := by decide
    g := ![![![3, -185065, -1711838], ![-30843, 1141225, 0]], ![![0, 21681, 200550], ![3615, -133700, 0]]]
    h := ![![![11, 871, -341], ![91, 7540, 0]], ![![0, -4186, 1638], ![1, -36218, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {12} * I199N1 =  Ideal.span {B.equivFun.symm ![5, 0, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E199RS1 


noncomputable def E211RS1 : RelationCertificate Table 24 ![![211, 0, 0], ![93, 1, 0]]
  ![-305, 28, -23] ![![24, 0, 0], ![0, 2, 0]] where
    su := ![![5064, 0, 0], ![2232, 24, 0]]
    hsu := by decide
    w := ![![-7320, 672, -552], ![6624, -600, 504]]
    hw := by decide
    g := ![![![29, -769413, -6972787], ![-64108, 9297045, 0]], ![![15, -345314, -3129399], ![-28769, 4172530, 0]]]
    h := ![![![131434, 1331, -8], ![-298203, 185, 0]], ![![-119148, -1345, -6], ![270328, 143, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {24} * I211N1 =  Ideal.span {B.equivFun.symm ![-305, 28, -23]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E211RS1 
