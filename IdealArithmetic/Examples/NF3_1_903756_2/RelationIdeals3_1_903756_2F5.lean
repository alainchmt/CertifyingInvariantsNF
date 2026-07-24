import IdealArithmetic.Examples.NF3_1_903756_2.PrimesBelow3_1_903756_2F5
import IdealArithmetic.Examples.NF3_1_903756_2.ClassGroupData3_1_903756_2

set_option linter.all false

noncomputable section


noncomputable def E263RS1 : RelationCertificate Table 3 ![![263, 0, 0], ![66, 1, 0]]
  ![-4427979617, -147531474, 300712894] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![789, 0, 0], ![198, 3, 0]]
    hsu := by decide
    w := ![![-13283938851, -442594422, 902138682], ![54440333706, -2629352199, -720707532]]
    hw := by decide
    g := ![![![1270200837860390445, 95351005243198173, 99667461509189712], ![31783668414399391, 1294202, 0]], ![![389719327001358040, 29255318123403502, 30579680681870016], ![9751772707801169, 326508, 0]]]
    h := ![![![-164092274395, -2833613168124, -487059975796], ![-51953244270, 11645188577022, 0]], ![![686319406538, 11851664278303, 2037146463563], ![217295608890, -48706341832083, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N1 : Ideal.span {3} * I263N1 =  Ideal.span {B.equivFun.symm ![-4427979617, -147531474, 300712894]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E263RS1 
