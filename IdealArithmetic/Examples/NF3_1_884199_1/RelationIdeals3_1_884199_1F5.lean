import IdealArithmetic.Examples.NF3_1_884199_1.PrimesBelow3_1_884199_1F5
import IdealArithmetic.Examples.NF3_1_884199_1.ClassGroupData3_1_884199_1

set_option linter.all false

noncomputable section


noncomputable def E263RS1 : RelationCertificate Table 25 ![![263, 0, 0], ![72, 1, 0]]
  ![293097697, 75201263, 14220194] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![6575, 0, 0], ![1800, 25, 0]]
    hsu := by decide
    w := ![![7327442425, 1880031575, 355504850], ![884066025, 226828400, 42892150]]
    hw := by decide
    g := ![![![-46336, -11548, 2838], ![53429, 0, 0]], ![![-9941, -2905, 695], ![11554, 0, 0]]]
    h := ![![![336176636687, 5186758441, 21315769], ![-1227974477097, -1863942351, 0]], ![![40560174303, 625789529, 2571776], ![-148156812209, -224887134, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N1 : Ideal.span {25} * I263N1 =  Ideal.span {B.equivFun.symm ![293097697, 75201263, 14220194]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E263RS1 
