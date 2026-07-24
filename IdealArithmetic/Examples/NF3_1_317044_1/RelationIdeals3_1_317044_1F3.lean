import IdealArithmetic.Examples.NF3_1_317044_1.PrimesBelow3_1_317044_1F3
import IdealArithmetic.Examples.NF3_1_317044_1.ClassGroupData3_1_317044_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 4 ![![139, 0, 0], ![45, 1, 0]]
  ![-15927762, -4597667, 649275] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![556, 0, 0], ![180, 4, 0]]
    hsu := by decide
    w := ![![-63711048, -18390668, 2597100], ![-61377012, -38108596, -22339060]]
    hw := by decide
    g := ![![![169909025296258, -14649492606849, 7965658769720], ![38814883172355, -1133730, 0]], ![![51211760357104, -4415458808442, 2400904917015], ![11699075387169, -371241, 0]]]
    h := ![![![238877412, 4896921, -36735], ![-738219734, 1151088, 0]], ![![226193013, 4597559, -79620], ![-699026068, 1096483, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {4} * I139N1 =  Ideal.span {B.equivFun.symm ![-15927762, -4597667, 649275]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E139RS1 
