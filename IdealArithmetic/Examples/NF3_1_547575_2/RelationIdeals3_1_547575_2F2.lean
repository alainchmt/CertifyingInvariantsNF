import IdealArithmetic.Examples.NF3_1_547575_2.PrimesBelow3_1_547575_2F2
import IdealArithmetic.Examples.NF3_1_547575_2.ClassGroupData3_1_547575_2

set_option linter.all false

noncomputable section


noncomputable def E97RS1 : RelationCertificate Table 4 ![![97, 0, 0], ![20, 1, 0]]
  ![147112424392190, 1056414766713, 3598746743600] ![![4, 0, 0], ![26, 1, 1]] where
    su := ![![388, 0, 0], ![80, 4, 0]]
    hsu := by decide
    w := ![![588449697568760, 4225659066852, 14394986974400], ![3893461949521252, 27958962093808, 95244052771616]]
    hw := by decide
    g := ![![![-178385, 2880109, 912510], ![-211321, 0, 4650]], ![![-20974, 247729, 240624], ![-14216, 0, 1550]]]
    h := ![![![869362415365990, 45710252054842, 256821582774], ![-4209052093305442, -10656473392739, 0]], ![![5752113559674209, 302440680679914, 1699253248800], ![-27849082490050898, -70508275970348, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {4} * I97N1 =  Ideal.span {B.equivFun.symm ![147112424392190, 1056414766713, 3598746743600]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E97RS1 


noncomputable def E107RS1 : RelationCertificate Table 4 ![![107, 0, 0], ![-38, 1, 0]]
  ![-8576657, -61589, -209807] ![![4, 0, 0], ![28, -1, 1]] where
    su := ![![428, 0, 0], ![-152, 4, 0]]
    hsu := by decide
    w := ![![-34306628, -246356, -839228], ![-234071480, -1680868, -5725988]]
    hw := by decide
    g := ![![![-9, 243, 371], ![-13, 0, 0]], ![![-22, -222, -131], ![20, 0, 0]]]
    h := ![![![-628509265, 16802400, -16305], ![-1769524071, 767414, 0]], ![![-4288270382, 114641395, -111243], ![-12073326658, 5235752, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {4} * I107N1 =  Ideal.span {B.equivFun.symm ![-8576657, -61589, -209807]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 4 ![![109, 0, 0], ![-35, 1, 0]]
  ![347063, -561532, 143447] ![![4, 0, 0], ![28, 0, 1]] where
    su := ![![436, 0, 0], ![-140, 4, 0]]
    hsu := by decide
    w := ![![1388252, -2246128, 573788], ![-5480368, 9021280, -1517748]]
    hw := by decide
    g := ![![![-78322718409, -27613217639, 40469181908], ![-538141733347, 0, 0]], ![![24727630823, 8717897717, -12776714226], ![169899237261, -15, 0]]]
    h := ![![![52663197, -1624388, 8061], ![163998326, -367601, 0]], ![![-207924058, 6413796, -30115], ![-647495778, 1451549, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {4} * I109N1 =  Ideal.span {B.equivFun.symm ![347063, -561532, 143447]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E109RS1 
