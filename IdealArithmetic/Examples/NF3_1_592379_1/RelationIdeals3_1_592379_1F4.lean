import IdealArithmetic.Examples.NF3_1_592379_1.PrimesBelow3_1_592379_1F4
import IdealArithmetic.Examples.NF3_1_592379_1.ClassGroupData3_1_592379_1

set_option linter.all false

noncomputable section


noncomputable def E197RS0 : RelationCertificate Table 4 ![![197, 0, 0], ![35, 1, 0]]
  ![-23, 15, -1] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![788, 0, 0], ![140, 4, 0]]
    hsu := by decide
    w := ![![-92, 60, -4], ![-132, 56, 12]]
    hw := by decide
    g := ![![![-110584, 1099909, 577406], ![219687, -2309683, 0]], ![![-20069, 199574, 104768], ![39862, -419083, 0]]]
    h := ![![![-2284, -100, -1], ![12855, 196, 0]], ![![-3204, -127, -1], ![18033, 200, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N0 : Ideal.span {4} * I197N0 =  Ideal.span {B.equivFun.symm ![-23, 15, -1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E197RS0 


noncomputable def E197RS1 : RelationCertificate Table 8 ![![197, 0, 0], ![-18, 1, 0]]
  ![1455, 21, 29] ![![8, 0, 0], ![-2, 1, 0]] where
    su := ![![1576, 0, 0], ![-144, 8, 0]]
    hsu := by decide
    w := ![![11640, 168, 232], ![-416, -8, -8]]
    hw := by decide
    g := ![![![29, 631, -323], ![75, 2592, 0]], ![![-2, -55, 28], ![-6, -225, 0]]]
    h := ![![![1749, -94, 0], ![19061, 29, 0]], ![![-56, 21, -1], ![-610, 196, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {8} * I197N1 =  Ideal.span {B.equivFun.symm ![1455, 21, 29]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E197RS1 


noncomputable def E199RS1 : RelationCertificate Table 56 ![![199, 0, 0], ![-93, 1, 0]]
  ![29, -25, -1] ![![56, 0, 0], ![-26, 1, 0]] where
    su := ![![11144, 0, 0], ![-5208, 56, 0]]
    hsu := by decide
    w := ![![1624, -1400, -56], ![-840, 728, 0]]
    hw := by decide
    g := ![![![-29341, -4303646, 165568], ![-63172, -9271821, 0]], ![![13884, 2032903, -78209], ![29893, 4379710, 0]]]
    h := ![![![203429, -2467, 3], ![435294, -598, 0]], ![![-105177, 1317, -2], ![-225056, 398, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {56} * I199N1 =  Ideal.span {B.equivFun.symm ![29, -25, -1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E199RS1 
