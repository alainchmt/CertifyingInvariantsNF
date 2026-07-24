import IdealArithmetic.Examples.NF3_1_884199_1.PrimesBelow3_1_884199_1F4
import IdealArithmetic.Examples.NF3_1_884199_1.ClassGroupData3_1_884199_1

set_option linter.all false

noncomputable section


noncomputable def E211RS1 : RelationCertificate Table 25 ![![211, 0, 0], ![-9, 1, 0]]
  ![-48, 8, -1] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![5275, 0, 0], ![-225, 25, 0]]
    hsu := by decide
    w := ![![-1200, 200, -25], ![5050, 425, -150]]
    hw := by decide
    g := ![![![40, 16, 5], ![-31, 0, 0]], ![![6, 1, 0], ![3, 0, 0]]]
    h := ![![![-714, 82, -1], ![-16734, 70, 0]], ![![3052, -331, -3], ![71530, 209, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {25} * I211N1 =  Ideal.span {B.equivFun.symm ![-48, 8, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E211RS1 


noncomputable def E223RS1 : RelationCertificate Table 25 ![![223, 0, 0], ![45, 1, 0]]
  ![187, 48, 9] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![5575, 0, 0], ![1125, 25, 0]]
    hsu := by decide
    w := ![![4675, 1200, 225], ![650, 150, 25]]
    hw := by decide
    g := ![![![-79, 9, -1], ![124, 0, 0]], ![![10, 4, -1], ![43, 0, 0]]]
    h := ![![![164179, 3832, 12], ![-813594, -889, 0]], ![![22802, 522, 1], ![-112996, -74, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N1 : Ideal.span {25} * I223N1 =  Ideal.span {B.equivFun.symm ![187, 48, 9]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E223RS1 


noncomputable def E227RS1 : RelationCertificate Table 125 ![![227, 0, 0], ![-50, 1, 0]]
  ![8205, 2105, 398] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![28375, 0, 0], ![-6250, 125, 0]]
    hsu := by decide
    w := ![![1025625, 263125, 49750], ![-3434000, -881125, -166625]]
    hw := by decide
    g := ![![![-615, 15, 16], ![263, 0, 0]], ![![209, 23, -5], ![54, 0, 0]]]
    h := ![![![56621715, -1177982, 2791], ![257062422, -211053, 0]], ![![-189580836, 3944155, -9347], ![-860696446, 706812, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {125} * I227N1 =  Ideal.span {B.equivFun.symm ![8205, 2105, 398]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E227RS1 


noncomputable def E229RS1 : RelationCertificate Table 25 ![![229, 0, 0], ![-35, 1, 0]]
  ![-1415, 0, 18] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![5725, 0, 0], ![-875, 25, 0]]
    hsu := by decide
    w := ![![-35375, 0, 450], ![20000, 3075, -875]]
    hw := by decide
    g := ![![![2401, 1080, 378], ![-2772, 0, 0]], ![![-189, -89, -32], ![242, 0, 0]]]
    h := ![![![-257505, 7392, -3], ![-1684778, 235, 0]], ![![145480, -4135, -2], ![951832, 141, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {25} * I229N1 =  Ideal.span {B.equivFun.symm ![-1415, 0, 18]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E229RS1 


noncomputable def E239RS0 : RelationCertificate Table 125 ![![239, 0, 0], ![30, 1, 0]]
  ![-381817, -27743, 10456] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![29875, 0, 0], ![3750, 125, 0]]
    hsu := by decide
    w := ![![-47727125, -3467875, 1307000], ![-85710500, -4511875, 2000875]]
    hw := by decide
    g := ![![![34436281, 6975201, 2132060], ![-16146281, 0, 0]], ![![6608488, 1338585, 409150], ![-3098459, 0, 0]]]
    h := ![![![-363083, -12380, 23], ![2879834, 1653, 0]], ![![-651896, -22188, 28], ![5170582, 3105, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N0 : Ideal.span {125} * I239N0 =  Ideal.span {B.equivFun.symm ![-381817, -27743, 10456]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E239RS0 


noncomputable def E239RS1 : RelationCertificate Table 25 ![![239, 0, 0], ![33, 1, 0]]
  ![1857935, 9675, -25587] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![5975, 0, 0], ![825, 25, 0]]
    hsu := by decide
    w := ![![46448375, 241875, -639675], ![-20968625, -3649425, 1003250]]
    hw := by decide
    g := ![![![3606052525, 1630067904, 572262615], ![-4211496432, 0, 0]], ![![737279774, 333277472, 117002632], ![-861066487, 0, 0]]]
    h := ![![![-44409032, -1341480, 285], ![321685351, -31234, 0]], ![![19911608, 600850, -11], ![-144233729, 14253, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N1 : Ideal.span {25} * I239N1 =  Ideal.span {B.equivFun.symm ![1857935, 9675, -25587]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E239RS1 


noncomputable def E239RS2 : RelationCertificate Table 125 ![![239, 0, 0], ![-64, 1, 0]]
  ![-2209512, -137463, 55849] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![29875, 0, 0], ![-8000, 125, 0]]
    hsu := by decide
    w := ![![-276189000, -17182875, 6981125], ![-445287250, -19583250, 9616625]]
    hw := by decide
    g := ![![![943018487, 191011745, 58385350], ![-442159326, 0, 0]], ![![-189925342, -38470038, -11758901], ![89051682, 0, 0]]]
    h := ![![![-19670564504, 325259552, -852514], ![-73457229796, 67935565, 0]], ![![-31715042662, 524418459, -1374526], ![-118435806780, 109529549, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N2 : Ideal.span {125} * I239N2 =  Ideal.span {B.equivFun.symm ![-2209512, -137463, 55849]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E239RS2 
