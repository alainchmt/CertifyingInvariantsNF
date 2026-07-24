import IdealArithmetic.Examples.NF3_1_197127_1.PrimesBelow3_1_197127_1F2
import IdealArithmetic.Examples.NF3_1_197127_1.ClassGroupData3_1_197127_1

set_option linter.all false

noncomputable section


noncomputable def E97RS1 : RelationCertificate Table 125 ![![97, 0, 0], ![-25, 1, 0]]
  ![78, 13, 12] ![![125, 0, 0], ![27, 1, 0]] where
    su := ![![12125, 0, 0], ![-3125, 125, 0]]
    hsu := by decide
    w := ![![9750, 1625, 1500], ![3125, 500, 375]]
    hw := by decide
    g := ![![![-11281522, 293804773, 33900471], ![-86272, -1412519628, 0]], ![![1743038, -45394730, -5237841], ![13467, 218243376, 0]]]
    h := ![![![-961, -25141, 2901], ![20, -93795, 0]], ![![-302, -8060, 930], ![30, -30069, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {125} * I97N1 =  Ideal.span {B.equivFun.symm ![78, 13, 12]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E97RS1 


noncomputable def E107RS1 : RelationCertificate Table 5 ![![107, 0, 0], ![17, 1, 0]]
  ![-1, -1, 1] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![535, 0, 0], ![85, 5, 0]]
    hsu := by decide
    w := ![![-5, -5, 5], ![85, 5, 0]]
    hw := by decide
    g := ![![![-110, 125, 361], ![-17, -602, 0]], ![![-20, 20, 60], ![1, -100, 0]]]
    h := ![![![14, -390, -73], ![65, 2604, 0]], ![![-420, 6720, 1260], ![1, -44940, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {5} * I107N1 =  Ideal.span {B.equivFun.symm ![-1, -1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 25 ![![109, 0, 0], ![-27, 1, 0]]
  ![-102, -17, -8] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![2725, 0, 0], ![-675, 25, 0]]
    hsu := by decide
    w := ![![-2550, -425, -200], ![-875, -175, -75]]
    hw := by decide
    g := ![![![3110121, -3124986, -9360100], ![123822, 78000835, 0]], ![![-757838, 761459, 2280758], ![-30161, -19006317, 0]]]
    h := ![![![-158, -5023, 538], ![90, -19550, 0]], ![![-43, -1709, 183], ![74, -6650, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {25} * I109N1 =  Ideal.span {B.equivFun.symm ![-102, -17, -8]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 125 ![![113, 0, 0], ![26, 1, 0]]
  ![-186, -31, -19] ![![125, 0, 0], ![27, 1, 0]] where
    su := ![![14125, 0, 0], ![3250, 125, 0]]
    hsu := by decide
    w := ![![-23250, -3875, -2375], ![-6625, -1125, -625]]
    hw := by decide
    g := ![![![4522, -118285, -13648], ![122, 568672, 0]], ![![1067, -28263, -3261], ![92, 135876, 0]]]
    h := ![![![-7711, 193085, 23170], ![-61, -872743, 0]], ![![-2200, 55017, 6602], ![-5, -248677, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {125} * I113N1 =  Ideal.span {B.equivFun.symm ![-186, -31, -19]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E113RS1 
