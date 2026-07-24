import IdealArithmetic.Examples.NF3_1_933107_3.PrimesBelow3_1_933107_3F5
import IdealArithmetic.Examples.NF3_1_933107_3.ClassGroupData3_1_933107_3

set_option linter.all false

noncomputable section


noncomputable def E263RS0 : RelationCertificate Table 4 ![![263, 0, 0], ![11, 1, 0]]
  ![11, 1, 0] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![1052, 0, 0], ![44, 4, 0]]
    hsu := by decide
    w := ![![44, 4, 0], ![24, 12, 8]]
    hw := by decide
    g := ![![![-22097850, 32488254, -3073213], ![-2926861, 0, 4097618]], ![![-998262, 1467641, -138831], ![-132216, 0, 185108]]]
    h := ![![![-180, -900, -720], ![1, 23670, 0]], ![![-102, -483, -386], ![132, 12690, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N0 : Ideal.span {4} * I263N0 =  Ideal.span {B.equivFun.symm ![11, 1, 0]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E263RS0 


noncomputable def E263RS1 : RelationCertificate Table 10 ![![263, 0, 0], ![110, 1, 0]]
  ![2721, -3, 88] ![![10, 0, 0], ![2, 1, 0]] where
    su := ![![2630, 0, 0], ![1100, 10, 0]]
    hsu := by decide
    w := ![![27210, -30, 880], ![7460, -10, 240]]
    hw := by decide
    g := ![![![2254439462833, 1127229565752, 9468667124908], ![563610849149, -11835834773868, 2313960]], ![![953013033857, 476510674170, 4002663780539], ![238253674197, -5003330092488, 978174]]]
    h := ![![![-955, -62024, -4552], ![-413, 149658, 0]], ![![-282, -17005, -1248], ![-65, 41031, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N1 : Ideal.span {10} * I263N1 =  Ideal.span {B.equivFun.symm ![2721, -3, 88]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E263RS1 


noncomputable def E263RS2 : RelationCertificate Table 25 ![![263, 0, 0], ![-121, 1, 0]]
  ![-214, 2, -7] ![![25, 0, 0], ![12, 1, 0]] where
    su := ![![6575, 0, 0], ![-3025, 25, 0]]
    hsu := by decide
    w := ![![-5350, 50, -175], ![-2725, 25, -75]]
    hw := by decide
    g := ![![![-47154850, -355134951, -259351665], ![-36839723, 810473953, 0]], ![![21516609, 162046976, 118341360], ![16809857, -369816750, 0]]]
    h := ![![![-1677198, 138772514, -9100161], ![1299444, 299167792, 0]], ![![-854215, 70683139, -4635125], ![661992, 152379734, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N2 : Ideal.span {25} * I263N2 =  Ideal.span {B.equivFun.symm ![-214, 2, -7]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E263RS2 
