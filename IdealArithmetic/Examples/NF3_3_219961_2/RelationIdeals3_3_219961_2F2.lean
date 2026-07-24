import IdealArithmetic.Examples.NF3_3_219961_2.PrimesBelow3_3_219961_2F2
import IdealArithmetic.Examples.NF3_3_219961_2.ClassGroupData3_3_219961_2

set_option linter.all false

noncomputable section


noncomputable def E101RS0 : RelationCertificate Table 4 ![![101, 0, 0], ![-48, 1, 0]]
  ![170, -3, -9] ![![4, 0, 0], ![-25, -1, 1]] where
    su := ![![404, 0, 0], ![-192, 4, 0]]
    hsu := by decide
    w := ![![680, -12, -36], ![-2996, -200, 56]]
    hw := by decide
    g := ![![![568896, 1118139, 306414], ![-3758381, -633080, 0]], ![![-268453, -527706, -144607], ![1773756, 298775, 0]]]
    h := ![![![4834, -90, -1], ![10168, 23, 0]], ![![-21193, 513, -6], ![-44578, 155, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {4} * I101N0 =  Ideal.span {B.equivFun.symm ![170, -3, -9]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 4 ![![101, 0, 0], ![-39, 1, 0]]
  ![-2370, -85, 73] ![![4, 0, 0], ![-25, -1, 1]] where
    su := ![![404, 0, 0], ![-156, 4, 0]]
    hsu := by decide
    w := ![![-9480, -340, 292], ![32460, 1192, -1008]]
    hw := by decide
    g := ![![![-577526, -1135035, -311114], ![3815607, 642770, 0]], ![![219142, 430638, 118038], ![-1447629, -243865, 0]]]
    h := ![![![-1056, -313591, 33013], ![-2674, -833560, 0]], ![![3678, 1073729, -113036], ![9317, 2854096, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {4} * I101N1 =  Ideal.span {B.equivFun.symm ![-2370, -85, 73]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS1 


noncomputable def E101RS2 : RelationCertificate Table 4 ![![101, 0, 0], ![-15, 1, 0]]
  ![-182, -23, 11] ![![4, 0, 0], ![-25, -1, 1]] where
    su := ![![404, 0, 0], ![-60, 4, 0]]
    hsu := by decide
    w := ![![-728, -92, 44], ![-1036, -128, 64]]
    hw := by decide
    g := ![![![261, 444, 127], ![-1603, -252, 0]], ![![-12, -64, -20], ![245, 37, 0]]]
    h := ![![![-2692, 183, -1], ![-18114, 28, 0]], ![![-3824, 269, -4], ![-25731, 105, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {4} * I101N2 =  Ideal.span {B.equivFun.symm ![-182, -23, 11]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS2 
