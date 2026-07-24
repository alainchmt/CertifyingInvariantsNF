import IdealArithmetic.Examples.NF3_3_149769_2.PrimesBelow3_3_149769_2F0
import IdealArithmetic.Examples.NF3_3_149769_2.ClassGroupData3_3_149769_2

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 169 ![![3, 0, 0], ![-1, 1, 0]]
  ![-728, -51, 8] ![![169, 0, 0], ![-57, 1, 0]] where
    su := ![![507, 0, 0], ![-169, 169, 0]]
    hsu := by decide
    w := ![![-123032, -8619, 1352], ![45968, 3211, -507]]
    hw := by decide
    g := ![![![2011, 1097614, -19257], ![5964, 3254434, 0]], ![![2856, 1588653, -27872], ![8464, 4710365, 0]]]
    h := ![![![-528, 293, -22], ![-856, 74, 0]], ![![198, -109, 7], ![322, -24, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {169} * I3N0 =  Ideal.span {B.equivFun.symm ![-728, -51, 8]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS0 


noncomputable def E13RS0 : RelationCertificate Table 13 ![![13, 0, 0], ![0, 1, 0]]
  ![-91, -8, 1] ![![13, 0, 0], ![-5, 1, 0]] where
    su := ![![169, 0, 0], ![0, 13, 0]]
    hsu := by decide
    w := ![![-1183, -104, 13], ![1014, 78, -13]]
    hw := by decide
    g := ![![![-5, 248, -50], ![23, 652, 0]], ![![27, 686, -138], ![53, 1793, 0]]]
    h := ![![![-7, -1, 0], ![5, 1, 0]], ![![6, 0, 0], ![6, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {13} * I13N0 =  Ideal.span {B.equivFun.symm ![-91, -8, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 13 ![![13, 0, 0], ![5, 1, 0]]
  ![78, 8, -1] ![![13, 0, 0], ![-5, 1, 0]] where
    su := ![![169, 0, 0], ![65, 13, 0]]
    hsu := by decide
    w := ![![1014, 104, -13], ![-949, -91, 13]]
    hw := by decide
    g := ![![![-872, -33612, 6757], ![-2249, -87840, 0]], ![![-559, -21848, 4392], ![-1455, -57096, 0]]]
    h := ![![![2926, 710, 25], ![-7592, -326, 0]], ![![-2751, -670, -24], ![7138, 313, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {13} * I13N1 =  Ideal.span {B.equivFun.symm ![78, 8, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 1 ![![13, 0, 0], ![-5, 1, 0]]
  ![1, 0, 0] ![![13, 0, 0], ![-5, 1, 0]] where
    su := ![![13, 0, 0], ![-5, 1, 0]]
    hsu := by decide
    w := ![![13, 0, 0], ![-5, 1, 0]]
    hw := by decide
    g := ![![![51, -10, 0], ![130, 0, 0]], ![![-15, 8, -1], ![-38, 13, 0]]]
    h := ![![![51, -10, 0], ![130, 0, 0]], ![![-15, 8, -1], ![-38, 13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {1} * I13N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS2 
