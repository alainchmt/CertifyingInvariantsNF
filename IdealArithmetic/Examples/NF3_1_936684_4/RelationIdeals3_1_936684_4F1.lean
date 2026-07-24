import IdealArithmetic.Examples.NF3_1_936684_4.PrimesBelow3_1_936684_4F1
import IdealArithmetic.Examples.NF3_1_936684_4.ClassGroupData3_1_936684_4

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 50 ![![37, 0, 0], ![-12, 1, 0]]
  ![-250, -9, 3] ![![50, 0, 0], ![-46, -4, 1]] where
    su := ![![1850, 0, 0], ![-600, 50, 0]]
    hsu := by decide
    w := ![![-12500, -450, 150], ![4150, 700, -100]]
    hw := by decide
    g := ![![![-6322, -804, 16], ![5939, 1684, 0]], ![![1989, 251, -6], ![-1764, -516, 0]]]
    h := ![![![-156778, 14253, -99], ![-483378, 3666, 0]], ![![51971, -4715, 32], ![160237, -1186, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {50} * I37N1 =  Ideal.span {B.equivFun.symm ![-250, -9, 3]} * (J0 ^ 2*J1^ 0*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0J2_2 E37RS1 


noncomputable def E43RS1 : RelationCertificate Table 10 ![![43, 0, 0], ![-5, 1, 0]]
  ![60, 21, 2] ![![10, 0, 0], ![-52, -4, 1]] where
    su := ![![430, 0, 0], ![-50, 10, 0]]
    hsu := by decide
    w := ![![600, 210, 20], ![1430, 460, 40]]
    hw := by decide
    g := ![![![262, 116, 45], ![-1189, -184, 0]], ![![16, -10, -6], ![145, 21, 0]]]
    h := ![![![3140, -632, 1], ![26992, -41, 0]], ![![7486, -1510, 3], ![64351, -125, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {10} * I43N1 =  Ideal.span {B.equivFun.symm ![60, 21, 2]} * (J0 ^ 0*J1^ 1*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1J2_2 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 50 ![![47, 0, 0], ![16, 1, 0]]
  ![-100, -2, 1] ![![50, 0, 0], ![-44, -5, 1]] where
    su := ![![2350, 0, 0], ![800, 50, 0]]
    hsu := by decide
    w := ![![-5000, -100, 50], ![1950, 350, -50]]
    hw := by decide
    g := ![![![-53019820, -6086422, 406246], ![47274223, 13517305, 0]], ![![-16921261, -1942480, 129653], ![15087594, 4314049, 0]]]
    h := ![![![-124, -24, -1], ![358, 48, 0]], ![![25, -14, -1], ![-71, 46, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {50} * I47N1 =  Ideal.span {B.equivFun.symm ![-100, -2, 1]} * (J0 ^ 1*J1^ 2*J2^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2J2_1 E47RS1 


noncomputable def E59RS0 : RelationCertificate Table 50 ![![59, 0, 0], ![17, 1, 0]]
  ![50, 13, 1] ![![50, 0, 0], ![752, 80, -13]] where
    su := ![![2950, 0, 0], ![850, 50, 0]]
    hsu := by decide
    w := ![![2500, 650, 50], ![6450, 1750, 50]]
    hw := by decide
    g := ![![![-582, 136, 12], ![-379, -69, 0]], ![![-662, -13, 12], ![-77, -20, 0]]]
    h := ![![![70, 4, 0], ![-240, 1, 0]], ![![218, 13, 0], ![-749, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {50} * I59N0 =  Ideal.span {B.equivFun.symm ![50, 13, 1]} * (J0 ^ 1*J1^ 2*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2J2_2 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 50 ![![59, 0, 0], ![21, 1, 0]]
  ![-750, -249, -23] ![![50, 0, 0], ![752, 80, -13]] where
    su := ![![2950, 0, 0], ![1050, 50, 0]]
    hsu := by decide
    w := ![![-37500, -12450, -1150], ![-75050, -25250, -2350]]
    hw := by decide
    g := ![![![-149, -1268, -9], ![2641, 434, 0]], ![![38, -463, -5], ![979, 162, 0]]]
    h := ![![![-408966, -23691, -201], ![1148964, 11836, 0]], ![![-818567, -47391, -401], ![2299712, 23612, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {50} * I59N1 =  Ideal.span {B.equivFun.symm ![-750, -249, -23]} * (J0 ^ 1*J1^ 2*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2J2_2 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 50 ![![61, 0, 0], ![22, 1, 0]]
  ![-50, -8, 1] ![![50, 0, 0], ![-74, -5, 1]] where
    su := ![![3050, 0, 0], ![1100, 50, 0]]
    hsu := by decide
    w := ![![-2500, -400, 50], ![-850, 100, 0]]
    hw := by decide
    g := ![![![-11269574, 637164, 179987], ![16618967, 5123664, 0]], ![![-107061676, 6053037, 1709887], ![157880184, 48674907, 0]]]
    h := ![![![-342, -38, -1], ![946, 62, 0]], ![![-155, -29, -1], ![429, 61, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {50} * I61N1 =  Ideal.span {B.equivFun.symm ![-50, -8, 1]} * (J0 ^ 2*J1^ 1*J2^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1J2_1 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 50 ![![67, 0, 0], ![31, 1, 0]]
  ![300, -17, -1] ![![50, 0, 0], ![-594, -40, 11]] where
    su := ![![3350, 0, 0], ![1550, 50, 0]]
    hsu := by decide
    w := ![![15000, -850, -50], ![-229650, -18100, 3650]]
    hw := by decide
    g := ![![![610, 149, 32], ![-369, -64, 0]], ![![367, 78, 14], ![-167, -30, 0]]]
    h := ![![![1486, 48, 0], ![-3202, -1, 0]], ![![-23654, -924, -4], ![50975, 341, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {50} * I67N1 =  Ideal.span {B.equivFun.symm ![300, -17, -1]} * (J0 ^ 2*J1^ 1*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1J2_2 E67RS1 


noncomputable def E73RS1 : RelationCertificate Table 10 ![![73, 0, 0], ![23, 1, 0]]
  ![-20, -8, -1] ![![10, 0, 0], ![2, 1, 0]] where
    su := ![![730, 0, 0], ![230, 10, 0]]
    hsu := by decide
    w := ![![-200, -80, -10], ![-390, -120, -10]]
    hw := by decide
    g := ![![![6173, -322393, -162745], ![-30997, 1627454, 0]], ![![679721, -35345901, -17842882], ![-3398637, 178428821, 0]]]
    h := ![![![-2604, -136, -1], ![8264, 72, 0]], ![![-5064, -266, -2], ![16071, 145, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {10} * I73N1 =  Ideal.span {B.equivFun.symm ![-20, -8, -1]} * (J0 ^ 0*J1^ 1*J2^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1J2_1 E73RS1 
