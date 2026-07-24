import IdealArithmetic.Examples.NF3_1_688076_2.PrimesBelow3_1_688076_2F1
import IdealArithmetic.Examples.NF3_1_688076_2.ClassGroupData3_1_688076_2

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 7 ![![37, 0, 0], ![18, 1, 0]]
  ![59, -14, 3] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![259, 0, 0], ![126, 7, 0]]
    hsu := by decide
    w := ![![413, -98, 21], ![-595, 133, -28]]
    hw := by decide
    g := ![![![3721, -3728, 7757], ![-1063, -27150, 0]], ![![1986, -1989, 4137], ![-563, -14480, 0]]]
    h := ![![![-8545, -248513, -27645], ![-10845, 511434, 0]], ![![12281, 357886, 39812], ![15669, -736524, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {7} * I37N1 =  Ideal.span {B.equivFun.symm ![59, -14, 3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 11 ![![41, 0, 0], ![-19, 1, 0]]
  ![73, 0, -2] ![![11, 0, 0], ![-1, 1, 0]] where
    su := ![![451, 0, 0], ![-209, 11, 0]]
    hsu := by decide
    w := ![![803, 0, -22], ![275, 33, 0]]
    hw := by decide
    g := ![![![59, -50, 96], ![-3, -525, 0]], ![![-29, 23, -44], ![6, 240, 0]]]
    h := ![![![14319, -420154, 44270], ![-16870, -907536, 0]], ![![4890, -143272, 15096], ![-5737, -309468, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {11} * I41N1 =  Ideal.span {B.equivFun.symm ![73, 0, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E41RS1 


noncomputable def E53RS1 : RelationCertificate Table 11 ![![53, 0, 0], ![13, 1, 0]]
  ![-31, 0, 1] ![![11, 0, 0], ![-1, 1, 0]] where
    su := ![![583, 0, 0], ![143, 11, 0]]
    hsu := by decide
    w := ![![-341, 0, 11], ![-143, -11, 0]]
    hw := by decide
    g := ![![![-6, 7, -17], ![10, 94, 0]], ![![-2, 2, -6], ![10, 33, 0]]]
    h := ![![![14167, 207762, 31985], ![7440, -847602, 0]], ![![5929, 86989, 13392], ![3126, -354888, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {11} * I53N1 =  Ideal.span {B.equivFun.symm ![-31, 0, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E53RS1 


noncomputable def E61RS0 : RelationCertificate Table 77 ![![61, 0, 0], ![7, 1, 0]]
  ![-157, 0, 4] ![![77, 0, 0], ![-1, 1, 0]] where
    su := ![![4697, 0, 0], ![539, 77, 0]]
    hsu := by decide
    w := ![![-12089, 0, 308], ![-539, -77, 0]]
    hw := by decide
    g := ![![![-6741928, 6741927, -13488404], ![175189, 519303552, 0]], ![![-1084530, 1084530, -2169792], ![28181, 83536992, 0]]]
    h := ![![![2098, 15125, 4324], ![535, -131880, 0]], ![![89, 671, 192], ![60, -5856, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {77} * I61N0 =  Ideal.span {B.equivFun.symm ![-157, 0, 4]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 77 ![![61, 0, 0], ![-5, 1, 0]]
  ![-37, 0, -2] ![![77, 0, 0], ![-1, 1, 0]] where
    su := ![![4697, 0, 0], ![-385, 77, 0]]
    hsu := by decide
    w := ![![-2849, 0, -154], ![385, -77, 0]]
    hw := by decide
    g := ![![![-596285, 596284, -1192972], ![15559, 45929423, 0]], ![![0, 0, 0], ![-1, 0, 0]]]
    h := ![![![130, -655, 262], ![-5, -7992, 0]], ![![-13, 89, -36], ![60, 1098, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {77} * I61N1 =  Ideal.span {B.equivFun.symm ![-37, 0, -2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 77 ![![61, 0, 0], ![-3, 1, 0]]
  ![57, 0, 1] ![![77, 0, 0], ![-1, 1, 0]] where
    su := ![![4697, 0, 0], ![-231, 77, 0]]
    hsu := by decide
    w := ![![4389, 0, 77], ![-231, 77, 0]]
    hw := by decide
    g := ![![![-555, 556, -1113], ![37, 42850, 0]], ![![20, -20, 40], ![1, -1540, 0]]]
    h := ![![![-147, 448, -299], ![32, 9120, 0]], ![![8, -24, 16], ![1, -488, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {77} * I61N2 =  Ideal.span {B.equivFun.symm ![57, 0, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E61RS2 


noncomputable def E67RS0 : RelationCertificate Table 11 ![![67, 0, 0], ![28, 1, 0]]
  ![48, -11, 2] ![![11, 0, 0], ![-1, 1, 0]] where
    su := ![![737, 0, 0], ![308, 11, 0]]
    hsu := by decide
    w := ![![528, -121, 22], ![-407, 99, -22]]
    hw := by decide
    g := ![![![363049, -363054, 738110], ![-66000, -4059603, 0]], ![![153625, -153628, 312334], ![-27924, -1717836, 0]]]
    h := ![![![117, 5149, 368], ![162, -12327, 0]], ![![-102, -3974, -284], ![-97, 9513, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {11} * I67N0 =  Ideal.span {B.equivFun.symm ![48, -11, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 847 ![![67, 0, 0], ![-21, 1, 0]]
  ![-290, 77, -24] ![![847, 0, 0], ![76, 1, 0]] where
    su := ![![56749, 0, 0], ![-17787, 847, 0]]
    hsu := by decide
    w := ![![-245630, 65219, -20328], ![-17787, 5082, -1694]]
    hw := by decide
    g := ![![![1107851083, 85563218202, 2251669864], ![200425263, -953582187399, 0]], ![![-344545707, -26610467076, -700277386], ![-62332357, 296567472970, 0]]]
    h := ![![![-10335049, 264206310, -25172716], ![7182761, 843285974, 0]], ![![-748683, 19139718, -1823570], ![520374, 61089594, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {847} * I67N1 =  Ideal.span {B.equivFun.symm ![-290, 77, -24]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 49 ![![67, 0, 0], ![-8, 1, 0]]
  ![-53, 14, -4] ![![49, 0, 0], ![6, 1, 0]] where
    su := ![![3283, 0, 0], ![-392, 49, 0]]
    hsu := by decide
    w := ![![-2597, 686, -196], ![392, -49, 0]]
    hw := by decide
    g := ![![![305, 1906, 636], ![100, -15580, 0]], ![![-35, -210, -70], ![-1, 1715, 0]]]
    h := ![![![63730, -524338, 131142], ![-15412, -4393259, 0]], ![![-9563, 78709, -19686], ![2344, 659481, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {49} * I67N2 =  Ideal.span {B.equivFun.symm ![-53, 14, -4]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E67RS2 


noncomputable def E71RS1 : RelationCertificate Table 49 ![![71, 0, 0], ![35, 1, 0]]
  ![-3, -14, -3] ![![49, 0, 0], ![6, 1, 0]] where
    su := ![![3479, 0, 0], ![1715, 49, 0]]
    hsu := by decide
    w := ![![-147, -686, -147], ![490, -147, -49]]
    hw := by decide
    g := ![![![31, 188, 63], ![15, -1541, 0]], ![![12, 95, 32], ![36, -783, 0]]]
    h := ![![![26, 2187, 125], ![74, -4439, 0]], ![![-144, -7855, -449], ![-163, 15939, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {49} * I71N1 =  Ideal.span {B.equivFun.symm ![-3, -14, -3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 847 ![![73, 0, 0], ![24, 1, 0]]
  ![-510, 77, -13] ![![847, 0, 0], ![76, 1, 0]] where
    su := ![![61831, 0, 0], ![20328, 847, 0]]
    hsu := by decide
    w := ![![-431970, 65219, -11011], ![-36421, 5082, -847]]
    hw := by decide
    g := ![![![16075, 1244914, 32761], ![3402, -13874284, 0]], ![![5498, 429588, 11305], ![1721, -4787668, 0]]]
    h := ![![![10629, 317475, 26465], ![7898, -965979, 0]], ![![893, 26763, 2231], ![675, -81432, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {847} * I73N1 =  Ideal.span {B.equivFun.symm ![-510, 77, -13]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 121 ![![79, 0, 0], ![-38, 1, 0]]
  ![10, -11, 5] ![![121, 0, 0], ![-45, 1, 0]] where
    su := ![![9559, 0, 0], ![-4598, 121, 0]]
    hsu := by decide
    w := ![![1210, -1331, 605], ![-1331, 605, -242]]
    hw := by decide
    g := ![![![430, -23781, 1057], ![-265, -63950, 0]], ![![-156, 10551, -469], ![211, 28375, 0]]]
    h := ![![![-21170, 1289404, -67881], ![26549, 2681302, 0]], ![![22781, -1385766, 72954], ![-28473, -2881684, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {121} * I79N1 =  Ideal.span {B.equivFun.symm ![10, -11, 5]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E79RS1 
