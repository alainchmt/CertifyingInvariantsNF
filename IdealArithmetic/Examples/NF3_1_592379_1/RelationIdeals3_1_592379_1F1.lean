import IdealArithmetic.Examples.NF3_1_592379_1.PrimesBelow3_1_592379_1F1
import IdealArithmetic.Examples.NF3_1_592379_1.ClassGroupData3_1_592379_1

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 112 ![![37, 0, 0], ![5, 1, 0]]
  ![-5683, -81, -113] ![![112, 0, 0], ![30, 1, 0]] where
    su := ![![4144, 0, 0], ![560, 112, 0]]
    hsu := by decide
    w := ![![-636496, -9072, -12656], ![-180208, -2576, -3584]]
    hw := by decide
    g := ![![![321336497, -144001598145, -4800410312], ![-1199656258, 537645954951, 0]], ![![40528518, -18162192400, -605451445], ![-151306467, 67810561842, 0]]]
    h := ![![![-10434, -2103, -12], ![76075, 331, 0]], ![![-2962, -600, -4], ![21597, 116, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {112} * I37N0 =  Ideal.span {B.equivFun.symm ![-5683, -81, -113]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E37RS0 


noncomputable def E37RS1 : RelationCertificate Table 28 ![![37, 0, 0], ![-5, 1, 0]]
  ![27, -3, 1] ![![28, 0, 0], ![2, 1, 0]] where
    su := ![![1036, 0, 0], ![-140, 28, 0]]
    hsu := by decide
    w := ![![756, -84, 28], ![140, -28, 0]]
    hw := by decide
    g := ![![![193493, -76236104, -38166425], ![-2708886, 1068659901, 0]], ![![-27900, 10992230, 5503090], ![390599, -154086520, 0]]]
    h := ![![![66, -13, 0], ![483, 1, 0]], ![![20, -4, 0], ![147, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {28} * I37N1 =  Ideal.span {B.equivFun.symm ![27, -3, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 8 ![![41, 0, 0], ![-17, 1, 0]]
  ![55, -27, -3] ![![8, 0, 0], ![-2, 1, 0]] where
    su := ![![328, 0, 0], ![-136, 8, 0]]
    hsu := by decide
    w := ![![440, -216, -24], ![-368, 256, -24]]
    hw := by decide
    g := ![![![2895, 133917, -67990], ![16024, 543743, 0]], ![![-1339, -58797, 29848], ![-7013, -238718, 0]]]
    h := ![![![8775, -569, 3], ![21160, -126, 0]], ![![-7336, 499, -4], ![-17690, 161, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {8} * I41N1 =  Ideal.span {B.equivFun.symm ![55, -27, -3]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E41RS1 


noncomputable def E43RS0 : RelationCertificate Table 8 ![![43, 0, 0], ![0, 1, 0]]
  ![-43, -1, -1] ![![8, 0, 0], ![-2, 1, 0]] where
    su := ![![344, 0, 0], ![0, 8, 0]]
    hsu := by decide
    w := ![![-344, -8, -8], ![0, 8, 0]]
    hw := by decide
    g := ![![![-1, 0, 0], ![-1, -1, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-1, 0, 0], ![-1, -1, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {8} * I43N0 =  Ideal.span {B.equivFun.symm ![-43, -1, -1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E43RS0 


noncomputable def E53RS1 : RelationCertificate Table 14 ![![53, 0, 0], ![22, 1, 0]]
  ![-17, 5, 3] ![![14, 0, 0], ![2, 1, 0]] where
    su := ![![742, 0, 0], ![308, 14, 0]]
    hsu := by decide
    w := ![![-238, 70, 42], ![224, -154, 14]]
    hw := by decide
    g := ![![![-7129, 726146, 364891], ![50855, -5108436, 0]], ![![-2966, 302561, 152038], ![21188, -2128515, 0]]]
    h := ![![![-2329, -151, -2], ![5610, 109, 0]], ![![2148, 119, 1], ![-5174, -52, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {14} * I53N1 =  Ideal.span {B.equivFun.symm ![-17, 5, 3]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 2 ![![59, 0, 0], ![-9, 1, 0]]
  ![-1055, -15, -21] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![118, 0, 0], ![-18, 2, 0]]
    hsu := by decide
    w := ![![-2110, -30, -42], ![-1806, -26, -36]]
    hw := by decide
    g := ![![![-25, 9, -87], ![6, 177, 0]], ![![6, -3, 15], ![-1, -30, 0]]]
    h := ![![![-18022, 2051, -6], ![-118027, 333, 0]], ![![-15414, 1753, -5], ![-100947, 277, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {2} * I59N1 =  Ideal.span {B.equivFun.symm ![-1055, -15, -21]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![-27, 1, 0]]
  ![9, -7, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![122, 0, 0], ![-54, 2, 0]]
    hsu := by decide
    w := ![![18, -14, 2], ![86, -40, -6]]
    hw := by decide
    g := ![![![-1030, -12, 4961], ![-5, -9963, 0]], ![![427, 4, -2057], ![4, 4131, 0]]]
    h := ![![![522, -19, 0], ![1179, 1, 0]], ![![2440, -92, 0], ![5511, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![9, -7, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E61RS1 


noncomputable def E67RS0 : RelationCertificate Table 14 ![![67, 0, 0], ![11, 1, 0]]
  ![27, -17, 1] ![![14, 0, 0], ![2, 1, 0]] where
    su := ![![938, 0, 0], ![154, 14, 0]]
    hsu := by decide
    w := ![![378, -238, 14], ![140, -56, -14]]
    hw := by decide
    g := ![![![440687, -44061450, -22140877], ![-3084282, 309972299, 0]], ![![65839, -6582630, -3307771], ![-460773, 46308798, 0]]]
    h := ![![![2909, 264, 0], ![-17716, 1, 0]], ![![1066, 97, 0], ![-6492, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {14} * I67N0 =  Ideal.span {B.equivFun.symm ![27, -17, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 14 ![![67, 0, 0], ![12, 1, 0]]
  ![-61, 27, 5] ![![14, 0, 0], ![2, 1, 0]] where
    su := ![![938, 0, 0], ![168, 14, 0]]
    hsu := by decide
    w := ![![-854, 378, 70], ![308, -252, 42]]
    hw := by decide
    g := ![![![-657, 5454, 2730], ![304, -38391, 0]], ![![-134, 949, 475], ![59, -6685, 0]]]
    h := ![![![-271, -23, 0], ![1508, 5, 0]], ![![82, 6, 0], ![-456, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {14} * I67N1 =  Ideal.span {B.equivFun.symm ![-61, 27, 5]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E67RS1 


noncomputable def E79RS0 : RelationCertificate Table 2 ![![79, 0, 0], ![6, 1, 0]]
  ![-49, -1, -1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![158, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![-98, -2, -2], ![-86, 0, -2]]
    hw := by decide
    g := ![![![-6, 2, -23153], ![3, 46305, 0]], ![![-1, 0, -1890], ![1, 3780, 0]]]
    h := ![![![-481, -86, -1], ![6325, 78, 0]], ![![-415, -75, -1], ![5457, 78, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {2} * I79N0 =  Ideal.span {B.equivFun.symm ![-49, -1, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E79RS0 


noncomputable def E79RS1 : RelationCertificate Table 8 ![![79, 0, 0], ![-4, 1, 0]]
  ![59, 1, 1] ![![8, 0, 0], ![-2, 1, 0]] where
    su := ![![632, 0, 0], ![-32, 8, 0]]
    hsu := by decide
    w := ![![472, 8, 8], ![-32, 8, 0]]
    hw := by decide
    g := ![![![5, 76, -39], ![11, 311, 0]], ![![0, -2, 1], ![1, -8, 0]]]
    h := ![![![69, -17, 0], ![1348, 1, 0]], ![![-4, 5, -1], ![-78, 79, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {8} * I79N1 =  Ideal.span {B.equivFun.symm ![59, 1, 1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E79RS1 
