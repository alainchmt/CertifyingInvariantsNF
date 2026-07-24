import IdealArithmetic.Examples.NF3_1_110700_4.PrimesBelow3_1_110700_4F1
import IdealArithmetic.Examples.NF3_1_110700_4.ClassGroupData3_1_110700_4

set_option linter.all false

noncomputable section


noncomputable def E43RS0 : RelationCertificate Table 8281 ![![43, 0, 0], ![19, 1, 0]]
  ![-887, -256, -67] ![![8281, 0, 0], ![-869, 1, 0]] where
    su := ![![356083, 0, 0], ![157339, 8281, 0]]
    hsu := by decide
    w := ![![-7345247, -2119936, -554827], ![770133, 223587, 57967]]
    hw := by decide
    g := ![![![68565159, 5470211512634, -6294834973], ![653380992, 52127528411396, 0]], ![![41458484, 3307562555636, -3806171005], ![395072159, 31518902092398, 0]]]
    h := ![![![-58698671, -4288678, -63121], ![132844314, 2714136, 0]], ![![6154833, 449678, 6618], ![-13929354, -284567, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {8281} * I43N0 =  Ideal.span {B.equivFun.symm ![-887, -256, -67]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E43RS0 


noncomputable def E43RS1 : RelationCertificate Table 7 ![![43, 0, 0], ![-10, 1, 0]]
  ![3, -6, 1] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![301, 0, 0], ![-70, 7, 0]]
    hsu := by decide
    w := ![![21, -42, 7], ![7, -21, -7]]
    hw := by decide
    g := ![![![20, -883, 903], ![-127, -6312, 0]], ![![-31, -1180, 1202], ![-157, -8416, 0]]]
    h := ![![![31, -3, 0], ![133, 1, 0]], ![![17, 8, -1], ![73, 42, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {7} * I43N1 =  Ideal.span {B.equivFun.symm ![3, -6, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E43RS1 


noncomputable def E43RS2 : RelationCertificate Table 13 ![![43, 0, 0], ![-9, 1, 0]]
  ![-3, 4, -2] ![![13, 0, 0], ![2, 1, 0]] where
    su := ![![559, 0, 0], ![-117, 13, 0]]
    hsu := by decide
    w := ![![-39, 52, -26], ![-26, 65, 0]]
    hw := by decide
    g := ![![![-21, -222, -112], ![-10, 1446, 0]], ![![3, 39, 20], ![10, -258, 0]]]
    h := ![![![-399, 53, -1], ![-1906, 41, 0]], ![![-260, 38, -1], ![-1242, 43, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {13} * I43N2 =  Ideal.span {B.equivFun.symm ![-3, 4, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E43RS2 


noncomputable def E53RS0 : RelationCertificate Table 7 ![![53, 0, 0], ![13, 1, 0]]
  ![3, 1, 1] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![371, 0, 0], ![91, 7, 0]]
    hsu := by decide
    w := ![![21, 7, 7], ![7, -28, 0]]
    hw := by decide
    g := ![![![1055, 51993, -53032], ![7278, 371228, 0]], ![![302, 14907, -15205], ![2087, 106436, 0]]]
    h := ![![![146, 11, 0], ![-595, 1, 0]], ![![40, 3, 0], ![-163, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {7} * I53N0 =  Ideal.span {B.equivFun.symm ![3, 1, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 91 ![![53, 0, 0], ![-8, 1, 0]]
  ![-17, 27, 6] ![![91, 0, 0], ![41, 1, 0]] where
    su := ![![4823, 0, 0], ![-728, 91, 0]]
    hsu := by decide
    w := ![![-1547, 2457, 546], ![-637, 910, 273]]
    hw := by decide
    g := ![![![101, -26064, -636], ![-240, 57855, 0]], ![![-26, 3278, 80], ![60, -7277, 0]]]
    h := ![![![-61, 9, 0], ![-402, 6, 0]], ![![-11, 2, 0], ![-72, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {91} * I53N1 =  Ideal.span {B.equivFun.symm ![-17, 27, 6]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E53RS1 


noncomputable def E53RS2 : RelationCertificate Table 1183 ![![53, 0, 0], ![-5, 1, 0]]
  ![-53, -146, 8] ![![1183, 0, 0], ![314, 1, 0]] where
    su := ![![62699, 0, 0], ![-5915, 1183, 0]]
    hsu := by decide
    w := ![![-62699, -172718, 9464], ![-16562, -46137, 2366]]
    hw := by decide
    g := ![![![-99, -332835, -1060], ![371, 1253960, 0]], ![![-147, 26061, 83], ![554, -98187, 0]]]
    h := ![![![-333551, 67263, -111], ![-3535630, 5891, 0]], ![![-88098, 17769, -30], ![-933836, 1592, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {1183} * I53N2 =  Ideal.span {B.equivFun.symm ![-53, -146, 8]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E53RS2 


noncomputable def E59RS1 : RelationCertificate Table 91 ![![59, 0, 0], ![15, 1, 0]]
  ![19, 18, 4] ![![91, 0, 0], ![41, 1, 0]] where
    su := ![![5369, 0, 0], ![1365, 91, 0]]
    hsu := by decide
    w := ![![1729, 1638, 364], ![819, 637, 182]]
    hw := by decide
    g := ![![![233, -65311, -1593], ![-512, 144971, 0]], ![![38, -17220, -420], ![-83, 38222, 0]]]
    h := ![![![11, 0, 0], ![-42, 4, 0]], ![![-9, -1, 0], ![36, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {91} * I59N1 =  Ideal.span {B.equivFun.symm ![19, 18, 4]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E59RS1 


noncomputable def E67RS1 : RelationCertificate Table 7 ![![67, 0, 0], ![-33, 1, 0]]
  ![17, 1, 1] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![469, 0, 0], ![-231, 7, 0]]
    hsu := by decide
    w := ![![119, 7, 7], ![-7, -14, 0]]
    hw := by decide
    g := ![![![2, -112, 114], ![-13, -796, 0]], ![![0, 53, -55], ![13, 384, 0]]]
    h := ![![![4010, -121, 0], ![8141, 1, 0]], ![![32, -1, 0], ![65, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {7} * I67N1 =  Ideal.span {B.equivFun.symm ![17, 1, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E67RS1 


noncomputable def E79RS1 : RelationCertificate Table 169 ![![79, 0, 0], ![31, 1, 0]]
  ![-99, -24, -1] ![![169, 0, 0], ![-24, 1, 0]] where
    su := ![![13351, 0, 0], ![5239, 169, 0]]
    hsu := by decide
    w := ![![-16731, -4056, -169], ![2366, 507, 0]]
    hw := by decide
    g := ![![![644540655, 782499184819, -32605251695], ![4538640451, 5510287536452, 0]], ![![250201437, 303754956468, -12656890897], ![1761835121, 2139014561592, 0]]]
    h := ![![![-291466, -11634, -72], ![742765, 5687, 0]], ![![41136, 1637, 10], ![-104830, -790, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {169} * I79N1 =  Ideal.span {B.equivFun.symm ![-99, -24, -1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E79RS1 
