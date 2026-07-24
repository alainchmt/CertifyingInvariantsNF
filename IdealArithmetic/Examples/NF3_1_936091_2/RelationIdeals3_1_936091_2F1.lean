import IdealArithmetic.Examples.NF3_1_936091_2.PrimesBelow3_1_936091_2F1
import IdealArithmetic.Examples.NF3_1_936091_2.ClassGroupData3_1_936091_2

set_option linter.all false

noncomputable section


noncomputable def E43RS1 : RelationCertificate Table 9 ![![43, 0, 0], ![-15, 1, 0]]
  ![-100346757, -2360961, -2971192] ![![9, 0, 0], ![1, 1, 0]] where
    su := ![![387, 0, 0], ![-135, 9, 0]]
    hsu := by decide
    w := ![![-903120813, -21248649, -26740728], ![-398686419, -9380304, -11804805]]
    hw := by decide
    g := ![![![297525843989, -441834786933, -739360632012], ![-16034326992, 1330849137283, 0]], ![![-110707291004, 164403641425, 275110932244], ![5966261167, -495199677856, 0]]]
    h := ![![![697975404, 4851256128, -1864789264], ![-130659849, 16036593432, 0]], ![![308124126, 2141607087, -823218935], ![-57680341, 7079420512, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {9} * I43N1 =  Ideal.span {B.equivFun.symm ![-100346757, -2360961, -2971192]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 12 ![![53, 0, 0], ![24, 1, 0]]
  ![135, -51, 17] ![![12, 0, 0], ![4, 1, 0]] where
    su := ![![636, 0, 0], ![288, 12, 0]]
    hsu := by decide
    w := ![![1620, -612, 204], ![2376, -732, -204]]
    hw := by decide
    g := ![![![198973, -598541, -497588], ![16453, 1194592, 0]], ![![90370, -271037, -225313], ![7544, 540945, 0]]]
    h := ![![![2589, -36495, -7016], ![486, 74373, 0]], ![![3784, -53438, -10274], ![727, 108901, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {12} * I53N1 =  Ideal.span {B.equivFun.symm ![135, -51, 17]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E53RS1 


noncomputable def E71RS1 : RelationCertificate Table 6 ![![71, 0, 0], ![19, 1, 0]]
  ![-9, 3, 1] ![![6, 0, 0], ![-2, 1, 0]] where
    su := ![![426, 0, 0], ![114, 6, 0]]
    hsu := by decide
    w := ![![-54, 18, 6], ![114, -42, 12]]
    hw := by decide
    g := ![![![-41, -1, 298], ![16, -355, 0]], ![![-8, 0, 79], ![3, -94, 0]]]
    h := ![![![1471, -16085, -3829], ![226, 54372, 0]], ![![-3149, 34033, 8102], ![-342, -115048, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {6} * I71N1 =  Ideal.span {B.equivFun.symm ![-9, 3, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E71RS1 


noncomputable def E73RS0 : RelationCertificate Table 18 ![![73, 0, 0], ![-33, 1, 0]]
  ![-375504405, -8834877, -11118403] ![![18, 0, 0], ![-8, 1, 0]] where
    su := ![![1314, 0, 0], ![-594, 18, 0]]
    hsu := by decide
    w := ![![-6759079290, -159027786, -200131254], ![1887627888, 44412156, 55891242]]
    hw := by decide
    g := ![![![-9109991529752942704773175, -30592865538310741690523414, 25385291583623887622896144], ![2349281483317377774870124, -91387049701045995442426781, 0]], ![![4118215349090775678335253, 13829651544797676489995772, -11475542770747218759830112], ![-1062003958218251607593669, 41311953974689987535388840, 0]]]
    h := ![![![512065956741, 8723295681604, -1406735921026], ![-111984669700, 20538342223299, 0]], ![![-143006160880, -2436180357912, 392863264603], ![31274287028, -5735803042190, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N0 : Ideal.span {18} * I73N0 =  Ideal.span {B.equivFun.symm ![-375504405, -8834877, -11118403]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E73RS0 


noncomputable def E73RS2 : RelationCertificate Table 12 ![![73, 0, 0], ![-19, 1, 0]]
  ![-30819459, -725121, -912541] ![![12, 0, 0], ![4, 1, 0]] where
    su := ![![876, 0, 0], ![-228, 12, 0]]
    hsu := by decide
    w := ![![-369833508, -8701452, -10950492], ![-214906776, -5056332, -6363228]]
    hw := by decide
    g := ![![![14719784895805, -45378190381469, -37737028158309], ![1125079100157, 90568867580092, 0]], ![![-4032817775283, 12432380913055, 10338911813115], ![-308240849003, -24813388351475, 0]]]
    h := ![![![16305176915, 143663616481, -42244850977], ![-2275818382, 616774641756, 0]], ![![9474785088, 83481577462, -24548085908], ![-1322456636, 358401948203, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N2 : Ideal.span {12} * I73N2 =  Ideal.span {B.equivFun.symm ![-30819459, -725121, -912541]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E73RS2 
