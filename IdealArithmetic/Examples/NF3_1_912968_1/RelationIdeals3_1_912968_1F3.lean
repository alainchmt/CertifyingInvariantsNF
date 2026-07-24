import IdealArithmetic.Examples.NF3_1_912968_1.PrimesBelow3_1_912968_1F3
import IdealArithmetic.Examples.NF3_1_912968_1.ClassGroupData3_1_912968_1

set_option linter.all false

noncomputable section


noncomputable def E151RS1 : RelationCertificate Table 2 ![![151, 0, 0], ![66, 1, 0]]
  ![755784, 173674, 38841] ![![2, 0, 0], ![-16, -1, 1]] where
    su := ![![302, 0, 0], ![132, 2, 0]]
    hsu := by decide
    w := ![![1511568, 347348, 77682], ![17373206, 3992244, 892838]]
    hw := by decide
    g := ![![![-343, 1930, -734], ![1485, 0, 0]], ![![-132, 764, -305], ![649, 0, 0]]]
    h := ![![![-122325084, -11886057109, -360209853], ![-132182119, 27195863322, 0]], ![![-1405942976, -136612391027, -4140071753], ![-1519235827, 312575640561, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {2} * I151N1 =  Ideal.span {B.equivFun.symm ![755784, 173674, 38841]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E151RS1 


noncomputable def E179RS1 : RelationCertificate Table 2 ![![179, 0, 0], ![78, 1, 0]]
  ![-1732, -398, -89] ![![2, 0, 0], ![-16, -1, 1]] where
    su := ![![358, 0, 0], ![156, 2, 0]]
    hsu := by decide
    w := ![![-3464, -796, -178], ![-39814, -9148, -2046]]
    hw := by decide
    g := ![![![11, 70, -2], ![-53, 0, 0]], ![![8, 31, -2], ![-19, 0, 0]]]
    h := ![![![23908, 2742548, 70325], ![25806, -6294132, 0]], ![![274999, 31521892, 808291], ![296126, -72342556, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {2} * I179N1 =  Ideal.span {B.equivFun.symm ![-1732, -398, -89]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E179RS1 


noncomputable def E193RS1 : RelationCertificate Table 2 ![![193, 0, 0], ![58, 1, 0]]
  ![78399192149490212, 18015598573333506, 4029065156981151] ![![2, 0, 0], ![-16, -1, 1]] where
    su := ![![386, 0, 0], ![116, 2, 0]]
    hsu := by decide
    w := ![![156798384298980424, 36031197146667012, 8058130313962302], ![1802162114522401354, 414124537882965724, 92616114832005914]]
    hw := by decide
    g := ![![![108385989, -758110334, 238467254], ![-368799067, 0, 0]], ![![31974912, -208134444, 69159413], ![-117152257, 0, 0]]]
    h := ![![![1265300827912985898, 87928256961557278471, 3032175853768059079], ![835832668292800387, -292602955356039210548, 0]], ![![14542734134240943151, 1010603356664431580635, 34850310943324851133], ![9606642157774125955, -3363031852002140132856, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {2} * I193N1 =  Ideal.span {B.equivFun.symm ![78399192149490212, 18015598573333506, 4029065156981151]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E193RS1 
