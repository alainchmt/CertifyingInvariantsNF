import IdealArithmetic.Examples.NF3_1_808623_1.PrimesBelow3_1_808623_1F1
import IdealArithmetic.Examples.NF3_1_808623_1.ClassGroupData3_1_808623_1

set_option linter.all false

noncomputable section


noncomputable def E41RS0 : RelationCertificate Table 5 ![![41, 0, 0], ![13, 1, 0]]
  ![10733, -1746, 420] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![205, 0, 0], ![65, 5, 0]]
    hsu := by decide
    w := ![![53665, -8730, 2100], ![88565, 10115, -9150]]
    hw := by decide
    g := ![![![12928206, 1114283, 432276], ![2808503, 0, -184140]], ![![6078208, 627646, 268566], ![1341173, 0, -61380]]]
    h := ![![![164207, -1279737, -426385], ![20856, 3496441, 0]], ![![267075, -2081355, -693570], ![33958, 5686908, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {5} * I41N0 =  Ideal.span {B.equivFun.symm ![10733, -1746, 420]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 5 ![![41, 0, 0], ![-10, 1, 0]]
  ![8116, 648, -695] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![205, 0, 0], ![-50, 5, 0]]
    hsu := by decide
    w := ![![40580, 3240, -3475], ![-116195, 2415, 3935]]
    hw := by decide
    g := ![![![-3441239, 209379, 203505], ![-646372, 0, 171864]], ![![1516985, 46990, -2012], ![312799, 0, -41943]]]
    h := ![![![-6264, -26721, 16680], ![889, -136915, 0]], ![![6779, 30285, -18888], ![-890, 155039, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {5} * I41N1 =  Ideal.span {B.equivFun.symm ![8116, 648, -695]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 5 ![![41, 0, 0], ![-3, 1, 0]]
  ![-3, 1, 0] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![205, 0, 0], ![-15, 5, 0]]
    hsu := by decide
    w := ![![-15, 5, 0], ![-5, 0, 5]]
    hw := by decide
    g := ![![![-6940, -165, 41], ![-1418, 0, 204]], ![![341, 8, -2], ![70, 0, -10]]]
    h := ![![![-65, -35, 170], ![42, -1394, 0]], ![![-20, -12, 56], ![33, -459, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {5} * I41N2 =  Ideal.span {B.equivFun.symm ![-3, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS2 


noncomputable def E47RS0 : RelationCertificate Table 25 ![![47, 0, 0], ![18, 1, 0]]
  ![66441933, 12112349, 4470895] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![1175, 0, 0], ![450, 25, 0]]
    hsu := by decide
    w := ![![1661048325, 302808725, 111772375], ![833565650, 151958825, 56090850]]
    hw := by decide
    g := ![![![-2970565945063, 4449931461029, 7420497410110], ![59174620644, -37102487050512, -141]], ![![-1116595709766, 1672669272634, 2789264983913], ![22242942532, -13946324919696, -53]]]
    h := ![![![722670287, -7651234095, -1912171575], ![113975134, 17975306984, 0]], ![![362658394, -3839626955, -959587098], ![57196278, 9020567448, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {25} * I47N0 =  Ideal.span {B.equivFun.symm ![66441933, 12112349, 4470895]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E47RS0 


noncomputable def E47RS1 : RelationCertificate Table 25 ![![47, 0, 0], ![-16, 1, 0]]
  ![-68, -4, 5] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![1175, 0, 0], ![-400, 25, 0]]
    hsu := by decide
    w := ![![-1700, -100, 125], ![825, -25, -25]]
    hw := by decide
    g := ![![![-109302, -28877, -34974], ![-5517, 178365, 17484]], ![![37982, 10034, 12154], ![1943, -61985, -6076]]]
    h := ![![![-139836, -1040112, 371275], ![25484, -3489984, 0]], ![![68015, 505783, -180543], ![-12346, 1697104, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {25} * I47N1 =  Ideal.span {B.equivFun.symm ![-68, -4, 5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E47RS1 


noncomputable def E47RS2 : RelationCertificate Table 25 ![![47, 0, 0], ![-2, 1, 0]]
  ![-99, 28, -10] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![1175, 0, 0], ![-50, 25, 0]]
    hsu := by decide
    w := ![![-2475, 700, -250], ![-1925, -125, 150]]
    hw := by decide
    g := ![![![-10429249843938, 15623088885059, 26052332448454], ![207753561665, -130261662051976, 951588]], ![![257512345758, -385755287031, -643267477728], ![-5129717642, 3216337383936, -23496]]]
    h := ![![![114943, 104, -287880], ![-4860, 2706070, 0]], ![![88065, 79, -220562], ![-3718, 2073284, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N2 : Ideal.span {25} * I47N2 =  Ideal.span {B.equivFun.symm ![-99, 28, -10]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E47RS2 


noncomputable def E59RS1 : RelationCertificate Table 5 ![![59, 0, 0], ![-11, 1, 0]]
  ![103061, 18788, 6935] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![295, 0, 0], ![-55, 5, 0]]
    hsu := by decide
    w := ![![515305, 93940, 34675], ![1292980, 235710, 87005]]
    hw := by decide
    g := ![![![4602, 117, 13], ![945, 0, -153]], ![![-646, -29, -7], ![-130, 0, 26]]]
    h := ![![![-973254, -4477581, 2486845], ![105611, -29343384, 0]], ![![-2442064, -11234942, 6239879], ![264892, -73627092, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {5} * I59N1 =  Ideal.span {B.equivFun.symm ![103061, 18788, 6935]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 25 ![![61, 0, 0], ![-27, 1, 0]]
  ![-154257, -28121, -10380] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![1525, 0, 0], ![-675, 25, 0]]
    hsu := by decide
    w := ![![-3856425, -703025, -259500], ![-1935275, -352800, -130225]]
    hw := by decide
    g := ![![![6214992124995, -9310107729126, -15525099856531], ![-123804624153, 77625499282778, 344]], ![![-2637758280144, 3951382923412, 6589141204613], ![52544985735, -32945706023123, -146]]]
    h := ![![![-60972205, -835844405, 167125060], ![13285384, -2038927808, 0]], ![![-30597758, -419452934, 83868596], ![6667037, -1023197913, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {25} * I61N1 =  Ideal.span {B.equivFun.symm ![-154257, -28121, -10380]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E61RS1 


noncomputable def E67RS0 : RelationCertificate Table 5 ![![67, 0, 0], ![3, 1, 0]]
  ![429, -8, -15] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![335, 0, 0], ![15, 5, 0]]
    hsu := by decide
    w := ![![2145, -40, -75], ![-2210, 240, -25]]
    hw := by decide
    g := ![![![8552, -59, -215], ![1701, 0, -315]], ![![41, -56, -36], ![-2, 0, -15]]]
    h := ![![![186155, -465551, -465530], ![1414, 6238099, 0]], ![![-192181, 480617, 480595], ![-1421, -6439974, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {5} * I67N0 =  Ideal.span {B.equivFun.symm ![429, -8, -15]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 5 ![![67, 0, 0], ![32, 1, 0]]
  ![818, 149, 55] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![335, 0, 0], ![160, 5, 0]]
    hsu := by decide
    w := ![![4090, 745, 275], ![10255, 1870, 690]]
    hw := by decide
    g := ![![![22589, 527, -134], ![4628, 0, -662]], ![![10915, 256, -65], ![2235, 0, -320]]]
    h := ![![![27358, -509371, -74895], ![5470, 1003604, 0]], ![![68593, -1277158, -187786], ![13720, 2516360, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {5} * I67N1 =  Ideal.span {B.equivFun.symm ![818, 149, 55]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E67RS1 
