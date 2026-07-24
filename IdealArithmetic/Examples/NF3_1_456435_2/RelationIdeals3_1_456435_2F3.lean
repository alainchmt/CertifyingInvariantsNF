import IdealArithmetic.Examples.NF3_1_456435_2.PrimesBelow3_1_456435_2F3
import IdealArithmetic.Examples.NF3_1_456435_2.ClassGroupData3_1_456435_2

set_option linter.all false

noncomputable section


noncomputable def E149RS1 : RelationCertificate Table 5 ![![149, 0, 0], ![39, 1, 0]]
  ![-91, -12, 12] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![745, 0, 0], ![195, 5, 0]]
    hsu := by decide
    w := ![![-455, -60, 60], ![1745, 65, -120]]
    hw := by decide
    g := ![![![-2171, -5132, -10940], ![-1456, 6854, 0]], ![![-533, -1321, -2824], ![-370, 1771, 0]]]
    h := ![![![-86135, -2006372, -382212], ![-35984, 7118700, 0]], ![![330599, 7701579, 1467144], ![138262, -27325560, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {5} * I149N1 =  Ideal.span {B.equivFun.symm ![-91, -12, 12]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E149RS1 


noncomputable def E151RS0 : RelationCertificate Table 4 ![![151, 0, 0], ![15, 1, 0]]
  ![15, 1, 0] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![604, 0, 0], ![60, 4, 0]]
    hsu := by decide
    w := ![![60, 4, 0], ![32, 20, 8]]
    hw := by decide
    g := ![![![561, 5, -4], ![283, 0, -18]], ![![124, 1, -1], ![64, 0, -4]]]
    h := ![![![97, 1007, 448], ![152, -8456, 0]], ![![52, 535, 238], ![76, -4492, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N0 : Ideal.span {4} * I151N0 =  Ideal.span {B.equivFun.symm ![15, 1, 0]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E151RS0 


noncomputable def E151RS1 : RelationCertificate Table 25 ![![151, 0, 0], ![64, 1, 0]]
  ![-2611, -562, -248] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![3775, 0, 0], ![1600, 25, 0]]
    hsu := by decide
    w := ![![-65275, -14050, -6200], ![-42175, -9075, -4000]]
    hw := by decide
    g := ![![![-710, -1281, -2560], ![-65, 8013, 0]], ![![-298, -545, -1088], ![-12, 3405, 0]]]
    h := ![![![5778421, 252023789, 30095648], ![4118228, -568055387, 0]], ![![3733515, 162835935, 19445200], ![2660842, -367028170, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {25} * I151N1 =  Ideal.span {B.equivFun.symm ![-2611, -562, -248]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E151RS1 


noncomputable def E151RS2 : RelationCertificate Table 10 ![![151, 0, 0], ![72, 1, 0]]
  ![-1, 3, 2] ![![10, 0, 0], ![-4, 1, 0]] where
    su := ![![1510, 0, 0], ![720, 10, 0]]
    hsu := by decide
    w := ![![-10, 30, 20], ![320, 30, 10]]
    hw := by decide
    g := ![![![470808851212, -256799554290, 2225606358009], ![-214003495913, -2782008430929, -552477]], ![![228972613256, -124891587907, 1082398732641], ![-104078204086, -1352998650906, -268691]]]
    h := ![![![1249, 66124, 7054], ![1079, -133144, 0]], ![![-39176, -2042422, -217881], ![-32075, 4112504, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N2 : Ideal.span {10} * I151N2 =  Ideal.span {B.equivFun.symm ![-1, 3, 2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E151RS2 


noncomputable def E163RS1 : RelationCertificate Table 2 ![![163, 0, 0], ![9, 1, 0]]
  ![9, 1, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![326, 0, 0], ![18, 2, 0]]
    hsu := by decide
    w := ![![18, 2, 0], ![2, 12, 8]]
    hw := by decide
    g := ![![![8375099, 734847, -162097], ![367425, 0, -108066]], ![![504526, 44268, -9765], ![22134, 0, -6510]]]
    h := ![![![263, 1631, 1088], ![164, -22168, 0]], ![![20, 173, 116], ![163, -2363, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {2} * I163N1 =  Ideal.span {B.equivFun.symm ![9, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E163RS1 


noncomputable def E167RS1 : RelationCertificate Table 20 ![![167, 0, 0], ![62, 1, 0]]
  ![257, -41, 16] ![![20, 0, 0], ![6, 1, 0]] where
    su := ![![3340, 0, 0], ![1240, 20, 0]]
    hsu := by decide
    w := ![![5140, -820, 320], ![3940, 160, -280]]
    hw := by decide
    g := ![![![-32020850394, -167467353546, -149658964465], ![-17979622776, 374147411307, -534]], ![![-12112753206, -63349058364, -56612553274], ![-6801278868, 141531383235, -202]]]
    h := ![![![1092167, 43529175, 5357928], ![666159, -111846745, 0]], ![![835893, 33316191, 4100830], ![509931, -85604828, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {20} * I167N1 =  Ideal.span {B.equivFun.symm ![257, -41, 16]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E167RS1 


noncomputable def E173RS1 : RelationCertificate Table 100 ![![173, 0, 0], ![78, 1, 0]]
  ![20867, -111, -844] ![![100, 0, 0], ![26, 1, 0]] where
    su := ![![17300, 0, 0], ![7800, 100, 0]]
    hsu := by decide
    w := ![![2086700, -11100, -84400], ![411500, 3300, -20300]]
    hw := by decide
    g := ![![![-1805969, -28977227, -7995906], ![-759290, 99944019, -519]], ![![-811228, -13009141, -3589728], ![-340948, 44868879, -233]]]
    h := ![![![-377358891, -20558013942, -2030586108], ![-288971025, 43911424480, 0]], ![![-74407533, -4053624309, -400390487], ![-56979246, 8658444256, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {100} * I173N1 =  Ideal.span {B.equivFun.symm ![20867, -111, -844]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E173RS1 


noncomputable def E181RS1 : RelationCertificate Table 20 ![![181, 0, 0], ![-24, 1, 0]]
  ![-8301, -1787, -788] ![![20, 0, 0], ![6, 1, 0]] where
    su := ![![3620, 0, 0], ![-480, 20, 0]]
    hsu := by decide
    w := ![![-166020, -35740, -15760], ![-175520, -37780, -16660]]
    hw := by decide
    g := ![![![-466169709768, -2437723881597, -2178493128296], ![-261737106992, 5446229535812, 8759795]], ![![60871747223, 318314358093, 284464391959], ![34177242073, -711160550957, -1143841]]]
    h := ![![![-43759, 470825, -179388], ![8543, 4058555, 0]], ![![-46270, 497767, -189653], ![8979, 4290795, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {20} * I181N1 =  Ideal.span {B.equivFun.symm ![-8301, -1787, -788]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E181RS1 


noncomputable def E191RS1 : RelationCertificate Table 100 ![![191, 0, 0], ![-8, 1, 0]]
  ![408451, 87917, 38768] ![![100, 0, 0], ![26, 1, 0]] where
    su := ![![19100, 0, 0], ![-800, 100, 0]]
    hsu := by decide
    w := ![![40845100, 8791700, 3876800], ![16804600, 3617100, 1595000]]
    hw := by decide
    g := ![![![4834276109, 77746240328, 21452850840], ![2034374253, -268160634434, -422]], ![![-160378854, -2579259198, -711705962], ![-67491039, 8896324500, 14]]]
    h := ![![![28469917, -71324745, 114133648], ![-1565788, -2724936000, 0]], ![![11713170, -29344617, 46957170], ![-644182, -1121100440, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {100} * I191N1 =  Ideal.span {B.equivFun.symm ![408451, 87917, 38768]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E191RS1 
