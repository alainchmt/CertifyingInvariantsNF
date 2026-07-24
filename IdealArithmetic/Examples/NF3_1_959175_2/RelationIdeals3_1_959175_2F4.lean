import IdealArithmetic.Examples.NF3_1_959175_2.PrimesBelow3_1_959175_2F4
import IdealArithmetic.Examples.NF3_1_959175_2.ClassGroupData3_1_959175_2

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 13 ![![197, 0, 0], ![-29, 1, 0]]
  ![1527, 62, 91] ![![13, 0, 0], ![4, 1, 0]] where
    su := ![![2561, 0, 0], ![-377, 13, 0]]
    hsu := by decide
    w := ![![19851, 806, 1183], ![22633, 923, 1352]]
    hw := by decide
    g := ![![![507144582, -35762055, 17977679], ![153293568, 0, -38951640]], ![![-73254220, 5165630, -2596776], ![-22142399, 0, 5626348]]]
    h := ![![![15600518, 98372527, -41249169], ![-1797149, 625083568, 0]], ![![17786838, 112158730, -47029944], ![-2048875, 712684544, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {13} * I197N1 =  Ideal.span {B.equivFun.symm ![1527, 62, 91]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E197RS1 


noncomputable def E211RS1 : RelationCertificate Table 169 ![![211, 0, 0], ![60, 1, 0]]
  ![311, 7, 13] ![![169, 0, 0], ![69, 1, 0]] where
    su := ![![35659, 0, 0], ![10140, 169, 0]]
    hsu := by decide
    w := ![![52559, 1183, 2197], ![23829, 676, 1014]]
    hw := by decide
    g := ![![![-31357981677623, 474926462346233, 92138437882140], ![-9992747179826, -1197799692380032, -16074]], ![![-8966112393896, 135794582827436, 26344922270209], ![-2857202203179, -342483989487616, -4596]]]
    h := ![![![9126, -113343, -25402], ![2270, 412295, 0]], ![![4141, -51384, -11516], ![1016, 186914, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {169} * I211N1 =  Ideal.span {B.equivFun.symm ![311, 7, 13]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E211RS1 


noncomputable def E223RS0 : RelationCertificate Table 169 ![![223, 0, 0], ![4, 1, 0]]
  ![-587, 27, 26] ![![169, 0, 0], ![69, 1, 0]] where
    su := ![![37687, 0, 0], ![676, 169, 0]]
    hsu := by decide
    w := ![![-99203, 4563, 4394], ![-35828, 1014, 2197]]
    hw := by decide
    g := ![![![-2566688058300133139, 38873295219166019253, 7541640613197744305], ![-817918229606764190, -98041327967396489420, -764287680]], ![![-64167201455043922, 971832380441901695, 188541015322717131], ![-20447955739385320, -2451033199090968040, -19107192]]]
    h := ![![![-25079, 10033, 65208], ![-200, -1118566, 0]], ![![-9056, 3622, 23543], ![4, -403852, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N0 : Ideal.span {169} * I223N0 =  Ideal.span {B.equivFun.symm ![-587, 27, 26]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E223RS0 


noncomputable def E223RS2 : RelationCertificate Table 13 ![![223, 0, 0], ![-40, 1, 0]]
  ![1743, 71, 104] ![![13, 0, 0], ![4, 1, 0]] where
    su := ![![2899, 0, 0], ![-520, 13, 0]]
    hsu := by decide
    w := ![![22659, 923, 1352], ![25857, 1053, 1547]]
    hw := by decide
    g := ![![![1146043973, -80814997, 40625917], ![346412386, 0, -88022816]], ![![-205071226, 14460902, -7269535], ![-61986453, 0, 15750658]]]
    h := ![![![-127699, -1099975, 340444], ![18024, -5839916, 0]], ![![-145697, -1255222, 388493], ![20707, -6664140, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N2 : Ideal.span {13} * I223N2 =  Ideal.span {B.equivFun.symm ![1743, 71, 104]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E223RS2 


noncomputable def E227RS1 : RelationCertificate Table 361 ![![227, 0, 0], ![53, 1, 0]]
  ![4983, 203, 301] ![![361, 0, 0], ![48, 1, 0]] where
    su := ![![81947, 0, 0], ![19133, 361, 0]]
    hsu := by decide
    w := ![![1798863, 73283, 108661], ![293854, 11913, 17689]]
    hw := by decide
    g := ![![![-3215687471, 30006633188, 8479865814], ![-344449525, -235479350680, 0]], ![![-878658331, 8199048641, 2317048762], ![-94117741, -64342661775, 0]]]
    h := ![![![-302507, 3220113, 820751], ![-56296, -14331552, 0]], ![![-49435, 526026, 134075], ![-9117, -2341152, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {361} * I227N1 =  Ideal.span {B.equivFun.symm ![4983, 203, 301]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E227RS1 


noncomputable def E229RS1 : RelationCertificate Table 19 ![![229, 0, 0], ![-106, 1, 0]]
  ![-109, 13, -3] ![![19, 0, 0], ![-9, 1, 0]] where
    su := ![![4351, 0, 0], ![-2014, 19, 0]]
    hsu := by decide
    w := ![![-2071, 247, -57], ![361, -228, 190]]
    hw := by decide
    g := ![![![-4883, -12399, 14540], ![1678, -21258, 0]], ![![2227, 5653, -6630], ![-757, 9693, 0]]]
    h := ![![![4598, 114071, -13730], ![-1474, 241859, 0]], ![![-725, -20073, 2416], ![441, -42558, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {19} * I229N1 =  Ideal.span {B.equivFun.symm ![-109, 13, -3]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E229RS1 


noncomputable def E233RS1 : RelationCertificate Table 3211 ![![233, 0, 0], ![-81, 1, 0]]
  ![-1203, 49, 91] ![![3211, 0, 0], ![238, 1, 0]] where
    su := ![![748163, 0, 0], ![-260091, 3211, 0]]
    hsu := by decide
    w := ![![-3862833, 157339, 292201], ![-269724, 9633, 22477]]
    hw := by decide
    g := ![![![-72233135017303, 3424405085101666, 188632414318822], ![-4287474633381, -46592205259549164, -58348326]], ![![25162758764830, -1192907923064738, -65711005560276], ![1493562338394, 16230617998140435, 20325919]]]
    h := ![![![27795, 503595, -78871], ![-7292, 1413618, 0]], ![![1947, 35156, -5506], ![-490, 98685, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N1 : Ideal.span {3211} * I233N1 =  Ideal.span {B.equivFun.symm ![-1203, 49, 91]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E233RS1 


noncomputable def E239RS1 : RelationCertificate Table 13 ![![239, 0, 0], ![-86, 1, 0]]
  ![19, -3, 0] ![![13, 0, 0], ![4, 1, 0]] where
    su := ![![3107, 0, 0], ![-1118, 13, 0]]
    hsu := by decide
    w := ![![247, -39, 0], ![91, 13, -39]]
    hw := by decide
    g := ![![![-1102725842, 77760350, -39090339], ![-333318689, 0, 84695733]], ![![394919935, -27848366, 13999449], ![119371647, 0, -30332139]]]
    h := ![![![-755, -14785, 2184], ![236, -40152, 0]], ![![-273, -5382, 795], ![91, -14616, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N1 : Ideal.span {13} * I239N1 =  Ideal.span {B.equivFun.symm ![19, -3, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E239RS1 


noncomputable def E257RS1 : RelationCertificate Table 3211 ![![257, 0, 0], ![-14, 1, 0]]
  ![-977, -454, 533] ![![3211, 0, 0], ![238, 1, 0]] where
    su := ![![825227, 0, 0], ![-44954, 3211, 0]]
    hsu := by decide
    w := ![![-3137147, -1457794, 1711463], ![-131651, -112385, 122018]]
    hw := by decide
    g := ![![![4519828573460, -214273744938619, -11803187668487], ![268279494248, 2915392899641320, -300382600]], ![![1291379592768, -61221070001950, -3372339334927], ![76651284878, 832969400162660, -85823600]]]
    h := ![![![-132383, -424613, 344981], ![5599, -6819968, 0]], ![![-5515, -17692, 14374], ![249, -284160, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R257N1 : Ideal.span {3211} * I257N1 =  Ideal.span {B.equivFun.symm ![-977, -454, 533]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E257RS1 
