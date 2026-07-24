import IdealArithmetic.Examples.NF3_1_797203_1.PrimesBelow3_1_797203_1F0
import IdealArithmetic.Examples.NF3_1_797203_1.ClassGroupData3_1_797203_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![1, 1, 0]]
  ![5, -1, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![4, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![10, -2, 0], ![-2, 6, -4]]
    hw := by decide
    g := ![![![-61, -2, -2], ![1, 0, 0]], ![![-184, -4, -6], ![-1, 0, 0]]]
    h := ![![![2, -1, 0], ![1, 0, 0]], ![![-394, 142, -10], ![-125, 0, 6]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![5, -1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![18, -1, 1]]
  ![1, 0, 0] ![![3, 0, 0], ![18, -1, 1]] where
    su := ![![3, 0, 0], ![18, -1, 1]]
    hsu := by decide
    w := ![![3, 0, 0], ![18, -1, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 3 ![![3, 0, 0], ![-1, 1, 0]]
  ![38690288, -11674889, 2825459] ![![3, 0, 0], ![18, -1, 1]] where
    su := ![![9, 0, 0], ![-3, 3, 0]]
    hsu := by decide
    w := ![![116070864, -35024667, 8476377], ![-1198906575, 187132344, 36610935]]
    hw := by decide
    g := ![![![-179716185065315, -435328260072995, 116607137453958], ![-894318644549519, 0, 0]], ![![-241070852008835, -583948265545350, 156416529574784], ![-1199636847012855, 0, 0]]]
    h := ![![![23699821, -14694688, 31080049], ![-12798169, -22603672, 0]], ![![-65959179, -46460180, 134240095], ![6499668, -97629160, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {3} * I3N1 =  Ideal.span {B.equivFun.symm ![38690288, -11674889, 2825459]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 3 ![![5, 0, 0], ![16, 0, 1]]
  ![-3538, 835, -93] ![![3, 0, 0], ![18, -1, 1]] where
    su := ![![15, 0, 0], ![48, 0, 3]]
    hsu := by decide
    w := ![![-10614, 2505, -279], ![66309, -7050, -4371]]
    hw := by decide
    g := ![![![161833, 392042, -105013], ![805394, 0, 0]], ![![746647, 1808618, -484457], ![3715543, 0, 0]]]
    h := ![![![-74, 167, 21], ![-198, 0, 0]], ![![411, -470, -542], ![1253, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3} * I5N0 =  Ideal.span {B.equivFun.symm ![-3538, 835, -93]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 3 ![![5, 0, 0], ![-2, 1, 0]]
  ![-26369, 3524, 1226] ![![3, 0, 0], ![18, -1, 1]] where
    su := ![![15, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![-79107, 10572, 3678], ![-8568, 64227, -44451]]
    hw := by decide
    g := ![![![-44242407, -107168805, 28706263], ![-220162735, 0, 0]], ![![-26759514, -64819823, 17362654], ![-133162906, 0, 0]]]
    h := ![![![-39031, 62593, -89774], ![28131, 112524, 0]], ![![-16842, 34114, -46357], ![13565, 54242, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {3} * I5N1 =  Ideal.span {B.equivFun.symm ![-26369, 3524, 1226]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![15, -2, 1]]
  ![10703202026028190313959960412363798466754, 264842008620202661590423456477525845678, 350297797573765211151109106156081770463] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![30, -4, 2]]
    hsu := by decide
    w := ![![21406404052056380627919920824727596933508, 529684017240405323180846912955051691356, 700595595147530422302218212312163540926], ![53774949248452717418149431048679480801732, 1330617280490092162440700195828146589038, 1759963629628341068663912038222266923638]]
    hw := by decide
    g := ![![![33350531454823380296, -5247638039419194187, -55768890150689145], ![-2623819019709597093, 0, 0]], ![![-65604854395658617669, -1366781658032444590, 10498368744653854961], ![-683390829016222293, 0, 0]]]
    h := ![![![297318844188695278358568320209743812602, 202062574883025587188155392275753059450, -32071458600960430458889005510041573539], ![574798007780488224363332144726372785236, 0, 0]], ![![746893579976119915366956375302151141083, 507600654594883141155402792982480611851, -80566593735056774157396958195787433200], ![1443947970959567953433734726481645494219, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![10703202026028190313959960412363798466754, 264842008620202661590423456477525845678, 350297797573765211151109106156081770463]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 2 ![![7, 0, 0], ![-1, 1, 0]]
  ![-841689, 100921, 47355] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![-1683378, 201842, 94710], ![7399802, -2173840, 498394]]
    hw := by decide
    g := ![![![-2341101289227, -46342914303, -76620307037], ![-23171457151, 0, 0]], ![![-1345863238022, -26641830916, -44047839793], ![-13320915456, 0, 0]]]
    h := ![![![-143599, 37775, -47355], ![25916, 94710, 0]], ![![378335, -5052, -249197], ![-54768, 498394, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![-841689, 100921, 47355]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS1 


noncomputable def E11RS1 : RelationCertificate Table 6 ![![11, 0, 0], ![-3, 1, 0]]
  ![-43016693, -1064413, -1407864] ![![6, 0, 0], ![36, 1, 2]] where
    su := ![![66, 0, 0], ![-18, 6, 0]]
    hsu := by decide
    w := ![![-258100158, -6386478, -8447184], ![-2372695182, -58710408, -77654322]]
    hw := by decide
    g := ![![![134, -638, -355], ![607, 0, 0]], ![![-117, 986, -8], ![-520, 0, 0]]]
    h := ![![![-148568857, 320897595, -327457920], ![69691298, 900157314, 0]], ![![-1365782259, 2949987266, -3010295829], ![640666738, 8275077933, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {6} * I11N1 =  Ideal.span {B.equivFun.symm ![-43016693, -1064413, -1407864]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 2 ![![13, 0, 0], ![6, 1, 0]]
  ![539481867, 13349039, 17656334] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![26, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![1078963734, 26698078, 35312668], ![2710460846, 67068144, 88708824]]
    hw := by decide
    g := ![![![6408, 1207, -1980], ![605, 0, 0]], ![![-19961, 4026, -754], ![2015, 0, 0]]]
    h := ![![![2090409525, 6718921308, 5466851870], ![1481644505, -17762854494, 0]], ![![5251310119, 16878577620, 13733258568], ![3722033727, -44622001743, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {2} * I13N0 =  Ideal.span {B.equivFun.symm ![539481867, 13349039, 17656334]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 6 ![![13, 0, 0], ![-4, 1, 0]]
  ![-11, 5, -2] ![![6, 0, 0], ![36, 1, 2]] where
    su := ![![78, 0, 0], ![-24, 6, 0]]
    hsu := by decide
    w := ![![-66, 30, -12], ![426, -144, 42]]
    hw := by decide
    g := ![![![-48, 1, 15], ![-121, 0, 0]], ![![-7, 0, 1], ![-9, 0, 0]]]
    h := ![![![33, -87, 70], ![-4, -228, 0]], ![![-181, 537, -437], ![105, 1422, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {6} * I13N1 =  Ideal.span {B.equivFun.symm ![-11, 5, -2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 3 ![![13, 0, 0], ![-3, 1, 0]]
  ![1931080, 47783, 63201] ![![3, 0, 0], ![18, -1, 1]] where
    su := ![![39, 0, 0], ![-9, 3, 0]]
    hsu := by decide
    w := ![![5793240, 143349, 189603], ![38703639, 957690, 1266705]]
    hw := by decide
    g := ![![![-27, 219, 6], ![-167, 0, 0]], ![![-19, -80, 104], ![-47, 0, 0]]]
    h := ![![![-40976332, 88508995, -89751571], ![16264472, 291708406, 0]], ![![-273755835, 591313362, -599614793], ![108660068, 1948853636, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {3} * I13N2 =  Ideal.span {B.equivFun.symm ![1931080, 47783, 63201]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS2 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0], ![2, 1, 0]]
  ![2, 1, -1] ![![3, 0, 0], ![18, -1, 1]] where
    su := ![![51, 0, 0], ![6, 3, 0]]
    hsu := by decide
    w := ![![6, 3, -3], ![237, -60, 9]]
    hw := by decide
    g := ![![![-13, -23, 6], ![-47, 0, 0]], ![![-14, -9, 2], ![-18, 0, 0]]]
    h := ![![![4, 2, 11], ![14, -47, 0]], ![![-13, -10, -33], ![9, 141, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![2, 1, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 6 ![![19, 0, 0], ![5, 1, 0]]
  ![-1253, -31, -41] ![![6, 0, 0], ![36, 1, 2]] where
    su := ![![114, 0, 0], ![30, 6, 0]]
    hsu := by decide
    w := ![![-7518, -186, -246], ![-69108, -1710, -2262]]
    hw := by decide
    g := ![![![-15, 2, 2], ![-1, 0, 0]], ![![-28, -4, -1], ![6, 0, 0]]]
    h := ![![![2318, 5194, 5241], ![903, -24905, 0]], ![![21348, 47753, 48177], ![8148, -228935, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {6} * I19N1 =  Ideal.span {B.equivFun.symm ![-1253, -31, -41]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E19RS1 


noncomputable def E31RS1 : RelationCertificate Table 2 ![![31, 0, 0], ![15, 1, 0]]
  ![-8329, 413, 885] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![62, 0, 0], ![30, 2, 0]]
    hsu := by decide
    w := ![![-16658, 826, 1770], ![135346, -31752, 3422]]
    hw := by decide
    g := ![![![450890971, 8925543, 14756903], ![4462773, 0, 0]], ![![291249280, 5765380, 9532099], ![2882692, 0, 0]]]
    h := ![![![-563729, -5448995, -1560965], ![-448542, 12097700, 0]], ![![4609428, 44554567, 12763881], ![3667647, -98919650, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {2} * I31N1 =  Ideal.span {B.equivFun.symm ![-8329, 413, 885]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E31RS1 
