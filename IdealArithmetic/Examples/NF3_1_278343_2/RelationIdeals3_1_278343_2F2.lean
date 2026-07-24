import IdealArithmetic.Examples.NF3_1_278343_2.PrimesBelow3_1_278343_2F2
import IdealArithmetic.Examples.NF3_1_278343_2.ClassGroupData3_1_278343_2

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 4 ![![83, 0, 0], ![41, 1, 0]]
  ![987, -67, -354] ![![4, 0, 0], ![-9, 1, -1]] where
    su := ![![332, 0, 0], ![164, 4, 0]]
    hsu := by decide
    w := ![![3948, -268, -1416], ![-40760, 10076, -3360]]
    hw := by decide
    g := ![![![939370, 578979, -185199], ![-1922533, 0, -14586]], ![![516705, 318951, -101838], ![-1057372, 0, -7956]]]
    h := ![![![438063, 13073445, 2491034], ![373922, -25844522, 0]], ![![-4532735, -135271592, -25774912], ![-3868839, 267414607, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {4} * I83N1 =  Ideal.span {B.equivFun.symm ![987, -67, -354]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E83RS1 


noncomputable def E107RS1 : RelationCertificate Table 2 ![![107, 0, 0], ![-43, 1, 0]]
  ![3, 1, -4] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![214, 0, 0], ![-86, 2, 0]]
    hsu := by decide
    w := ![![6, 2, -8], ![-322, 64, 12]]
    hw := by decide
    g := ![![![3217772, -476494, -39644], ![-238247, 0, -79422]], ![![-1280142, 189574, 15775], ![94788, 0, 31598]]]
    h := ![![![49, -1197, 228], ![-20, -3050, 0]], ![![-2428, 64571, -12302], ![1615, 164540, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {2} * I107N1 =  Ideal.span {B.equivFun.symm ![3, 1, -4]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E107RS1 


noncomputable def E113RS1 : RelationCertificate Table 4 ![![113, 0, 0], ![18, 1, 0]]
  ![-23, 5, 0] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![452, 0, 0], ![72, 4, 0]]
    hsu := by decide
    w := ![![-92, 20, 0], ![-36, -8, 40]]
    hw := by decide
    g := ![![![-3476, 1186, -42], ![-1439, 0, 218]], ![![-602, 206, -7], ![-247, 0, 38]]]
    h := ![![![7505, 74197, 31248], ![1926, -441378, 0]], ![![2909, 28745, 12106], ![737, -170996, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {4} * I113N1 =  Ideal.span {B.equivFun.symm ![-23, 5, 0]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E113RS1 


noncomputable def E131RS1 : RelationCertificate Table 4 ![![131, 0, 0], ![-24, 1, 0]]
  ![35, 1, 2] ![![4, 0, 0], ![-9, 1, -1]] where
    su := ![![524, 0, 0], ![-96, 4, 0]]
    hsu := by decide
    w := ![![140, 4, 8], ![-184, -12, -16]]
    hw := by decide
    g := ![![![-169422, 179366, 50975], ![413303, 0, 41880]], ![![25414, -26905, -7646], ![-61995, 0, -6282]]]
    h := ![![![15667, -189022, 65758], ![-4218, -1076787, 0]], ![![-20552, 248276, -86372], ![5684, 1414341, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {4} * I131N1 =  Ideal.span {B.equivFun.symm ![35, 1, 2]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 4 ![![137, 0, 0], ![-52, 1, 0]]
  ![1974529435, 79593404, 112110217] ![![4, 0, 0], ![12, 0, 1]] where
    su := ![![548, 0, 0], ![-208, 4, 0]]
    hsu := by decide
    w := ![![7898117740, 318373616, 448440868], ![27450773736, 1106542392, 1558605380]]
    hw := by decide
    g := ![![![619800, -221071, -498585], ![1734783, -286890, 0]], ![![1024443453937802, -356231956983279, -834895601052196], ![2864606461550384, -474975942646447, 0]]]
    h := ![![![1286737130895, -40386029250103, 6335961055297], ![-783185109869, -108503319058184, 0]], ![![4472195908002, -140366070440481, 22021326986329], ![-2722045676271, -377115175934466, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {4} * I137N1 =  Ideal.span {B.equivFun.symm ![1974529435, 79593404, 112110217]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E137RS1 
