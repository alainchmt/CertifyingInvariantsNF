import IdealArithmetic.Examples.NF3_1_884199_1.PrimesBelow3_1_884199_1F1
import IdealArithmetic.Examples.NF3_1_884199_1.ClassGroupData3_1_884199_1

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 125 ![![41, 0, 0], ![-6, 1, 0]]
  ![-32, 7, -1] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![5125, 0, 0], ![-750, 125, 0]]
    hsu := by decide
    w := ![![-4000, 875, -125], ![13250, 2250, -625]]
    hw := by decide
    g := ![![![37, 17, 0], ![64, 0, 0]], ![![9, 4, 0], ![15, 0, 0]]]
    h := ![![![-4804, 804, -2], ![-32822, 27, 0]], ![![15746, -2622, -1], ![107580, 12, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {125} * I41N1 =  Ideal.span {B.equivFun.symm ![-32, 7, -1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 25 ![![43, 0, 0], ![17, 1, 0]]
  ![-179338, -20527, 6424] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![1075, 0, 0], ![425, 25, 0]]
    hsu := by decide
    w := ![![-4483450, -513175, 160600], ![-8693025, -433775, 198125]]
    hw := by decide
    g := ![![![-55179872, -24943329, -8756774], ![64444411, 0, 0]], ![![-42174131, -19064260, -6692829], ![49255066, 0, 0]]]
    h := ![![![267638, -34114081, -5688116], ![-687516, 81531804, 0]], ![![519820, -66256470, -11047669], ![-1335293, 158352564, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {25} * I43N1 =  Ideal.span {B.equivFun.symm ![-179338, -20527, 6424]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS1 


noncomputable def E43RS2 : RelationCertificate Table 25 ![![43, 0, 0], ![-20, 1, 0]]
  ![36115492, -5457607, 642014] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![1075, 0, 0], ![-500, 25, 0]]
    hsu := by decide
    w := ![![902887300, -136440175, 16050350], ![-3495666525, -297432775, 104494375]]
    hw := by decide
    g := ![![![-16348425335624, -7390087456226, -2594413872615], ![19093270315786, 0, 0]], ![![1572099210127, 710646463746, 249484333572], ![-1836049317608, 0, 0]]]
    h := ![![![22388346884, -1264318671, 22880678], ![48133140026, -327742380, 0]], ![![-86403366847, 4880536929, -88451405], ![-185760247388, 1269196730, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {25} * I43N2 =  Ideal.span {B.equivFun.symm ![36115492, -5457607, 642014]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS2 


noncomputable def E53RS0 : RelationCertificate Table 125 ![![53, 0, 0], ![-26, 1, 0]]
  ![-33580520, -8615890, -1629223] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![6625, 0, 0], ![-3250, 125, 0]]
    hsu := by decide
    w := ![![-4197565000, -1076986250, -203652875], ![14057122625, 3606692875, 682008125]]
    hw := by decide
    g := ![![![-19420, 519, 490], ![8162, 0, 0]], ![![12450, -369, -305], ![-5190, 0, 0]]]
    h := ![![![-4013398, -469498397, 56305159], ![-6889599, -995267550, 0]], ![![13440427, 1572291681, -188558968], ![23072525, 3333027123, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {125} * I53N0 =  Ideal.span {B.equivFun.symm ![-33580520, -8615890, -1629223]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 25 ![![53, 0, 0], ![-2, 1, 0]]
  ![500549932, 128428123, 24285135] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![1325, 0, 0], ![-50, 25, 0]]
    hsu := by decide
    w := ![![12513748300, 3210703075, 607128375], ![1509800975, 387375750, 73250875]]
    hw := by decide
    g := ![![![-55791, 7349, -868], ![61612, 0, 0]], ![![6558, -1464, 223], ![-7144, 0, 0]]]
    h := ![![![9605436, 245472248, -728930664], ![4269088, 12885870109, 0]], ![![1158911, 29616564, -87946489], ![515122, 1554697984, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {25} * I53N1 =  Ideal.span {B.equivFun.symm ![500549932, 128428123, 24285135]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS1 


noncomputable def E67RS0 : RelationCertificate Table 25 ![![67, 0, 0], ![-30, 1, 0]]
  ![2580791, 662164, 125212] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![1675, 0, 0], ![-750, 25, 0]]
    hsu := by decide
    w := ![![64519775, 16554100, 3130300], ![7784400, 1997275, 377675]]
    hw := by decide
    g := ![![![-2715, 644, -100], ![2976, 0, 0]], ![![1270, -362, 59], ![-1367, 0, 0]]]
    h := ![![![2490060713, -92979570, 1035184], ![5561049566, -23077372, 0]], ![![300429288, -11218101, 124895], ![670948364, -2784286, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {25} * I67N0 =  Ideal.span {B.equivFun.symm ![2580791, 662164, 125212]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 125 ![![67, 0, 0], ![-19, 1, 0]]
  ![1054, 216, -57] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![8375, 0, 0], ![-2375, 125, 0]]
    hsu := by decide
    w := ![![131750, 27000, -7125], ![542875, 51875, -17375]]
    hw := by decide
    g := ![![![-3272, -657, -204], ![1584, 0, 0]], ![![182, 46, 9], ![-6, 0, 0]]]
    h := ![![![2627034, -147104, 1473], ![9263696, -32916, 0]], ![![10832929, -606583, 6071], ![38200100, -135632, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {125} * I67N1 =  Ideal.span {B.equivFun.symm ![1054, 216, -57]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E67RS1 


noncomputable def E73RS0 : RelationCertificate Table 5 ![![73, 0, 0], ![4, 1, 0]]
  ![4, 1, 0] ![![5, 0, 0], ![-38, -3, 1]] where
    su := ![![365, 0, 0], ![20, 5, 0]]
    hsu := by decide
    w := ![![20, 5, 0], ![175, 5, -5]]
    hw := by decide
    g := ![![![30, 4, -1], ![8, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![68, 17, 0], ![-1240, 0, 0]], ![![599, 148, -1], ![-10923, 24, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N0 : Ideal.span {5} * I73N0 =  Ideal.span {B.equivFun.symm ![4, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS0 


noncomputable def E73RS1 : RelationCertificate Table 5 ![![73, 0, 0], ![15, 1, 0]]
  ![93825244, 1913636, -1579735] ![![5, 0, 0], ![-38, -3, 1]] where
    su := ![![365, 0, 0], ![75, 5, 0]]
    hsu := by decide
    w := ![![469126220, 9568180, -7898675], ![-1217689150, -146261145, 45007820]]
    hw := by decide
    g := ![![![370106895486, 12832505688760, 5384182454617], ![-9435479327847, 0, 0]], ![![156484384000, 5425693960907, 2276478728080], ![-3989401949159, 0, 0]]]
    h := ![![![6244053628, 435678692, 3628595], ![-30381472640, -88822390, 0]], ![![-16208318270, -1131250213, -9348695], ![78864246392, 230485433, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {5} * I73N1 =  Ideal.span {B.equivFun.symm ![93825244, 1913636, -1579735]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS1 


noncomputable def E73RS2 : RelationCertificate Table 25 ![![73, 0, 0], ![-20, 1, 0]]
  ![2594759, 1526676, -341115] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![1825, 0, 0], ![-500, 25, 0]]
    hsu := by decide
    w := ![![64868975, 38166900, -8527875], ![798385150, 55608450, -21378775]]
    hw := by decide
    g := ![![![-589129015973, -266307908058, -93491847716], ![688041772997, 0, 0]], ![![33370293799, 15084595883, 5295699820], ![-38973052531, 0, 0]]]
    h := ![![![529571843, -26482038, -546], ![1932807489, -100419, 0]], ![![6572024262, -328855728, 36737], ![23986291786, -1178984, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N2 : Ideal.span {25} * I73N2 =  Ideal.span {B.equivFun.symm ![2594759, 1526676, -341115]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E73RS2 


noncomputable def E79RS1 : RelationCertificate Table 5 ![![79, 0, 0], ![-14, 1, 0]]
  ![-49199, -3276, 1287] ![![5, 0, 0], ![-38, -3, 1]] where
    su := ![![395, 0, 0], ![-70, 5, 0]]
    hsu := by decide
    w := ![![-245995, -16380, 6435], ![-604520, 8250, 6025]]
    hw := by decide
    g := ![![![-77489, -2687859, -1127757], ![1976334, 0, 0]], ![![-1793, -63452, -26625], ![46662, 0, 0]]]
    h := ![![![-997099, 71427, -51], ![-5622973, 1772, 0]], ![![-2453052, 175824, -145], ![-13833586, 4220, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {5} * I79N1 =  Ideal.span {B.equivFun.symm ![-49199, -3276, 1287]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS1 
