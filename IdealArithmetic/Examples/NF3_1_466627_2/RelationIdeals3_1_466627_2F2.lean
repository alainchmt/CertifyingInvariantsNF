import IdealArithmetic.Examples.NF3_1_466627_2.PrimesBelow3_1_466627_2F2
import IdealArithmetic.Examples.NF3_1_466627_2.ClassGroupData3_1_466627_2

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 1179648 ![![83, 0, 0], ![32, 1, 0]]
  ![44131, 5815, -607] ![![1179648, 0, 0], ![-50519, 1, 0]] where
    su := ![![97910784, 0, 0], ![37748736, 1179648, 0]]
    hsu := by decide
    w := ![![52059045888, 6859653120, -716046336], ![-2229534720, -293732352, 30670848]]
    hw := by decide
    g := ![![![-727593632505, -20078663512145894442, 397447762468780], ![-16989734028727, -468848458100771389393, 0]], ![![-271751820705, -7499259866007915710, 148444345018969], ![-6345562892991, -175112074712936742896, 0]]]
    h := ![![![198545, 7132, 20], ![-513597, -2267, 0]], ![![-8534, -311, -1], ![22076, 109, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {1179648} * I83N1 =  Ideal.span {B.equivFun.symm ![44131, 5815, -607]} * (J0 ^ 11*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_2 E83RS1 


noncomputable def E89RS0 : RelationCertificate Table 36864 ![![89, 0, 0], ![16, 1, 0]]
  ![9035, 767, -359] ![![36864, 0, 0], ![-13655, 1, 0]] where
    su := ![![3280896, 0, 0], ![589824, 36864, 0]]
    hsu := by decide
    w := ![![333066240, 28274688, -13234176], ![-123420672, -10469376, 4902912]]
    hw := by decide
    g := ![![![-22276660376566, -2521175551999340908, 184633874304704], ![-60139641751866, -6806343142368608201, 0]], ![![-3954732959539, -447579480018423106, 32777699033910], ![-10676475710029, -1208317097186058227, 0]]]
    h := ![![![53779, 3476, 3], ![-298581, -626, 0]], ![![-19956, -1304, -2], ![110796, 311, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N0 : Ideal.span {36864} * I89N0 =  Ideal.span {B.equivFun.symm ![9035, 767, -359]} * (J0 ^ 6*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_2 E89RS0 


noncomputable def E89RS1 : RelationCertificate Table 4608 ![![89, 0, 0], ![-8, 1, 0]]
  ![1567, 259, 53] ![![4608, 0, 0], ![169, 1, 0]] where
    su := ![![410112, 0, 0], ![-36864, 4608, 0]]
    hsu := by decide
    w := ![![7220736, 1193472, 244224], ![271872, 46080, 9216]]
    hw := by decide
    g := ![![![-74, 1985412, 11748], ![2021, -54134796, 0]], ![![-163, -165452, -979], ![4444, 4511233, 0]]]
    h := ![![![59018271, -7435138, 7233], ![656578069, -643684, 0]], ![![2222123, -279941, 272], ![24721111, -24206, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {4608} * I89N1 =  Ideal.span {B.equivFun.symm ![1567, 259, 53]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 18432 ![![97, 0, 0], ![15, 1, 0]]
  ![-2245, -721, -23] ![![18432, 0, 0], ![4777, 1, 0]] where
    su := ![![1787904, 0, 0], ![276480, 18432, 0]]
    hsu := by decide
    w := ![![-41379840, -13289472, -423936], ![-10727424, -3446784, -110592]]
    hw := by decide
    g := ![![![-2311, -46336894, -9700], ![8917, 178790375, 0]], ![![-3717, -7404350, -1550], ![14342, 28569597, 0]]]
    h := ![![![-4360, -308, -1], ![28045, 74, 0]], ![![-1146, -92, -1], ![7372, 91, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {18432} * I97N1 =  Ideal.span {B.equivFun.symm ![-2245, -721, -23]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 1536 ![![101, 0, 0], ![-48, 1, 0]]
  ![529, 109, -37] ![![1536, 0, 0], ![169, 1, 0]] where
    su := ![![155136, 0, 0], ![-73728, 1536, 0]]
    hsu := by decide
    w := ![![812544, 167424, -56832], ![84480, 18432, -6144]]
    hw := by decide
    g := ![![![29, -785173, -4646], ![-265, 7136248, 0]], ![![-117, 339182, 2007], ![1064, -3082749, 0]]]
    h := ![![![14813, -325, 0], ![31158, -37, 0]], ![![1547, -34, 0], ![3254, -4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {1536} * I101N1 =  Ideal.span {B.equivFun.symm ![529, 109, -37]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E101RS1 


noncomputable def E107RS0 : RelationCertificate Table 96 ![![107, 0, 0], ![25, 1, 0]]
  ![157, -23, -1] ![![96, 0, 0], ![-23, 1, 0]] where
    su := ![![10272, 0, 0], ![2400, 96, 0]]
    hsu := by decide
    w := ![![15072, -2208, -96], ![-3744, 672, 0]]
    hw := by decide
    g := ![![![-62103, -26313212, 1144170], ![-259208, -109840327, 0]], ![![-13929, -5901931, 256632], ![-58137, -24636674, 0]]]
    h := ![![![951, 38, 0], ![-4064, -1, 0]], ![![-277, -36, -1], ![1184, 107, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {96} * I107N0 =  Ideal.span {B.equivFun.symm ![157, -23, -1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 768 ![![107, 0, 0], ![41, 1, 0]]
  ![-113, -77, 5] ![![768, 0, 0], ![169, 1, 0]] where
    su := ![![82176, 0, 0], ![31488, 768, 0]]
    hsu := by decide
    w := ![![-86784, -59136, 3840], ![-18432, -13056, 768]]
    hw := by decide
    g := ![![![-281983559, 1031800966206, 6105341034], ![1281440079, -4688901914120, 0]], ![![-110844846, 405590438490, 2399947304], ![503720957, -1843159529475, 0]]]
    h := ![![![-1492, -80, -1], ![3891, 112, 0]], ![![-388, -51, -1], ![1012, 108, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {768} * I107N1 =  Ideal.span {B.equivFun.symm ![-113, -77, 5]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 4 ![![109, 0, 0], ![-34, 1, 0]]
  ![23, 7, 1] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![436, 0, 0], ![-136, 4, 0]]
    hsu := by decide
    w := ![![92, 28, 4], ![156, 44, 8]]
    hw := by decide
    g := ![![![-17, 24, 28], ![6, -109, 0]], ![![5, -9, -9], ![3, 35, 0]]]
    h := ![![![3311, -97, 0], ![10614, 1, 0]], ![![5567, -163, 0], ![17846, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {4} * I109N1 =  Ideal.span {B.equivFun.symm ![23, 7, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 384 ![![113, 0, 0], ![23, 1, 0]]
  ![235, 31, -7] ![![384, 0, 0], ![169, 1, 0]] where
    su := ![![43392, 0, 0], ![8832, 384, 0]]
    hsu := by decide
    w := ![![90240, 11904, -2688], ![38784, 5376, -1152]]
    hw := by decide
    g := ![![![12906542034, -13442430930166, -79541463315], ![-29326107343, 30543921912965, 0]], ![![2513135192, -2617482359895, -15488149293], ![-5710319016, 5947449328513, 0]]]
    h := ![![![1650811, 75341, 155], ![-8110496, -17522, 0]], ![![709511, 32367, 66], ![-3485854, -7461, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {384} * I113N1 =  Ideal.span {B.equivFun.symm ![235, 31, -7]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E113RS1 


noncomputable def E113RS2 : RelationCertificate Table 147456 ![![113, 0, 0], ![-25, 1, 0]]
  ![26171, 47, -791] ![![147456, 0, 0], ![-50519, 1, 0]] where
    su := ![![16662528, 0, 0], ![-3686400, 147456, 0]]
    hsu := by decide
    w := ![![3859070976, 6930432, -116637696], ![-1322237952, -2359296, 39960576]]
    hw := by decide
    g := ![![![-17587332984848, -8458045820045560625, 167423064993244], ![-51334305362611, -24687535471643787345, 0]], ![![3686178217787, 1772745427101640952, -35090667415717], ![10759300367822, 5174329454451965965, 0]]]
    h := ![![![99717175092, -4168748044, 7202435], ![450721630369, -813875946, 0]], ![![-34166212434, 1428343029, -2467779], ![-154431279843, 278859298, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N2 : Ideal.span {147456} * I113N2 =  Ideal.span {B.equivFun.symm ![26171, 47, -791]} * (J0 ^ 8*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_2 E113RS2 


noncomputable def E131RS1 : RelationCertificate Table 49152 ![![131, 0, 0], ![11, 1, 0]]
  ![-899, -1367, -1] ![![49152, 0, 0], ![-1367, 1, 0]] where
    su := ![![6438912, 0, 0], ![540672, 49152, 0]]
    hsu := by decide
    w := ![![-44187648, -67190784, -49152], ![1228800, 1867776, 0]]
    hw := by decide
    g := ![![![-2464891090, -4359609380323577, 3189180235645], ![-88627890897, -156754586942423078, 0]], ![![-432767708, -765430087184521, 559934226409], ![-15560642563, -27521887096455171, 0]]]
    h := ![![![-905, -103, -1], ![10696, 130, 0]], ![![19, 2, 0], ![-224, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {49152} * I131N1 =  Ideal.span {B.equivFun.symm ![-899, -1367, -1]} * (J0 ^ 11*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_1 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 32 ![![137, 0, 0], ![47, 1, 0]]
  ![-29, -9, 1] ![![32, 0, 0], ![9, 1, 0]] where
    su := ![![4384, 0, 0], ![1504, 32, 0]]
    hsu := by decide
    w := ![![-928, -288, 32], ![-128, -96, 0]]
    hw := by decide
    g := ![![![-63, 7536, 838], ![223, -26819, 0]], ![![-30, 2589, 288], ![106, -9217, 0]]]
    h := ![![![-310, -54, -1], ![903, 138, 0]], ![![-46, -48, -1], ![134, 137, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {32} * I137N1 =  Ideal.span {B.equivFun.symm ![-29, -9, 1]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E137RS1 
