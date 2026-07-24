import IdealArithmetic.Examples.NF3_1_780300_2.PrimesBelow3_1_780300_2F2
import IdealArithmetic.Examples.NF3_1_780300_2.ClassGroupData3_1_780300_2

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 23 ![![83, 0, 0], ![-2, 1, 0]]
  ![-123, 21, -1] ![![23, 0, 0], ![-4, 1, 0]] where
    su := ![![1909, 0, 0], ![-46, 23, 0]]
    hsu := by decide
    w := ![![-2829, 483, -23], ![322, -207, 46]]
    hw := by decide
    g := ![![![-62683, -8535884, 4275769], ![-360224, -49171360, 0]], ![![336, 45727, -22906], ![1944, 263418, 0]]]
    h := ![![![-5669, 2837, -3], ![-235202, 124, 0]], ![![646, -323, 0], ![26802, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {23} * I83N1 =  Ideal.span {B.equivFun.symm ![-123, 21, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 253 ![![89, 0, 0], ![32, 1, 0]]
  ![-101, -31, -4] ![![253, 0, 0], ![111, 1, 0]] where
    su := ![![22517, 0, 0], ![8096, 253, 0]]
    hsu := by decide
    w := ![![-25553, -7843, -1012], ![-11891, -3542, -506]]
    hw := by decide
    g := ![![![295, -217112, -3912], ![-672, 494865, 0]], ![![61, -84026, -1514], ![-139, 191520, 0]]]
    h := ![![![-444653, -16839, -184], ![1236688, 8186, 0]], ![![-206919, -7842, -86], ![575492, 3826, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {253} * I89N1 =  Ideal.span {B.equivFun.symm ![-101, -31, -4]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E89RS1 


noncomputable def E101RS1 : RelationCertificate Table 23 ![![101, 0, 0], ![4, 1, 0]]
  ![-9, 15, -4] ![![23, 0, 0], ![-4, 1, 0]] where
    su := ![![2323, 0, 0], ![92, 23, 0]]
    hsu := by decide
    w := ![![-207, 345, -92], ![-644, -69, 46]]
    hw := by decide
    g := ![![![-18053, -2457644, 1231074], ![-103693, -14157360, 0]], ![![-2180, -296772, 148658], ![-12523, -1709568, 0]]]
    h := ![![![-773, -197, -2], ![19516, 99, 0]], ![![-2404, -605, -2], ![60694, 102, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {23} * I101N1 =  Ideal.span {B.equivFun.symm ![-9, 15, -4]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 121 ![![103, 0, 0], ![17, 1, 0]]
  ![47, -25, 6] ![![121, 0, 0], ![-32, 1, 0]] where
    su := ![![12463, 0, 0], ![2057, 121, 0]]
    hsu := by decide
    w := ![![5687, -3025, 726], ![-484, 847, -242]]
    hw := by decide
    g := ![![![9842125, 4818014803, -301145148], ![37215528, 18219281458, 0]], ![![1721291, 842614242, -52666752], ![6508630, 3186338497, 0]]]
    h := ![![![67214, 4089, 16], ![-407235, -821, 0]], ![![-5716, -353, -2], ![34632, 102, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {121} * I103N0 =  Ideal.span {B.equivFun.symm ![47, -25, 6]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 253 ![![103, 0, 0], ![25, 1, 0]]
  ![863, 72, -56] ![![253, 0, 0], ![111, 1, 0]] where
    su := ![![26059, 0, 0], ![6325, 253, 0]]
    hsu := by decide
    w := ![![218339, 18216, -14168], ![86273, 8855, -6072]]
    hw := by decide
    g := ![![![1099, -798350, -14384], ![-2454, 1819692, 0]], ![![207, -201700, -3634], ![-456, 459737, 0]]]
    h := ![![![5896, 243, 0], ![-24257, -28, 0]], ![![2322, 96, 0], ![-9553, -12, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {253} * I103N1 =  Ideal.span {B.equivFun.symm ![863, 72, -56]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 529 ![![103, 0, 0], ![-42, 1, 0]]
  ![217, -32, 7] ![![529, 0, 0], ![-142, 1, 0]] where
    su := ![![54487, 0, 0], ![-22218, 529, 0]]
    hsu := by decide
    w := ![![114793, -16928, 3703], ![-29624, 4761, -1058]]
    hw := by decide
    g := ![![![829233023, 1751929881544, -24675151003], ![3089184993, 6526577440294, 0]], ![![-339475568, -717214012833, 10101639486], ![-1264666024, -2671883644047, 0]]]
    h := ![![![3661, -65, -1], ![8973, 55, 0]], ![![-896, 63, -2], ![-2196, 102, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {529} * I103N2 =  Ideal.span {B.equivFun.symm ![217, -32, 7]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E103RS2 


noncomputable def E107RS1 : RelationCertificate Table 64009 ![![107, 0, 0], ![38, 1, 0]]
  ![-359573, -51420, -14739] ![![64009, 0, 0], ![-5961, 1, 0]] where
    su := ![![6848963, 0, 0], ![2432342, 64009, 0]]
    hsu := by decide
    w := ![![-23015908157, -3291342780, -943428651], ![2140909023, 306155047, 87756339]]
    hw := by decide
    g := ![![![-5800, -6291856354, 2111007], ![-62279, -67561723440, 0]], ![![2108, -2394819825, 803496], ![22636, -25715487696, 0]]]
    h := ![![![-3241289, -97303, -749], ![9117325, 32702, 0]], ![![301491, 9038, 69], ![-848055, -3006, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {64009} * I107N1 =  Ideal.span {B.equivFun.symm ![-359573, -51420, -14739]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E107RS1 


noncomputable def E131RS1 : RelationCertificate Table 5819 ![![131, 0, 0], ![58, 1, 0]]
  ![1151, 213, 3] ![![5819, 0, 0], ![-142, 1, 0]] where
    su := ![![762289, 0, 0], ![337502, 5819, 0]]
    hsu := by decide
    w := ![![6697669, 1239447, 17457], ![-162932, -29095, 0]]
    hw := by decide
    g := ![![![-8524093, -2033857793076, 28645885255], ![-349307728, -83345203149415, 0]], ![![-3767534, -898934090226, 12661043898], ![-154389299, -36837307221228, 0]]]
    h := ![![![20311, 438, 3], ![-45855, -195, 0]], ![![-520, -67, -2], ![1174, 131, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {5819} * I131N1 =  Ideal.span {B.equivFun.symm ![1151, 213, 3]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 2783 ![![137, 0, 0], ![-46, 1, 0]]
  ![-2297, -189, 147] ![![2783, 0, 0], ![-395, 1, 0]] where
    su := ![![381271, 0, 0], ![-128018, 2783, 0]]
    hsu := by decide
    w := ![![-6392551, -525987, 409101], ![932305, 72358, -58443]]
    hw := by decide
    g := ![![![744, 12260590, -62079], ![5251, 86382855, 0]], ![![13, -4051512, 20514], ![89, -28545210, 0]]]
    h := ![![![-3683, 126, -1], ![-10919, 142, 0]], ![![585, 7, -1], ![1735, 58, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {2783} * I137N1 =  Ideal.span {B.equivFun.symm ![-2297, -189, 147]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E137RS1 
