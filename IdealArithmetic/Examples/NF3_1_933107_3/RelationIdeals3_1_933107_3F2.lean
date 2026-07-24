import IdealArithmetic.Examples.NF3_1_933107_3.PrimesBelow3_1_933107_3F2
import IdealArithmetic.Examples.NF3_1_933107_3.ClassGroupData3_1_933107_3

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 50 ![![83, 0, 0], ![39, 1, 0]]
  ![79, 3, 2] ![![50, 0, 0], ![12, 1, 0]] where
    su := ![![4150, 0, 0], ![1950, 50, 0]]
    hsu := by decide
    w := ![![3950, 150, 100], ![1000, 50, 50]]
    hw := by decide
    g := ![![![16550162, 95241227, 70124707], ![5876865, -436512769, -1087169]], ![![7832902, 45076012, 33188801], ![2781422, -206593882, -514538]]]
    h := ![![![1361, 35773, 7534], ![1114, -78165, 0]], ![![313, 9054, 1907], ![349, -19785, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {50} * I83N1 =  Ideal.span {B.equivFun.symm ![79, 3, 2]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 100 ![![89, 0, 0], ![30, 1, 0]]
  ![64119, -67, 2072] ![![100, 0, 0], ![-38, 1, 0]] where
    su := ![![8900, 0, 0], ![3000, 100, 0]]
    hsu := by decide
    w := ![![6411900, -6700, 207200], ![-2389000, 2500, -77200]]
    hw := by decide
    g := ![![![-21326685853504033795, 513867186569579003771, -105435818398872545058], ![13242812490027322973, 1317947729985853468114, -11534076]], ![![-7372187701342434663, 177633101503638281928, -36446949564525574301], ![4577762341546508096, 455586869556551238477, -3987088]]]
    h := ![![![114403, 1943019, 536216], ![60418, -5965144, 0]], ![![-42630, -723947, -199788], ![-22497, 2222545, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {100} * I89N1 =  Ideal.span {B.equivFun.symm ![64119, -67, 2072]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E89RS1 


noncomputable def E97RS0 : RelationCertificate Table 20 ![![97, 0, 0], ![12, 1, 0]]
  ![6559, -7, 212] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![1940, 0, 0], ![240, 20, 0]]
    hsu := by decide
    w := ![![131180, -140, 4240], ![17980, -20, 580]]
    hw := by decide
    g := ![![![30923396898, 18736897472, 132163913495], ![4029184577, -330987760034, 1541270127]], ![![3506720803, 2124768775, 14987420257], ![456910539, -37534093296, 174780411]]]
    h := ![![![211951, 1191191, 866612], ![38550, -10507644, 0]], ![![29051, 163269, 118781], ![5282, -1440216, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N0 : Ideal.span {20} * I97N0 =  Ideal.span {B.equivFun.symm ![6559, -7, 212]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E97RS0 


noncomputable def E97RS1 : RelationCertificate Table 20 ![![97, 0, 0], ![30, 1, 0]]
  ![7, -11, -4] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![1940, 0, 0], ![600, 20, 0]]
    hsu := by decide
    w := ![![140, -220, -80], ![-100, 120, -100]]
    hw := by decide
    g := ![![![501290376, 250645706, 2030227477], ![62661331, -5075568783, 215]], ![![160890234, 80445283, 651605914], ![20111294, -1629014814, 69]]]
    h := ![![![-65, -711, -196], ![52, 2376, 0]], ![![1, 503, 139], ![109, -1686, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {20} * I97N1 =  Ideal.span {B.equivFun.symm ![7, -11, -4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E97RS1 


noncomputable def E97RS2 : RelationCertificate Table 20 ![![97, 0, 0], ![-42, 1, 0]]
  ![123, 1, 4] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![1940, 0, 0], ![-840, 20, 0]]
    hsu := by decide
    w := ![![2460, 20, 80], ![340, 0, 20]]
    hw := by decide
    g := ![![![21384748154, 10694632915, 86613005477], ![2673206477, -216532912311, 1062983]], ![![-8897316565, -4449598091, -36036118949], ![-1112211551, 90090463221, -442263]]]
    h := ![![![955, -26159, 4868], ![-608, -59024, 0]], ![![155, -3617, 673], ![-31, -8160, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N2 : Ideal.span {20} * I97N2 =  Ideal.span {B.equivFun.symm ![123, 1, 4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E97RS2 


noncomputable def E101RS1 : RelationCertificate Table 10 ![![101, 0, 0], ![-15, 1, 0]]
  ![807, -1, 26] ![![10, 0, 0], ![2, 1, 0]] where
    su := ![![1010, 0, 0], ![-150, 10, 0]]
    hsu := by decide
    w := ![![8070, -10, 260], ![2210, 0, 70]]
    hw := by decide
    g := ![![![3268749628, 1634469204, 13728953659], ![817196855, -17161200403, 22209]], ![![-78870, -39435, -331247], ![-19709, 414059, 0]]]
    h := ![![![9161, -75663, 37842], ![-2070, -477752, 0]], ![![2520, -20721, 10363], ![-491, -130832, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {10} * I101N1 =  Ideal.span {B.equivFun.symm ![807, -1, 26]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 100 ![![103, 0, 0], ![-29, 1, 0]]
  ![1471, -3, 48] ![![100, 0, 0], ![-38, 1, 0]] where
    su := ![![10300, 0, 0], ![-2900, 100, 0]]
    hsu := by decide
    w := ![![147100, -300, 4800], ![-54800, 100, -1800]]
    hw := by decide
    g := ![![![-698537901, 16831294700, -3453463144], ![433757370, 43168288089, -262]], ![![191805845, -4621568071, 948258306], ![-119101864, -11853228492, 72]]]
    h := ![![![18555762, -313160498, 83530864], ![-8264749, -1075459868, 0]], ![![-6912646, 116663109, -31118134], ![3078964, 400645973, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {100} * I103N1 =  Ideal.span {B.equivFun.symm ![1471, -3, 48]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E103RS1 


noncomputable def E107RS0 : RelationCertificate Table 2 ![![107, 0, 0], ![1, 1, 0]]
  ![1, 1, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![214, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![2, 2, 0], ![2, 0, 8]]
    hw := by decide
    g := ![![![-19580, 21178, -852], ![10591, 0, 1708]], ![![-9820, 10589, -427], ![5296, 0, 854]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![-3, 0, -12], ![0, 161, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {2} * I107N0 =  Ideal.span {B.equivFun.symm ![1, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 100 ![![107, 0, 0], ![13, 1, 0]]
  ![1, 7, -12] ![![100, 0, 0], ![-38, 1, 0]] where
    su := ![![10700, 0, 0], ![1300, 100, 0]]
    hsu := by decide
    w := ![![100, 700, -1200], ![-300, 100, 500]]
    hw := by decide
    g := ![![![-4190248410348742, 100964202045606226, -20715945819614265], ![2601936416388667, 258949291104053010, -6841324391]], ![![-469981193135374, 11324215534374049, -2323514975671875], ![291835008735263, 29043933647007687, -767327730]]]
    h := ![![![-4, -6, -4], ![25, 52, 0]], ![![-2, 22, 15], ![47, -200, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {100} * I107N1 =  Ideal.span {B.equivFun.symm ![1, 7, -12]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E107RS1 


noncomputable def E107RS2 : RelationCertificate Table 5 ![![107, 0, 0], ![-14, 1, 0]]
  ![9, -12, 2] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![535, 0, 0], ![-70, 5, 0]]
    hsu := by decide
    w := ![![45, -60, 10], ![40, -65, -90]]
    hw := by decide
    g := ![![![-1275, 113, 70], ![-483, -74, 0]], ![![160, -13, 6], ![64, 0, 0]]]
    h := ![![![541, -4091, 2182], ![-35, -29184, 0]], ![![484, -3649, 1946], ![-20, -26030, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N2 : Ideal.span {5} * I107N2 =  Ideal.span {B.equivFun.symm ![9, -12, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E107RS2 


noncomputable def E109RS1 : RelationCertificate Table 4 ![![109, 0, 0], ![28, 1, 0]]
  ![-989, 1, -32] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![436, 0, 0], ![112, 4, 0]]
    hsu := by decide
    w := ![![-3956, 4, -128], ![-2712, 4, -88]]
    hw := by decide
    g := ![![![656, -965, 89], ![87, 0, -122]], ![![181, -269, 25], ![27, 0, -34]]]
    h := ![![![-11003, -163121, -48344], ![-4251, 658683, 0]], ![![-7548, -111827, -33142], ![-2895, 451557, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {4} * I109N1 =  Ideal.span {B.equivFun.symm ![-989, 1, -32]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E109RS1 


noncomputable def E127RS1 : RelationCertificate Table 20 ![![127, 0, 0], ![-21, 1, 0]]
  ![-3, -1, -4] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![2540, 0, 0], ![-420, 20, 0]]
    hsu := by decide
    w := ![![-60, -20, -80], ![-100, 120, -20]]
    hw := by decide
    g := ![![![-1196613198, -598307615, -4846285487], ![-149576693, 12115713897, -487]], ![![196588280, 98294307, 796182875], ![24573557, -1990457217, 80]]]
    h := ![![![642, -7314, 2660], ![-139, -42228, 0]], ![![1372, -15489, 5633], ![-219, -89424, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {20} * I127N1 =  Ideal.span {B.equivFun.symm ![-3, -1, -4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 5 ![![131, 0, 0], ![-31, 1, 0]]
  ![12, -16, 1] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![655, 0, 0], ![-155, 5, 0]]
    hsu := by decide
    w := ![![60, -80, 5], ![15, -35, -125]]
    hw := by decide
    g := ![![![1944, -290, -1061], ![723, 714, 0]], ![![-449, 67, 250], ![-164, -168, 0]]]
    h := ![![![-3940, 68936, -17237], ![1560, 282256, 0]], ![![-1006, 17672, -4419], ![417, 72358, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {5} * I131N1 =  Ideal.span {B.equivFun.symm ![12, -16, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E131RS1 


noncomputable def E137RS0 : RelationCertificate Table 25 ![![137, 0, 0], ![-52, 1, 0]]
  ![-21, 28, 2] ![![25, 0, 0], ![12, 1, 0]] where
    su := ![![3425, 0, 0], ![-1300, 25, 0]]
    hsu := by decide
    w := ![![-525, 700, 50], ![-150, 225, 250]]
    hw := by decide
    g := ![![![1563, 13792, 10058], ![1312, -31464, 0]], ![![-602, -5198, -3790], ![-469, 11856, 0]]]
    h := ![![![-1477, 48846, -7374], ![966, 126280, 0]], ![![-408, 13977, -2110], ![315, 36135, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {25} * I137N0 =  Ideal.span {B.equivFun.symm ![-21, 28, 2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 25 ![![137, 0, 0], ![-33, 1, 0]]
  ![-9, 12, 8] ![![25, 0, 0], ![12, 1, 0]] where
    su := ![![3425, 0, 0], ![-825, 25, 0]]
    hsu := by decide
    w := ![![-225, 300, 200], ![100, -125, 200]]
    hw := by decide
    g := ![![![-767, -4679, -3424], ![-534, 10683, 0]], ![![171, 1060, 776], ![130, -2421, 0]]]
    h := ![![![-477, 9416, -2216], ![320, 37950, 0]], ![![253, -4182, 984], ![29, -16850, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {25} * I137N1 =  Ideal.span {B.equivFun.symm ![-9, 12, 8]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E137RS1 
