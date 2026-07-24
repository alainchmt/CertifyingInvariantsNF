import IdealArithmetic.Examples.NF3_1_884199_1.PrimesBelow3_1_884199_1F2
import IdealArithmetic.Examples.NF3_1_884199_1.ClassGroupData3_1_884199_1

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 25 ![![83, 0, 0], ![24, 1, 0]]
  ![168413904, 1370191, -2418887] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![2075, 0, 0], ![600, 25, 0]]
    hsu := by decide
    w := ![![4210347600, 34254775, -60472175], ![-1630950025, -311018900, 83515575]]
    hw := by decide
    g := ![![![27491534906319, 12427181400808, 4362769996257], ![-32107270063319, 0, 0]], ![![13204226915454, 5968794528743, 2095445205468], ![-15421171680495, 0, 0]]]
    h := ![![![-71493912, 22820011752, 2738737901], ![254267025, -75772554890, 0]], ![![27579517, -8803995971, -1056563109], ![-98097413, 29232692890, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {25} * I83N0 =  Ideal.span {B.equivFun.symm ![168413904, 1370191, -2418887]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E83RS0 


noncomputable def E83RS1 : RelationCertificate Table 125 ![![83, 0, 0], ![29, 1, 0]]
  ![2989597, 767053, 145046] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![10375, 0, 0], ![3625, 125, 0]]
    hsu := by decide
    w := ![![373699625, 95881625, 18130750], ![-1251473500, -321095625, -60717625]]
    hw := by decide
    g := ![![![-2257, -221, 118], ![1049, 0, 0]], ![![-357, -62, 26], ![210, 0, 0]]]
    h := ![![![-9123578, 2440461618, 244078570], ![26215399, -6752792088, 0]], ![![30553719, -8172802000, -817388731], ![-87792085, 22614259644, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {125} * I83N1 =  Ideal.span {B.equivFun.symm ![2989597, 767053, 145046]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E83RS1 


noncomputable def E89RS0 : RelationCertificate Table 125 ![![89, 0, 0], ![18, 1, 0]]
  ![3072, 788, 149] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![11125, 0, 0], ![2250, 125, 0]]
    hsu := by decide
    w := ![![384000, 98500, 18625], ![-1285625, -329875, -62375]]
    hw := by decide
    g := ![![![98, 1, 0], ![34, 0, 0]], ![![62, 23, -1], ![104, 0, 0]]]
    h := ![![![-147792, -8208, 1], ![730920, 20, 0]], ![![494701, 27426, -11], ![-2446593, 160, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N0 : Ideal.span {125} * I89N0 =  Ideal.span {B.equivFun.symm ![3072, 788, 149]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E89RS0 


noncomputable def E89RS1 : RelationCertificate Table 25 ![![89, 0, 0], ![19, 1, 0]]
  ![21574, 1851, -648] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![2225, 0, 0], ![475, 25, 0]]
    hsu := by decide
    w := ![![539350, 46275, -16200], ![707525, 27375, -14525]]
    hw := by decide
    g := ![![![-394192, -178194, -62559], ![460404, 0, 0]], ![![-154421, -69806, -24507], ![180360, 0, 0]]]
    h := ![![![6542696, 370089, 3852], ![-30646230, -114492, 0]], ![![8579784, 485320, 5057], ![-40188025, -150218, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {25} * I89N1 =  Ideal.span {B.equivFun.symm ![21574, 1851, -648]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E89RS1 


noncomputable def E89RS2 : RelationCertificate Table 125 ![![89, 0, 0], ![-38, 1, 0]]
  ![-39, -11, -2] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![11125, 0, 0], ![-4750, 125, 0]]
    hsu := by decide
    w := ![![-4875, -1375, -250], ![17000, 4375, 875]]
    hw := by decide
    g := ![![![60, 21, -1], ![94, 0, 0]], ![![-4, 3, 0], ![13, 0, 0]]]
    h := ![![![-194943, 5882, -61], ![-456576, 1809, 0]], ![![680000, -20360, 200], ![1592628, -5931, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N2 : Ideal.span {125} * I89N2 =  Ideal.span {B.equivFun.symm ![-39, -11, -2]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E89RS2 


noncomputable def E103RS0 : RelationCertificate Table 5 ![![103, 0, 0], ![42, 1, 0]]
  ![-20, -5, -1] ![![5, 0, 0], ![-38, -3, 1]] where
    su := ![![515, 0, 0], ![210, 5, 0]]
    hsu := by decide
    w := ![![-100, -25, -5], ![215, 40, 5]]
    hw := by decide
    g := ![![![1, 6, -1], ![13, 0, 0]], ![![26, 4, -1], ![8, 0, 0]]]
    h := ![![![-284, -21, -1], ![696, 34, 0]], ![![367, -20, -2], ![-899, 69, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {5} * I103N0 =  Ideal.span {B.equivFun.symm ![-20, -5, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 125 ![![103, 0, 0], ![-38, 1, 0]]
  ![-175263, -16032, 5465] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![12875, 0, 0], ![-4750, 125, 0]]
    hsu := by decide
    w := ![![-21907875, -2004000, 683125], ![-46586750, -3003375, 1198750]]
    hw := by decide
    g := ![![![11589819, 2347561, 717563], ![-5434178, 0, 0]], ![![-2490639, -504474, -154207], ![1167922, 0, 0]]]
    h := ![![![-2528775, 70084, -250], ![-6849699, 10405, 0]], ![![-5378362, 149102, -547], ![-14568384, 21977, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {125} * I103N1 =  Ideal.span {B.equivFun.symm ![-175263, -16032, 5465]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E103RS1 


noncomputable def E109RS0 : RelationCertificate Table 25 ![![109, 0, 0], ![0, 1, 0]]
  ![0, -5, 1] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![2725, 0, 0], ![0, 25, 0]]
    hsu := by decide
    w := ![![0, -125, 25], ![-2725, -200, 75]]
    hw := by decide
    g := ![![![0, 27, -4], ![297, -49, -22]], ![![0, 10, -2], ![197, 0, -5]]]
    h := ![![![0, -25, -74], ![31, 2689, 0]], ![![-1, -75, -222], ![100, 8067, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {25} * I109N0 =  Ideal.span {B.equivFun.symm ![0, -5, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 5 ![![109, 0, 0], ![38, 1, 0]]
  ![-3150583813, -808358047, -152856585] ![![5, 0, 0], ![-38, -3, 1]] where
    su := ![![545, 0, 0], ![190, 5, 0]]
    hsu := by decide
    w := ![![-15752919065, -4041790235, -764282925], ![22002781175, 5645342665, 1067506910]]
    hw := by decide
    g := ![![![-27069, 18875, -8], ![194563, 0, 0]], ![![-7189, 3533, 316], ![52768, 0, 0]]]
    h := ![![![-545486373741, -16006352324, -127924836], ![1564601688262, 4596983513, 0]], ![![761904334307, 22356762274, 178678129], ![-2185346628506, -6420804893, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {5} * I109N1 =  Ideal.span {B.equivFun.symm ![-3150583813, -808358047, -152856585]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 5 ![![109, 0, 0], ![-39, 1, 0]]
  ![99556, -18851, 2538] ![![5, 0, 0], ![-38, -3, 1]] where
    su := ![![545, 0, 0], ![-195, 5, 0]]
    hsu := by decide
    w := ![![497780, -94255, 12690], ![-12713825, -784105, 319975]]
    hw := by decide
    g := ![![![10321864, 357883054, 150158331], ![-263144094, 0, 0]], ![![-2190771, -75959761, -31870722], ![55851663, 0, 0]]]
    h := ![![![10151248, -261777, 129], ![28368884, -3841, 0]], ![![-258622669, 6664845, -2218], ![-722752004, 101919, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {5} * I109N2 =  Ideal.span {B.equivFun.symm ![99556, -18851, 2538]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS2 


noncomputable def E127RS1 : RelationCertificate Table 125 ![![127, 0, 0], ![-7, 1, 0]]
  ![-148113, -38002, -7186] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![15875, 0, 0], ![-875, 125, 0]]
    hsu := by decide
    w := ![![-18514125, -4750250, -898250], ![62001625, 15908000, 3008125]]
    hw := by decide
    g := ![![![-797, -34, 36], ![446, 0, 0]], ![![138, 7, -5], ![-43, 0, 0]]]
    h := ![![![-131156396, 18777325, -20638], ![-2379530597, 871280, 0]], ![![439227334, -62883049, 69113], ![7968767915, -2917762, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {125} * I127N1 =  Ideal.span {B.equivFun.symm ![-148113, -38002, -7186]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 5 ![![131, 0, 0], ![53, 1, 0]]
  ![45124, -1219, -328] ![![5, 0, 0], ![-38, -3, 1]] where
    su := ![![655, 0, 0], ![265, 5, 0]]
    hsu := by decide
    w := ![![225620, -6095, -1640], ![-1755805, -134775, 49535]]
    hw := by decide
    g := ![![![-267084, -9260935, -3885646], ![6809379, 0, 0]], ![![-140385, -4868354, -2042635], ![3579606, 0, 0]]]
    h := ![![![11041900, 238949, 1699], ![-27291392, -74299, 0]], ![![-85931102, -1860044, -13177], ![212389117, 578698, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {5} * I131N1 =  Ideal.span {B.equivFun.symm ![45124, -1219, -328]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E131RS1 


noncomputable def E137RS0 : RelationCertificate Table 25 ![![137, 0, 0], ![-61, 1, 0]]
  ![-80, -5, 2] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![3425, 0, 0], ![-1525, 25, 0]]
    hsu := by decide
    w := ![![-2000, -125, 50], ![-1575, -25, 25]]
    hw := by decide
    g := ![![![12, 0, -1], ![12, 0, 0]], ![![5, 1, 0], ![5, 0, 0]]]
    h := ![![![-656, 51, -2], ![-1472, 92, 0]], ![![-480, 28, -1], ![-1077, 46, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {25} * I137N0 =  Ideal.span {B.equivFun.symm ![-80, -5, 2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 5 ![![137, 0, 0], ![-60, 1, 0]]
  ![-5, 35, -7] ![![5, 0, 0], ![-38, -3, 1]] where
    su := ![![685, 0, 0], ![-300, 5, 0]]
    hsu := by decide
    w := ![![-25, 175, -35], ![19265, 1065, -460]]
    hw := by decide
    g := ![![![9, -763, -322], ![567, 0, 0]], ![![25, 248, 103], ![-179, 0, 0]]]
    h := ![![![-925, 54, -2], ![-2112, 89, 0]], ![![694589, -11627, 2], ![1585914, -122, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {5} * I137N1 =  Ideal.span {B.equivFun.symm ![-5, 35, -7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E137RS1 


noncomputable def E137RS2 : RelationCertificate Table 5 ![![137, 0, 0], ![-17, 1, 0]]
  ![-2288, -587, -111] ![![5, 0, 0], ![-38, -3, 1]] where
    su := ![![685, 0, 0], ![-85, 5, 0]]
    hsu := by decide
    w := ![![-11440, -2935, -555], ![15985, 4100, 775]]
    hw := by decide
    g := ![![![-11, 74, -13], ![101, 0, 0]], ![![15, -12, 2], ![-13, 0, 0]]]
    h := ![![![-112, -124147, 23277], ![-768, -1063020, 0]], ![![188, 173469, -32525], ![1327, 1485360, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N2 : Ideal.span {5} * I137N2 =  Ideal.span {B.equivFun.symm ![-2288, -587, -111]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E137RS2 
