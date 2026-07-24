import IdealArithmetic.Examples.NF3_1_808623_1.PrimesBelow3_1_808623_1F0
import IdealArithmetic.Examples.NF3_1_808623_1.ClassGroupData3_1_808623_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 25 ![![3, 0, 0], ![1, 1, 0]]
  ![652, 31, -45] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![75, 0, 0], ![25, 25, 0]]
    hsu := by decide
    w := ![![16300, 775, -1125], ![-7375, 250, 200]]
    hw := by decide
    g := ![![![-148687, 234233, 389859], ![3429, -1949656, -1107]], ![![-34682, 51755, 86525], ![697, -433258, -246]]]
    h := ![![![629, -613, -1050], ![7, 621, 0]], ![![-303, 307, 511], ![4, -305, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {25} * I3N0 =  Ideal.span {B.equivFun.symm ![652, 31, -45]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 1 ![![5, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![5, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![681, 16, -4], ![140, 0, -20]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![681, 16, -4], ![140, 0, -20]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {1} * I5N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 25 ![![5, 0, 0], ![2, 1, 0]]
  ![-293, -54, -20] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![125, 0, 0], ![50, 25, 0]]
    hsu := by decide
    w := ![![-7325, -1350, -500], ![-3725, -675, -250]]
    hw := by decide
    g := ![![![842921, -1263032, -2106150], ![-16800, 10530756, 30]], ![![337218, -505288, -842585], ![-6710, 4212927, 12]]]
    h := ![![![-51, -7, -4], ![-19, 0, 0]], ![![-27, -4, -2], ![-7, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {25} * I5N1 =  Ideal.span {B.equivFun.symm ![-293, -54, -20]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 5 ![![7, 0, 0], ![-11, -2, 1]]
  ![-38464333, -7012039, -2588275] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![35, 0, 0], ![-55, -10, 5]]
    hsu := by decide
    w := ![![-192321665, -35060195, -12941375], ![-482564930, -87971475, -32471920]]
    hw := by decide
    g := ![![![248, -186, 63], ![14, 0, 8]], ![![-8680, 383, 410], ![-1656, 0, -14]]]
    h := ![![![-1592881, -292261, -724483], ![2483106, 0, 0]], ![![-3996779, -733327, -1817841], ![6230503, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {5} * I7N0 =  Ideal.span {B.equivFun.symm ![-38464333, -7012039, -2588275]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 25 ![![7, 0, 0], ![-2, 1, 0]]
  ![4304, -538, 85] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![175, 0, 0], ![-50, 25, 0]]
    hsu := by decide
    w := ![![107600, -13450, 2125], ![20425, 3625, -2775]]
    hw := by decide
    g := ![![![428798894836, -642343902170, -1071142645169], ![-8541800281, 5355713231478, -19228]], ![![-77963391521, 116789807582, 194753210029], ![1553056644, -973766036520, 3496]]]
    h := ![![![-618560, -24818, 1671655], ![173188, -2340300, 0]], ![![-106039, -4222, 286587], ![29699, -401244, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {25} * I7N1 =  Ideal.span {B.equivFun.symm ![4304, -538, 85]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 25 ![![11, 0, 0], ![1, 1, 0]]
  ![-129381799, -23586272, -8706135] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![275, 0, 0], ![25, 25, 0]]
    hsu := by decide
    w := ![![-3234544975, -589656800, -217653375], ![-1623195150, -295908100, -109225225]]
    hw := by decide
    g := ![![![49663684963466, -74396595804651, -124060280769615], ![-989316433631, 620301403848742, 43]], ![![8084785928180, -12111073738135, -20195859664386], ![-161051512375, 100979298321580, 7]]]
    h := ![![![5261003095, -7857642253, -13129054590], ![-236058102, 28882178871, 0]], ![![2640134786, -3943208982, -6588567449], ![-118461280, 14493974586, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {25} * I11N0 =  Ideal.span {B.equivFun.symm ![-129381799, -23586272, -8706135]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 25 ![![11, 0, 0], ![3, 1, 0]]
  ![669562, 122061, 45055] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![275, 0, 0], ![75, 25, 0]]
    hsu := by decide
    w := ![![16739050, 3051525, 1126375], ![8400175, 1531350, 565250]]
    hw := by decide
    g := ![![![-153003999982, 229201892044, 382206299994], ![3047915703, -1911031512288, -61830]], ![![-51001333164, 76400630678, 127402099992], ![1015971909, -637010504095, -20610]]]
    h := ![![![2353630, -5808768, -5805420], ![113834, 12780935, 0]], ![![1181125, -2915020, -2913340], ![57124, 6413870, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {25} * I11N1 =  Ideal.span {B.equivFun.symm ![669562, 122061, 45055]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 25 ![![11, 0, 0], ![-4, 1, 0]]
  ![3502067, 638426, 235655] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![275, 0, 0], ![-100, 25, 0]]
    hsu := by decide
    w := ![![87551675, 15960650, 5891375], ![43936150, 8009550, 2956475]]
    hw := by decide
    g := ![![![-3893005160373, 5831752751145, 9724757912167], ![77549903637, -48623789560821, -54]], ![![1009297633291, -1511935897016, -2521233530458], ![-20105530525, 12606167652207, 14]]]
    h := ![![![1231973449, 1378386953, -3372463945], ![-322682437, 7419467810, 0]], ![![618242546, 691717387, -1692407161], ![-161932063, 3723319406, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {25} * I11N2 =  Ideal.span {B.equivFun.symm ![3502067, 638426, 235655]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS2 


noncomputable def E23RS1 : RelationCertificate Table 5 ![![23, 0, 0], ![10, 1, 0]]
  ![-13, 1, 0] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![115, 0, 0], ![50, 5, 0]]
    hsu := by decide
    w := ![![-65, 5, 0], ![-15, -10, 5]]
    hw := by decide
    g := ![![![-3780, -91, 22], ![-769, 0, 111]], ![![-1738, -42, 10], ![-354, 0, 51]]]
    h := ![![![-807, 5141, 2140], ![-114, -9844, 0]], ![![-173, 1061, 442], ![-9, -2033, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {5} * I23N1 =  Ideal.span {B.equivFun.symm ![-13, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E31RS1 : RelationCertificate Table 5 ![![31, 0, 0], ![2, 1, 0]]
  ![2, 1, 0] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![155, 0, 0], ![10, 5, 0]]
    hsu := by decide
    w := ![![10, 5, 0], ![0, 5, 5]]
    hw := by decide
    g := ![![![2024152, 48057, -11904], ![414446, 0, -59521]], ![![131439, 3120, -773], ![26915, 0, -3865]]]
    h := ![![![12, -24, -30], ![1, 186, 0]], ![![-2, 0, 1], ![25, -6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {5} * I31N1 =  Ideal.span {B.equivFun.symm ![2, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS1 
