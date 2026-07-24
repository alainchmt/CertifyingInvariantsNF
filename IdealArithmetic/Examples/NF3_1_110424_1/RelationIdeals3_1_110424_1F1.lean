import IdealArithmetic.Examples.NF3_1_110424_1.PrimesBelow3_1_110424_1F1
import IdealArithmetic.Examples.NF3_1_110424_1.ClassGroupData3_1_110424_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 3 ![![37, 0, 0], ![7, 1, 0]]
  ![104398836467375, 8944772181864, 8066845761632] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![111, 0, 0], ![21, 3, 0]]
    hsu := by decide
    w := ![![313196509402125, 26834316545592, 24200537284896], ![381367762071009, 32675151032919, 29468095806288]]
    hw := by decide
    g := ![![![-914114, 1061925, -2800992], ![658681, 0, 0]], ![![-4029221, 531365, -170704], ![1520198, 0, 0]]]
    h := ![![![-8722675170499591, -41550528940205798, -27750263755006768], ![-2773223111721682, 171127970963502008, 0]], ![![-10621277725591458, -50594536526100457, -33790465945261142], ![-3376850827168643, 208376177112210725, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {3} * I37N1 =  Ideal.span {B.equivFun.symm ![104398836467375, 8944772181864, 8066845761632]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E37RS2 : RelationCertificate Table 3 ![![37, 0, 0], ![-8, 1, 0]]
  ![-141, 14, 44] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![111, 0, 0], ![-24, 3, 0]]
    hsu := by decide
    w := ![![-423, 42, 132], ![2721, -567, -48]]
    hw := by decide
    g := ![![![96020, 17677, 8092], ![-26113, 0, 0]], ![![-8685, -1600, -732], ![2365, 0, 0]]]
    h := ![![![-17517, 55842, -55984], ![5312, 345242, 0]], ![![113239, -360913, 361832], ![-34208, -2231300, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N2 : Ideal.span {3} * I37N2 =  Ideal.span {B.equivFun.symm ![-141, 14, 44]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS2 


noncomputable def E41RS1 : RelationCertificate Table 3 ![![41, 0, 0], ![-7, 1, 0]]
  ![-3328149, 730697, -41632] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![123, 0, 0], ![-21, 3, 0]]
    hsu := by decide
    w := ![![-9984447, 2192091, -124896], ![2374887, -2181132, 4509078]]
    hw := by decide
    g := ![![![-12672749413099, -2333072036357, -1067988293314], ![3446559125584, 0, 0]], ![![725441146976, 133554795321, 61136113972], ![-197295450549, 0, 0]]]
    h := ![![![-33067921, 85596941, -102922304], ![7733476, 703295472, 0]], ![![8021146, -20777381, 25003150], ![-1876193, -170604354, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {3} * I41N1 =  Ideal.span {B.equivFun.symm ![-3328149, 730697, -41632]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E47RS1 : RelationCertificate Table 3 ![![47, 0, 0], ![-6, 1, 0]]
  ![269343, 23077, 20812] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![141, 0, 0], ![-18, 3, 0]]
    hsu := by decide
    w := ![![808029, 69231, 62436], ![983907, 84300, 76026]]
    hw := by decide
    g := ![![![-755, 43, 134], ![266, 0, 0]], ![![249, -28, -6], ![-89, 0, 0]]]
    h := ![![![1751567, -3561242, 5352596], ![-299349, -41925200, 0]], ![![2132815, -4336392, 6517658], ![-364532, -51050764, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {3} * I47N1 =  Ideal.span {B.equivFun.symm ![269343, 23077, 20812]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS1 


noncomputable def E59RS1 : RelationCertificate Table 3 ![![59, 0, 0], ![-2, 1, 0]]
  ![530481, 45451, 40990] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![177, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![1591443, 136353, 122970], ![1937841, 166032, 149736]]
    hw := by decide
    g := ![![![829, -13, -248], ![-280, 0, 0]], ![![-248, 27, 6], ![92, 0, 0]]]
    h := ![![![-91397053, -51727, -274532422], ![3097344, 2699575648, 0]], ![![-111290795, -62986, -334287928], ![3771518, 3287172944, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {3} * I59N1 =  Ideal.span {B.equivFun.symm ![530481, 45451, 40990]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 


noncomputable def E71RS1 : RelationCertificate Table 3 ![![71, 0, 0], ![-24, 1, 0]]
  ![91651, -24603, 13240] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![213, 0, 0], ![-72, 3, 0]]
    hsu := by decide
    w := ![![274953, -73809, 39720], ![627063, -65352, -187338]]
    hw := by decide
    g := ![![![21652829332, 3986318120, 1824779098], ![-5888837069, 0, 0]], ![![-5900246977, -1086244254, -497239746], ![1604667575, 0, 0]]]
    h := ![![![4647979, -60067514, 16391426], ![-2417131, -193963001, 0]], ![![10574763, -136661085, 37291366], ![-5499333, -441291572, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {3} * I71N1 =  Ideal.span {B.equivFun.symm ![91651, -24603, 13240]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E71RS1 


noncomputable def E79RS0 : RelationCertificate Table 3 ![![79, 0, 0], ![4, 1, 0]]
  ![27, 2, 2] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![237, 0, 0], ![12, 3, 0]]
    hsu := by decide
    w := ![![81, 6, 6], ![93, 9, 6]]
    hw := by decide
    g := ![![![3, 0, -2], ![2, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
    h := ![![![-95, -286, -286], ![0, 3766, 0]], ![![-109, -328, -328], ![1, 4319, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {3} * I79N0 =  Ideal.span {B.equivFun.symm ![27, 2, 2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS0 


noncomputable def E79RS2 : RelationCertificate Table 3 ![![79, 0, 0], ![-33, 1, 0]]
  ![59, -69, 152] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![237, 0, 0], ![-99, 3, 0]]
    hsu := by decide
    w := ![![177, -207, 456], ![8619, -1530, -870]]
    hw := by decide
    g := ![![![1157291, 213059, 97530], ![-314744, 0, 0]], ![![-415262, -76451, -34996], ![112939, 0, 0]]]
    h := ![![![16174, -320250, 62012], ![-10765, -816466, 0]], ![![775366, -15367562, 2975632], ![-518405, -39179203, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {3} * I79N2 =  Ideal.span {B.equivFun.symm ![59, -69, 152]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS2 
