import IdealArithmetic.Examples.NF3_1_410700_2.PrimesBelow3_1_410700_2F1
import IdealArithmetic.Examples.NF3_1_410700_2.ClassGroupData3_1_410700_2

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 27 ![![37, 0, 0], ![12, 1, 0]]
  ![-14, -3, 1] ![![27, 0, 0], ![-72, -2, 3]] where
    su := ![![999, 0, 0], ![324, 27, 0]]
    hsu := by decide
    w := ![![-378, -81, 27], ![-1404, 0, 27]]
    hw := by decide
    g := ![![![8, 1, 0], ![1, 0, 0]], ![![53, 2, -2], ![19, 0, 0]]]
    h := ![![![-1958, -211, -11], ![6036, 136, 0]], ![![-7132, -759, -38], ![21986, 469, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {27} * I37N0 =  Ideal.span {B.equivFun.symm ![-14, -3, 1]} * (J0 ^ 6*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_0 E37RS0 


noncomputable def E41RS1 : RelationCertificate Table 9 ![![41, 0, 0], ![2, 1, 0]]
  ![2, 1, 0] ![![9, 0, 0], ![-81, -5, 3]] where
    su := ![![369, 0, 0], ![18, 9, 0]]
    hsu := by decide
    w := ![![18, 9, 0], ![441, 27, -9]]
    hw := by decide
    g := ![![![23, 2, -1], ![4, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-2, 41, 42], ![42, -574, 0]], ![![-1, 1050, 1051], ![45, -14364, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {9} * I41N1 =  Ideal.span {B.equivFun.symm ![2, 1, 0]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E41RS1 


noncomputable def E43RS0 : RelationCertificate Table 1458 ![![43, 0, 0], ![10, 1, 0]]
  ![-45, -5, -6] ![![1458, 0, 0], ![15609, 771, -567]] where
    su := ![![62694, 0, 0], ![14580, 1458, 0]]
    hsu := by decide
    w := ![![-65610, -7290, -8748], ![-1290330, 37908, 59778]]
    hw := by decide
    g := ![![![-154795559278235738, -201699942449887981, -280817079984958117], ![-1654657925961131072, -228603433378006323, -188039]], ![![-35998967450340858, -46906963590198561, -65306297990803253], ![-384804170713014896, -53163589418081415, -43730]]]
    h := ![![![-145, -25, -3], ![619, 41, 0]], ![![-2585, -274, -4], ![11027, 71, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {1458} * I43N0 =  Ideal.span {B.equivFun.symm ![-45, -5, -6]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E43RS0 


noncomputable def E43RS1 : RelationCertificate Table 27 ![![43, 0, 0], ![-6, 1, 0]]
  ![-9, -4, -1] ![![27, 0, 0], ![-72, -2, 3]] where
    su := ![![1161, 0, 0], ![-162, 27, 0]]
    hsu := by decide
    w := ![![-243, -108, -27], ![-1161, -297, -54]]
    hw := by decide
    g := ![![![8, -1, 0], ![2, 0, 0]], ![![22, 1, -1], ![8, 0, 0]]]
    h := ![![![-1491, 255, -4], ![-10684, 57, 0]], ![![-7165, 1212, -11], ![-51342, 157, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {27} * I43N1 =  Ideal.span {B.equivFun.symm ![-9, -4, -1]} * (J0 ^ 6*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_0 E43RS1 


noncomputable def E43RS2 : RelationCertificate Table 54 ![![43, 0, 0], ![-5, 1, 0]]
  ![-81, -5, 3] ![![54, 0, 0], ![-514, -28, 19]] where
    su := ![![2322, 0, 0], ![-270, 54, 0]]
    hsu := by decide
    w := ![![-4374, -270, 162], ![1836, 1458, -324]]
    hw := by decide
    g := ![![![-955919, -710275, -1264772], ![9024481, 1228042, -45]], ![![64000, 47370, 84315], ![-601652, -81876, 3]]]
    h := ![![![-2, -1404, 1053], ![-1, -15092, 0]], ![![3, 564, -423], ![19, 6061, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {54} * I43N2 =  Ideal.span {B.equivFun.symm ![-81, -5, 3]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E43RS2 


noncomputable def E47RS1 : RelationCertificate Table 27 ![![47, 0, 0], ![-16, 1, 0]]
  ![-16, 1, 0] ![![27, 0, 0], ![-72, -2, 3]] where
    su := ![![1269, 0, 0], ![-432, 27, 0]]
    hsu := by decide
    w := ![![-432, 27, 0], ![1755, 81, -54]]
    hw := by decide
    g := ![![![17, 0, -1], ![8, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-80, 20, -3], ![-234, 47, 0]], ![![351, -17, -1], ![1027, 15, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {27} * I47N1 =  Ideal.span {B.equivFun.symm ![-16, 1, 0]} * (J0 ^ 6*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_0 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 1458 ![![53, 0, 0], ![-3, 1, 0]]
  ![657, 127, -42] ![![1458, 0, 0], ![-451, -1, 1]] where
    su := ![![77274, 0, 0], ![-4374, 1458, 0]]
    hsu := by decide
    w := ![![957906, 185166, -61236], ![-259524, -53946, 17496]]
    hw := by decide
    g := ![![![12740812046350, -28535259625829, -205568573037], ![-3921657435509, -101217727692004, 30600372]], ![![-579127819920, 1297057255507, 9344026045], ![178257157014, 4600805803426, -1390926]]]
    h := ![![![142569, -47515, -3], ![2518500, 39, 0]], ![![-38606, 12867, 0], ![-681980, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {1458} * I53N1 =  Ideal.span {B.equivFun.symm ![657, 127, -42]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 1458 ![![59, 0, 0], ![-9, 1, 0]]
  ![36, 58, 21] ![![1458, 0, 0], ![-451, -1, 1]] where
    su := ![![86022, 0, 0], ![-13122, 1458, 0]]
    hsu := by decide
    w := ![![52488, 84564, 30618], ![-10206, -23328, -8748]]
    hw := by decide
    g := ![![![-2528461371647, 5662932701969, 40799548080], ![778267453894, 20087050591675, 6967755]], ![![280940152831, -629214744511, -4533283120], ![-86474159928, -2231894509650, -774195]]]
    h := ![![![496476, -56106, 354], ![3254672, -6955, 0]], ![![-96242, 10885, -72], ![-630919, 1414, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {1458} * I59N1 =  Ideal.span {B.equivFun.symm ![36, 58, 21]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E59RS1 


noncomputable def E67RS0 : RelationCertificate Table 81 ![![67, 0, 0], ![0, 1, 0]]
  ![-134, -11, 5] ![![81, 0, 0], ![-72, -2, 3]] where
    su := ![![5427, 0, 0], ![0, 81, 0]]
    hsu := by decide
    w := ![![-10854, -891, 405], ![0, 324, -81]]
    hw := by decide
    g := ![![![64, 1, -3], ![74, 0, 0]], ![![35, 0, -2], ![57, 2, 0]]]
    h := ![![![-2, -404, -1210], ![32, 27025, 0]], ![![0, 80, 242], ![49, -5405, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {81} * I67N0 =  Ideal.span {B.equivFun.symm ![-134, -11, 5]} * (J0 ^ 7*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_0 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 1458 ![![67, 0, 0], ![7, 1, 0]]
  ![477, 17, -12] ![![1458, 0, 0], ![105, -3, 3]] where
    su := ![![97686, 0, 0], ![10206, 1458, 0]]
    hsu := by decide
    w := ![![695466, 24786, -17496], ![69984, 1458, -1458]]
    hw := by decide
    g := ![![![-94998836, -35567079, 1482491], ![-6765179, 230486040, -292991]], ![![-9925251, -3715953, 154886], ![-706454, 24080568, -30611]]]
    h := ![![![4044420, 587526, 3657], ![-38710809, -81677, 0]], ![![406950, 59117, 368], ![-3895086, -8219, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {1458} * I67N1 =  Ideal.span {B.equivFun.symm ![477, 17, -12]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 162 ![![67, 0, 0], ![-8, 1, 0]]
  ![-17, -3, 1] ![![162, 0, 0], ![81, 27, 0]] where
    su := ![![10854, 0, 0], ![-1296, 162, 0]]
    hsu := by decide
    w := ![![-2754, -486, 162], ![4050, 324, -162]]
    hw := by decide
    g := ![![![46244, -693682, -531822], ![-92488, 1063643, 0]], ![![-3779, 56626, 43414], ![7555, -86828, 0]]]
    h := ![![![-23651, 2989, -14], ![-198075, 313, 0]], ![![34811, -4391, 17], ![291539, -380, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {162} * I67N2 =  Ideal.span {B.equivFun.symm ![-17, -3, 1]} * (J0 ^ 8*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_1 E67RS2 


noncomputable def E71RS1 : RelationCertificate Table 1458 ![![71, 0, 0], ![32, 1, 0]]
  ![-126, -2, 3] ![![1458, 0, 0], ![10665, 675, -405]] where
    su := ![![103518, 0, 0], ![46656, 1458, 0]]
    hsu := by decide
    w := ![![-183708, -2916, 4374], ![-692550, -72900, 29160]]
    hw := by decide
    g := ![![![-11626875349020302867, -1599669336071887343, -7725225776757682051], ![-83643131659508362071, -11166463772484922730, 51551798]], ![![-5323147750145037945, -732378732176274932, -3536850355618128201], ![-38294445819952311801, -5112356907876177440, 23602028]]]
    h := ![![![-850, -60, -3], ![1882, 72, 0]], ![![-3021, -120, -2], ![6688, 54, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {1458} * I71N1 =  Ideal.span {B.equivFun.symm ![-126, -2, 3]} * (J0 ^ 6*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_2 E71RS1 
