import IdealArithmetic.Examples.NF3_1_280904_4.PrimesBelow3_1_280904_4F1
import IdealArithmetic.Examples.NF3_1_280904_4.ClassGroupData3_1_280904_4

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 7 ![![37, 0, 0], ![8, 1, 0]]
  ![1891745, -261556, 89694] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![259, 0, 0], ![56, 7, 0]]
    hsu := by decide
    w := ![![13242215, -1830892, 627858], ![-5357772, 740775, -254030]]
    hw := by decide
    g := ![![![-327, -169, -54], ![-117, 34, 0]], ![![32, -46, -26], ![7, 20, 0]]]
    h := ![![![-166511397, -1461044516, -365767006], ![-75490128, 6766734458, 0]], ![![67370149, 591135500, 147988552], ![30543181, -2737806357, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {7} * I37N0 =  Ideal.span {B.equivFun.symm ![1891745, -261556, 89694]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS0 


noncomputable def E37RS1 : RelationCertificate Table 7 ![![37, 0, 0], ![14, 1, 0]]
  ![196316, -27143, 9308] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![259, 0, 0], ![98, 7, 0]]
    hsu := by decide
    w := ![![1374212, -190001, 65156], ![-556003, 76874, -26362]]
    hw := by decide
    g := ![![![180, 132, 94], ![73, -288, 0]], ![![41, 57, 44], ![27, -126, 0]]]
    h := ![![![8194609, 152748500, 21849482], ![7229039, -404210763, 0]], ![![-3315539, -61801692, -8840250], ![-2924802, 163542742, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {7} * I37N1 =  Ideal.span {B.equivFun.symm ![196316, -27143, 9308]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 49 ![![41, 0, 0], ![18, 1, 0]]
  ![-1103901108, 152627315, -52339668] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![2009, 0, 0], ![882, 49, 0]]
    hsu := by decide
    w := ![![-54091154292, 7478738435, -2564643732], ![-12328163281, 1704513608, -584519726]]
    hw := by decide
    g := ![![![3237, 945, -56], ![1084, -1551, 0]], ![![1687, 560, 0], ![586, -804, 0]]]
    h := ![![![-585091076817, -15540931064630, -1728495159042], ![-635916352341, 35434124590527, 0]], ![![-133350793187, -3542004939833, -393949266382], ![-144934615047, 8075953996344, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {49} * I41N1 =  Ideal.span {B.equivFun.symm ![-1103901108, 152627315, -52339668]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E41RS1 


noncomputable def E47RS1 : RelationCertificate Table 7 ![![47, 0, 0], ![21, 1, 0]]
  ![57533860, -7954733, 2727874] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![329, 0, 0], ![147, 7, 0]]
    hsu := by decide
    w := ![![402737020, -55683131, 19095118], ![-162946539, 22529276, -7725844]]
    hw := by decide
    g := ![![![87830, 191955, 199372], ![52524, -699200, 0]], ![![41739, 89761, 93114], ![24750, -326600, 0]]]
    h := ![![![30880278, 938767439, 89549014], ![33771366, -2103037892, 0]], ![![-12494098, -379823303, -36231340], ![-13663815, 850884644, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {7} * I47N1 =  Ideal.span {B.equivFun.symm ![57533860, -7954733, 2727874]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS1 


noncomputable def E53RS0 : RelationCertificate Table 49 ![![53, 0, 0], ![26, 1, 0]]
  ![-676, -89, 22] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![2597, 0, 0], ![1274, 49, 0]]
    hsu := by decide
    w := ![![-33124, -4361, 1078], ![-13083, -2254, 196]]
    hw := by decide
    g := ![![![-494, -4585, -592], ![-238, 14176, 0]], ![![-231, -2292, -294], ![-80, 7072, 0]]]
    h := ![![![6729, 286608, 22060], ![8741, -584579, 0]], ![![2654, 113111, 8706], ![3453, -230707, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {49} * I53N0 =  Ideal.span {B.equivFun.symm ![-676, -89, 22]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 7 ![![53, 0, 0], ![-26, 1, 0]]
  ![331568313, -45843220, 15720770] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![371, 0, 0], ![-182, 7, 0]]
    hsu := by decide
    w := ![![2320978191, -320902540, 110045390], ![-939062824, 129836483, -44524130]]
    hw := by decide
    g := ![![![-1115, 2129, 1126], ![-11, -606, 0]], ![![-1062, -1124, -458], ![-459, 288, 0]]]
    h := ![![![-2893830743, 123050251724, -9470603966], ![3741317992, 250978865484, 0]], ![![1170837760, -49785869306, 3831786158], ![-1513729245, -101545513482, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {7} * I53N1 =  Ideal.span {B.equivFun.symm ![331568313, -45843220, 15720770]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 7 ![![59, 0, 0], ![12, 1, 0]]
  ![404, 449, 158] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![413, 0, 0], ![84, 7, 0]]
    hsu := by decide
    w := ![![2828, 3143, 1106], ![-14385, 196, 1372]]
    hw := by decide
    g := ![![![-234466, 43496, -11944], ![-60773, 14, 0]], ![![-28487, 5281, -1454], ![-7381, 12, 0]]]
    h := ![![![417, 5436, 908], ![209, -26707, 0]], ![![-2770, -35604, -5934], ![-1148, 175151, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {7} * I59N1 =  Ideal.span {B.equivFun.symm ![404, 449, 158]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 


noncomputable def E71RS1 : RelationCertificate Table 49 ![![71, 0, 0], ![31, 1, 0]]
  ![-12876, -93, 1112] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![3479, 0, 0], ![1519, 49, 0]]
    hsu := by decide
    w := ![![-630924, -4557, 54488], ![-316197, -22148, 18718]]
    hw := by decide
    g := ![![![56668, -2508016, -300578], ![-32677, 7597710, 0]], ![![12401, -1092300, -131790], ![-18229, 3314932, 0]]]
    h := ![![![20161, 927184, 59854], ![21934, -2124261, 0]], ![![10105, 464136, 29960], ![10951, -1063389, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {49} * I71N1 =  Ideal.span {B.equivFun.symm ![-12876, -93, 1112]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS1 


noncomputable def E71RS2 : RelationCertificate Table 7 ![![71, 0, 0], ![32, 1, 0]]
  ![-1913, -160, 102] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![497, 0, 0], ![224, 7, 0]]
    hsu := by decide
    w := ![![-13391, -1120, 714], ![-14084, -2947, -14]]
    hw := by decide
    g := ![![![121303, -22646, 6046], ![31426, 470, 0]], ![![46411, -8675, 2304], ![12026, 213, 0]]]
    h := ![![![-2183, -103000, -6438], ![-2360, 228600, 0]], ![![-2258, -107650, -6730], ![-2519, 238914, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {7} * I71N2 =  Ideal.span {B.equivFun.symm ![-1913, -160, 102]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E71RS2 


noncomputable def E79RS0 : RelationCertificate Table 49 ![![79, 0, 0], ![14, 1, 0]]
  ![-18017, -5352, -702] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![3871, 0, 0], ![686, 49, 0]]
    hsu := by decide
    w := ![![-882833, -262248, -34398], ![-224126, -98735, -22638]]
    hw := by decide
    g := ![![![1846354, 28339149, 3574872], ![1181271, -87055317, 0]], ![![372808, 6428331, 807606], ![252946, -19724952, 0]]]
    h := ![![![13754822, 204992417, 29293732], ![5032415, -1157102765, 0]], ![![3461953, 51594646, 7372952], ![1266641, -291231835, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {49} * I79N0 =  Ideal.span {B.equivFun.symm ![-18017, -5352, -702]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E79RS0 


noncomputable def E79RS1 : RelationCertificate Table 49 ![![79, 0, 0], ![19, 1, 0]]
  ![8866023, -1225832, 420368] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![3871, 0, 0], ![931, 49, 0]]
    hsu := by decide
    w := ![![434435127, -60065768, 20598032], ![99014104, -13689865, 4694592]]
    hw := by decide
    g := ![![![-9819369, -194444149, -24323796], ![-7174563, 595933714, 0]], ![![-2500195, -49508382, -6193200], ![-1826739, 151733600, 0]]]
    h := ![![![-9694029966, -206738470805, -21768530836], ![-4948418151, 859857178206, 0]], ![![-2209410868, -47118713883, -4961365788], ![-1127816698, 195973996530, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {49} * I79N1 =  Ideal.span {B.equivFun.symm ![8866023, -1225832, 420368]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E79RS1 


noncomputable def E79RS2 : RelationCertificate Table 49 ![![79, 0, 0], ![-34, 1, 0]]
  ![285, 36, -10] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![3871, 0, 0], ![-1666, 49, 0]]
    hsu := by decide
    w := ![![13965, 1764, -490], ![5586, 931, -98]]
    hw := by decide
    g := ![![![65, 2440, 302], ![112, -7458, 0]], ![![-38, -989, -122], ![4, 3018, 0]]]
    h := ![![![6807, -334914, 19706], ![-7086, -778392, 0]], ![![2710, -133890, 7878], ![-2859, -311182, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {49} * I79N2 =  Ideal.span {B.equivFun.symm ![285, 36, -10]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E79RS2 
