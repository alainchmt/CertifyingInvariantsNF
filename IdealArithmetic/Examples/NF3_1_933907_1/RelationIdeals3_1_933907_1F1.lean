import IdealArithmetic.Examples.NF3_1_933907_1.PrimesBelow3_1_933907_1F1
import IdealArithmetic.Examples.NF3_1_933907_1.ClassGroupData3_1_933907_1

set_option linter.all false

noncomputable section


noncomputable def E41RS0 : RelationCertificate Table 243 ![![41, 0, 0], ![-20, 1, 0]]
  ![-2434057133, 489381746, -56210648] ![![243, 0, 0], ![-89, 37, 1]] where
    su := ![![9963, 0, 0], ![-4860, 243, 0]]
    hsu := by decide
    w := ![![-591475883319, 118919764278, -13659187464], ![1394610491961, -280394781327, 32206293927]]
    hw := by decide
    g := ![![![-227238, 983, 2753], ![83533, 0, 0]], ![![60703, -426, -751], ![-22167, 0, 0]]]
    h := ![![![-357891393, -32248784359, 3396065504], ![-611974499, -69647448156, 0]], ![![843853727, 76037746063, -8007407769], ![1442943249, 164218127359, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {243} * I41N0 =  Ideal.span {B.equivFun.symm ![-2434057133, 489381746, -56210648]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 243 ![![41, 0, 0], ![-15, 1, 0]]
  ![-237297, 47710, -5480] ![![243, 0, 0], ![-89, 37, 1]] where
    su := ![![9963, 0, 0], ![-3645, 243, 0]]
    hsu := by decide
    w := ![![-57663171, 11593530, -1331640], ![135961173, -27335799, 3139803]]
    hw := by decide
    g := ![![![-1764, -27, 19], ![743, 0, 0]], ![![351, -21, -4], ![32, 0, 0]]]
    h := ![![![-1074852, 78947, -1064], ![-2922109, 19072, 0]], ![![2534386, -186136, 2507], ![6890021, -44933, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {243} * I41N1 =  Ideal.span {B.equivFun.symm ![-237297, 47710, -5480]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 9 ![![41, 0, 0], ![-7, 1, 0]]
  ![-90, 4, 1] ![![9, 0, 0], ![-80, 1, 1]] where
    su := ![![369, 0, 0], ![-63, 9, 0]]
    hsu := by decide
    w := ![![-810, 36, 9], ![3807, -198, -45]]
    hw := by decide
    g := ![![![21, -2, 0], ![1, 0, 0]], ![![67, 0, -1], ![8, 0, 0]]]
    h := ![![![-120, 20, -1], ![-690, 21, 0]], ![![571, -78, -1], ![3284, 18, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {9} * I41N2 =  Ideal.span {B.equivFun.symm ![-90, 4, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E41RS2 


noncomputable def E47RS1 : RelationCertificate Table 81 ![![47, 0, 0], ![12, 1, 0]]
  ![75, -16, 2] ![![81, 0, 0], ![-89, 37, 1]] where
    su := ![![3807, 0, 0], ![972, 81, 0]]
    hsu := by decide
    w := ![![6075, -1296, 162], ![-49653, 9639, -1053]]
    hw := by decide
    g := ![![![88, -7, -1], ![7, 0, 0]], ![![89, -24, -1], ![49, 0, 0]]]
    h := ![![![-3315, -277, 0], ![12990, 1, 0]], ![![26821, 2234, -1], ![-105100, 17, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {81} * I47N1 =  Ideal.span {B.equivFun.symm ![75, -16, 2]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E47RS1 


noncomputable def E71RS0 : RelationCertificate Table 9 ![![71, 0, 0], ![17, 1, 0]]
  ![-1074, 58, 13] ![![9, 0, 0], ![-80, 1, 1]] where
    su := ![![639, 0, 0], ![153, 9, 0]]
    hsu := by decide
    w := ![![-9666, 522, 117], ![37287, -2250, -477]]
    hw := by decide
    g := ![![![75, -149, 27], ![-80, 0, 0]], ![![67, 0, -1], ![8, 0, 0]]]
    h := ![![![135, -50149, -5573], ![-627, 197848, 0]], ![![-574, 193475, 21501], ![2641, -763312, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {9} * I71N0 =  Ideal.span {B.equivFun.symm ![-1074, 58, 13]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 9 ![![71, 0, 0], ![-12, 1, 0]]
  ![873879, -36830, -9452] ![![9, 0, 0], ![-80, 1, 1]] where
    su := ![![639, 0, 0], ![-108, 9, 0]]
    hsu := by decide
    w := ![![7864911, -331470, -85068], ![-38577096, 1931859, 450495]]
    hw := by decide
    g := ![![![-8770895, 156032029, -29323573], ![92042777, 0, 0]], ![![3633460, -64637744, 12147567], ![-38129587, 0, 0]]]
    h := ![![![1427601, -120171, 178], ![8373816, -11045, 0]], ![![-7002608, 589969, -827], ![-41074902, 54386, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {9} * I71N1 =  Ideal.span {B.equivFun.symm ![873879, -36830, -9452]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS1 


noncomputable def E71RS2 : RelationCertificate Table 9 ![![71, 0, 0], ![-6, 1, 0]]
  ![-72576, -16532, -1343] ![![9, 0, 0], ![-80, 1, 1]] where
    su := ![![639, 0, 0], ![-54, 9, 0]]
    hsu := by decide
    w := ![![-653184, -148788, -12087], ![18777519, -351612, -155331]]
    hw := by decide
    g := ![![![-11018709, 196019016, -36838448], ![115630961, 0, 0]], ![![3633460, -64637744, 12147567], ![-38129587, 0, 0]]]
    h := ![![![-518256, 86038, -45], ![-6120600, 926, 0]], ![![14952289, -2489436, 451], ![176587688, -24640, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {9} * I71N2 =  Ideal.span {B.equivFun.symm ![-72576, -16532, -1343]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS2 


noncomputable def E73RS0 : RelationCertificate Table 9 ![![73, 0, 0], ![29, 1, 0]]
  ![1193, 492, 46] ![![9, 0, 0], ![-80, 1, 1]] where
    su := ![![657, 0, 0], ![261, 9, 0]]
    hsu := by decide
    w := ![![10737, 4428, 414], ![-483750, 7929, 3879]]
    hw := by decide
    g := ![![![8173, -144391, 27135], ![-85169, 0, 0]], ![![1317, -22920, 4307], ![-13517, 0, 0]]]
    h := ![![![109657, 5308, 102], ![-275992, -3700, 0]], ![![-4885192, -237761, -4617], ![12295354, 168736, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N0 : Ideal.span {9} * I73N0 =  Ideal.span {B.equivFun.symm ![1193, 492, 46]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E73RS0 


noncomputable def E73RS1 : RelationCertificate Table 243 ![![73, 0, 0], ![-25, 1, 0]]
  ![-272954, 13112, 3127] ![![243, 0, 0], ![-89, 37, 1]] where
    su := ![![17739, 0, 0], ![-6075, 243, 0]]
    hsu := by decide
    w := ![![-66327822, 3186216, 759861], ![-71651709, 3110886, 784890]]
    hw := by decide
    g := ![![![1921989, -327197, 53857], ![-753322, 0, 0]], ![![-1116615, 190080, -31291], ![437798, 0, 0]]]
    h := ![![![-2123292898, 91384504, -537687], ![-6200004344, 19627139, 0]], ![![-2293654981, 98716920, -580848], ![-6697460750, 21202567, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {243} * I73N1 =  Ideal.span {B.equivFun.symm ![-272954, 13112, 3127]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E73RS1 


noncomputable def E73RS2 : RelationCertificate Table 243 ![![73, 0, 0], ![-5, 1, 0]]
  ![77975795, -15677500, 1800726] ![![243, 0, 0], ![-89, 37, 1]] where
    su := ![![17739, 0, 0], ![-1215, 243, 0]]
    hsu := by decide
    w := ![![18948118185, -3809632500, 437576418], ![-44676791001, 8982536067, -1031738877]]
    hw := by decide
    g := ![![![-27737, -704, 246], ![10160, 0, 0]], ![![-695, -67, 2], ![336, 0, 0]]]
    h := ![![![98715569125, -19799699478, 28316930], ![1441231714066, -1032667582, 0]], ![![-232756351159, 46684690629, -66767031], ![-3398205955900, 2434873712, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N2 : Ideal.span {243} * I73N2 =  Ideal.span {B.equivFun.symm ![77975795, -15677500, 1800726]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E73RS2 


noncomputable def E79RS0 : RelationCertificate Table 9 ![![79, 0, 0], ![5, 1, 0]]
  ![-1519915, 305588, -35100] ![![9, 0, 0], ![-80, 1, 1]] where
    su := ![![711, 0, 0], ![45, 9, 0]]
    hsu := by decide
    w := ![![-13679235, 2750292, -315900], ![-95587452, 19218429, -2207439]]
    hw := by decide
    g := ![![![499, -1195, 53], ![-4265, 0, 0]], ![![137, -185, 10], ![-710, 0, 0]]]
    h := ![![![524715, 110872, -1040], ![-8594480, 23530, 0]], ![![3666628, 774763, -7265], ![-60056888, 164332, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {9} * I79N0 =  Ideal.span {B.equivFun.symm ![-1519915, 305588, -35100]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E79RS0 


noncomputable def E79RS1 : RelationCertificate Table 243 ![![79, 0, 0], ![20, 1, 0]]
  ![-12863, 633, 149] ![![243, 0, 0], ![-89, 37, 1]] where
    su := ![![19197, 0, 0], ![4860, 243, 0]]
    hsu := by decide
    w := ![![-3125709, 153819, 36207], ![-3433104, 154062, 38151]]
    hw := by decide
    g := ![![![-3992, 660, -115], ![1814, 0, 0]], ![![-110, 13, -4], ![116, 0, 0]]]
    h := ![![![1586223, 79276, -3], ![-6266224, 193, 0]], ![![1740328, 86981, -3], ![-6875002, 197, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {243} * I79N1 =  Ideal.span {B.equivFun.symm ![-12863, 633, 149]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E79RS1 


noncomputable def E79RS2 : RelationCertificate Table 243 ![![79, 0, 0], ![-26, 1, 0]]
  ![-217213, 3535, 1739] ![![243, 0, 0], ![-89, 37, 1]] where
    su := ![![19197, 0, 0], ![-6318, 243, 0]]
    hsu := by decide
    w := ![![-52782759, 859005, 422577], ![-31192452, -934578, 93069]]
    hw := by decide
    g := ![![![6662486, -1134162, 186701], ![-2612008, 0, 0]], ![![-3661175, 623240, -102597], ![1435425, 0, 0]]]
    h := ![![![-17273, -3938734, 315169], ![-44129, -12448306, 0]], ![![-10064, -2292026, 183389], ![-25642, -7243674, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {243} * I79N2 =  Ideal.span {B.equivFun.symm ![-217213, 3535, 1739]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E79RS2 
