import IdealArithmetic.Examples.NF3_1_894348_3.PrimesBelow3_1_894348_3F1
import IdealArithmetic.Examples.NF3_1_894348_3.ClassGroupData3_1_894348_3

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 55 ![![41, 0, 0], ![14, 1, 0]]
  ![-54127, -4993, -3224] ![![55, 0, 0], ![-4, 1, 0]] where
    su := ![![2255, 0, 0], ![770, 55, 0]]
    hsu := by decide
    w := ![![-2976985, -274615, -177320], ![-370260, -34155, -22055]]
    hw := by decide
    g := ![![![6063, 4607075, -8065031], ![83364, 63368088, 0]], ![![2104, 1604813, -2809345], ![29028, 22073424, 0]]]
    h := ![![![-54093, -4286, -276], ![154549, 1156, 0]], ![![-6736, -545, -40], ![19246, 177, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {55} * I41N1 =  Ideal.span {B.equivFun.symm ![-54127, -4993, -3224]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E41RS1 


noncomputable def E43RS0 : RelationCertificate Table 3025 ![![43, 0, 0], ![21, 1, 0]]
  ![-6300051, -581149, -375257] ![![3025, 0, 0], ![601, 1, 0]] where
    su := ![![130075, 0, 0], ![63525, 3025, 0]]
    hsu := by decide
    w := ![![-19057654275, -1757975725, -1135152425], ![-3854627425, -355570600, -229597500]]
    hw := by decide
    g := ![![![-342, -2224, -26], ![1699, 11194, 0]], ![![-240, -20438, -238], ![1195, 102869, 0]]]
    h := ![![![-100072949034, -8358497127, -1197712748], ![204910976591, 7357324701, 0]], ![![-20240892628, -1690601165, -242251036], ![41445576607, 1488102664, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {3025} * I43N0 =  Ideal.span {B.equivFun.symm ![-6300051, -581149, -375257]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E43RS0 


noncomputable def E43RS1 : RelationCertificate Table 3025 ![![43, 0, 0], ![-18, 1, 0]]
  ![5674939, 523486, 338023] ![![3025, 0, 0], ![601, 1, 0]] where
    su := ![![130075, 0, 0], ![-54450, 3025, 0]]
    hsu := by decide
    w := ![![17166690475, 1583545150, 1022519575], ![3472158525, 320290025, 206816225]]
    hw := by decide
    g := ![![![-778, 9981977, 116263], ![3903, -50242072, 0]], ![![-92, -3851191, -44856], ![476, 19384114, 0]]]
    h := ![![![43189597, -2612170, 98182], ![102859874, -554829, 0]], ![![8735595, -528325, 19852], ![20804598, -112181, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {3025} * I43N1 =  Ideal.span {B.equivFun.symm ![5674939, 523486, 338023]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E43RS1 


noncomputable def E43RS2 : RelationCertificate Table 3025 ![![43, 0, 0], ![-3, 1, 0]]
  ![48931, 4519, 2917] ![![3025, 0, 0], ![601, 1, 0]] where
    su := ![![130075, 0, 0], ![-9075, 3025, 0]]
    hsu := by decide
    w := ![![148016275, 13669975, 8823925], ![29938425, 2764850, 1784750]]
    hw := by decide
    g := ![![![-96235536, 1523082263605, 17739728729], ![484380191, -7666097057879, 0]], ![![-7354927, 116402478597, 1355769444], ![37019392, -585886081157, 0]]]
    h := ![![![463932262, -155342081, 1629850], ![6649679445, -10011519, 0]], ![![93836988, -31420175, 329660], ![1344993529, -2024970, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {3025} * I43N2 =  Ideal.span {B.equivFun.symm ![48931, 4519, 2917]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E43RS2 


noncomputable def E47RS1 : RelationCertificate Table 5 ![![47, 0, 0], ![8, 1, 0]]
  ![229, -49, 18] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![235, 0, 0], ![40, 5, 0]]
    hsu := by decide
    w := ![![1145, -245, 90], ![3505, 180, -325]]
    hw := by decide
    g := ![![![8175, 408, 268], ![1718, 171, 0]], ![![3276, 170, 160], ![694, 31, 0]]]
    h := ![![![219, 23, -2], ![-1258, 16, 0]], ![![691, 80, -6], ![-3972, 31, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {5} * I47N1 =  Ideal.span {B.equivFun.symm ![229, -49, 18]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 25 ![![53, 0, 0], ![-18, 1, 0]]
  ![-563, 38, 9] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![1325, 0, 0], ![-450, 25, 0]]
    hsu := by decide
    w := ![![-14075, 950, 225], ![1075, -525, 275]]
    hw := by decide
    g := ![![![406, 137, 731], ![39, -2524, 0]], ![![-55, -38, -234], ![-1, 824, 0]]]
    h := ![![![-877, 57, -3], ![-2551, 24, 0]], ![![101, 10, -6], ![295, 47, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {25} * I53N1 =  Ideal.span {B.equivFun.symm ![-563, 38, 9]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 605 ![![59, 0, 0], ![-20, 1, 0]]
  ![884943, 81632, 52711] ![![605, 0, 0], ![-4, 1, 0]] where
    su := ![![35695, 0, 0], ![-12100, 605, 0]]
    hsu := by decide
    w := ![![535390515, 49387360, 31890155], ![6053630, 558415, 360580]]
    hw := by decide
    g := ![![![-8759, -800600070, 1401053950], ![-1322948, -121091091333, 0]], ![![3022, 275913012, -482849091], ![456127, 41731957131, 0]]]
    h := ![![![1430297, -74063, 2532], ![4175129, -13811, 0]], ![![16194, -831, 26], ![47272, -134, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {605} * I59N1 =  Ideal.span {B.equivFun.symm ![884943, 81632, 52711]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E59RS1 


noncomputable def E67RS0 : RelationCertificate Table 11 ![![67, 0, 0], ![30, 1, 0]]
  ![-15, -1, 1] ![![11, 0, 0], ![-4, 1, 0]] where
    su := ![![737, 0, 0], ![330, 11, 0]]
    hsu := by decide
    w := ![![-165, -11, 11], ![242, -11, -11]]
    hw := by decide
    g := ![![![40837, 1398760, -2465698], ![112311, 3874668, 0]], ![![18542, 635001, -1119365], ![50996, 1759002, 0]]]
    h := ![![![-2805, -145, -12], ![6264, 115, 0]], ![![4006, 155, 5], ![-8946, -48, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {11} * I67N0 =  Ideal.span {B.equivFun.symm ![-15, -1, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 11 ![![67, 0, 0], ![-29, 1, 0]]
  ![435, 40, 26] ![![11, 0, 0], ![-4, 1, 0]] where
    su := ![![737, 0, 0], ![-319, 11, 0]]
    hsu := by decide
    w := ![![4785, 440, 286], ![2992, 275, 176]]
    hw := by decide
    g := ![![![-31, -1060, 1870], ![-84, -2940, 0]], ![![13, 445, -786], ![42, 1236, 0]]]
    h := ![![![176494, -6792, 171], ![407747, -1633, 0]], ![![110372, -4227, 102], ![254988, -974, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {11} * I67N1 =  Ideal.span {B.equivFun.symm ![435, 40, 26]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 11 ![![67, 0, 0], ![-1, 1, 0]]
  ![125, -10, -1] ![![11, 0, 0], ![-4, 1, 0]] where
    su := ![![737, 0, 0], ![-11, 11, 0]]
    hsu := by decide
    w := ![![1375, -110, -11], ![-682, 165, -66]]
    hw := by decide
    g := ![![![50811, 1743616, -3073633], ![140044, 4829984, 0]], ![![-11, -3, -1], ![16, 0, 0]]]
    h := ![![![4, -2, -2], ![143, 19, 0]], ![![0, 0, -5], ![62, 47, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {11} * I67N2 =  Ideal.span {B.equivFun.symm ![125, -10, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E67RS2 


noncomputable def E71RS1 : RelationCertificate Table 3025 ![![71, 0, 0], ![-13, 1, 0]]
  ![-15269, 569, 542] ![![3025, 0, 0], ![601, 1, 0]] where
    su := ![![214775, 0, 0], ![-39325, 3025, 0]]
    hsu := by decide
    w := ![![-46188725, 1721225, 1639550], ![-9078025, 326700, 329725]]
    hw := by decide
    g := ![![![-327212057, 5178675397431, 60317357059], ![1646949108, -26065715015280, 0]], ![![48584298, -768927451209, -8955894716], ![-244538269, 3870225930858, 0]]]
    h := ![![![-40156, 3167, -39], ![-218139, 473, 0]], ![![-7882, 626, -10], ![-42817, 117, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {3025} * I71N1 =  Ideal.span {B.equivFun.symm ![-15269, 569, 542]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E71RS1 


noncomputable def E79RS0 : RelationCertificate Table 5 ![![79, 0, 0], ![12, 1, 0]]
  ![-61, 1, 3] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![395, 0, 0], ![60, 5, 0]]
    hsu := by decide
    w := ![![-305, 5, 15], ![485, -60, 10]]
    hw := by decide
    g := ![![![119, 67, 450], ![40, -316, 0]], ![![34, 10, 68], ![14, -47, 0]]]
    h := ![![![-271, -26, -2], ![1779, 23, 0]], ![![403, 23, -6], ![-2645, 68, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {5} * I79N0 =  Ideal.span {B.equivFun.symm ![-61, 1, 3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E79RS0 


noncomputable def E79RS1 : RelationCertificate Table 5 ![![79, 0, 0], ![28, 1, 0]]
  ![23, 2, 1] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![395, 0, 0], ![140, 5, 0]]
    hsu := by decide
    w := ![![115, 10, 5], ![205, 25, 15]]
    hw := by decide
    g := ![![![-5594, 145607, 1058459], ![28003, -756042, 0]], ![![-2045, 53224, 386904], ![10239, -276360, 0]]]
    h := ![![![1793, 52, -3], ![-5058, 34, 0]], ![![3223, 135, 5], ![-9092, -56, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {5} * I79N1 =  Ideal.span {B.equivFun.symm ![23, 2, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E79RS1 


noncomputable def E79RS2 : RelationCertificate Table 5 ![![79, 0, 0], ![39, 1, 0]]
  ![-2417, -223, -144] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![395, 0, 0], ![195, 5, 0]]
    hsu := by decide
    w := ![![-12085, -1115, -720], ![-28625, -2640, -1705]]
    hw := by decide
    g := ![![![3150, -79427, -577302], ![-15251, 412357, 0]], ![![1606, -40662, -295557], ![-7809, 211111, 0]]]
    h := ![![![-106586, -5076, -422], ![215843, 4742, 0]], ![![-252478, -12026, -1000], ![511283, 11237, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {5} * I79N2 =  Ideal.span {B.equivFun.symm ![-2417, -223, -144]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E79RS2 
