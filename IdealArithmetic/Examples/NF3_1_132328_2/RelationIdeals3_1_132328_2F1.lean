import IdealArithmetic.Examples.NF3_1_132328_2.PrimesBelow3_1_132328_2F1
import IdealArithmetic.Examples.NF3_1_132328_2.ClassGroupData3_1_132328_2

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 2 ![![37, 0, 0], ![1, 1, 0]]
  ![1, 1, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![74, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![2, 2, 0], ![0, 2, 2]]
    hw := by decide
    g := ![![![-1998, 554, 37], ![279, 0, 73]], ![![-54, 15, 1], ![8, 0, 2]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -1], ![0, 19, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {2} * I37N0 =  Ideal.span {B.equivFun.symm ![1, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS0 


noncomputable def E37RS2 : RelationCertificate Table 4 ![![37, 0, 0], ![-11, 1, 0]]
  ![-1819, 879, -210] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![148, 0, 0], ![-44, 4, 0]]
    hsu := by decide
    w := ![![-7276, 3516, -840], ![-15188, 4808, 1548]]
    hw := by decide
    g := ![![![4113411248, -41158576458, -28811141733], ![-8232938487, 57621992922, -11505]], ![![-1054791926, 10553482293, 7387467857], ![2110974615, -14774869389, 2950]]]
    h := ![![![-85075, 8215, -98], ![-285996, 1708, 0]], ![![-177249, 17104, -183], ![-595856, 3579, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N2 : Ideal.span {4} * I37N2 =  Ideal.span {B.equivFun.symm ![-1819, 879, -210]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E37RS2 


noncomputable def E41RS0 : RelationCertificate Table 4 ![![41, 0, 0], ![13, 1, 0]]
  ![-824127, -67069, -37962] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![164, 0, 0], ![52, 4, 0]]
    hsu := by decide
    w := ![![-3296508, -268276, -151848], ![-3736164, -304056, -172100]]
    hw := by decide
    g := ![![![309088590053, -3090886221937, -2163620368110], ![-618177260457, 4327240734620, 2943]], ![![137372706387, -1373727207722, -961609051104], ![-274745448732, 1923218101510, 1308]]]
    h := ![![![-4756930, -405628, -6586], ![14939231, 116032, 0]], ![![-5391362, -459717, -7463], ![16931677, 131479, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {4} * I41N0 =  Ideal.span {B.equivFun.symm ![-824127, -67069, -37962]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 2 ![![41, 0, 0], ![-7, 1, 0]]
  ![-89, 75, -52] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![82, 0, 0], ![-14, 2, 0]]
    hsu := by decide
    w := ![![-178, 150, -104], ![-2860, 974, 202]]
    hw := by decide
    g := ![![![-182289, -71563, -19628], ![-35781, 0, -6357]], ![![12008, 9965, 2281], ![4984, 0, 978]]]
    h := ![![![-107, 19, -2], ![-614, 15, 0]], ![![-1916, 285, 1], ![-11018, 30, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {2} * I41N1 =  Ideal.span {B.equivFun.symm ![-89, 75, -52]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 2 ![![43, 0, 0], ![21, 1, 0]]
  ![12187, -2961, -2412] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![86, 0, 0], ![42, 2, 0]]
    hsu := by decide
    w := ![![24374, -5922, -4824], ![-132660, 55054, -3510]]
    hw := by decide
    g := ![![![777341104, 50527285, 35791479], ![25263643, 0, -8721]], ![![425422218, 27655575, 19588491], ![13827788, 0, -4446]]]
    h := ![![![490693, 28213, 392], ![-1004172, -9634, 0]], ![![-2670540, -153429, -2493], ![5465090, 52722, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {2} * I43N1 =  Ideal.span {B.equivFun.symm ![12187, -2961, -2412]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E43RS1 


noncomputable def E59RS0 : RelationCertificate Table 2 ![![59, 0, 0], ![18, 1, 0]]
  ![1510791, 122951, 69592] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![118, 0, 0], ![36, 2, 0]]
    hsu := by decide
    w := ![![3021582, 245902, 139184], ![3827560, 311494, 176310]]
    hw := by decide
    g := ![![![447424, -123767, -8017], ![-61883, 0, -16215]], ![![149183, -41253, -2699], ![-20625, 0, -5405]]]
    h := ![![![7669191, 481794, 6976], ![-25053971, -170996, 0]], ![![9714892, 610311, 8837], ![-31736936, -216614, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {2} * I59N0 =  Ideal.span {B.equivFun.symm ![1510791, 122951, 69592]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 4 ![![59, 0, 0], ![20, 1, 0]]
  ![-82459437653, -6710703335, -3798352782] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![236, 0, 0], ![80, 4, 0]]
    hsu := by decide
    w := ![![-329837750612, -26842813340, -15193411128], ![-373828278316, -30422844800, -17219759452]]
    hw := by decide
    g := ![![![33527907325896538, -335279073261987240, -234695351283507495], ![-67055814652548537, 469390702567016750, 11775]], ![![12070046637329809, -120700466374321153, -84490326462060055], ![-24140093274915383, 168980652924126030, 4239]]]
    h := ![![![110983208293, 5047790493, -107951248], ![-331523436347, 1285385425, 0]], ![![125785061299, 5721015323, -122348729], ![-375738784311, 1456817574, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {4} * I59N1 =  Ideal.span {B.equivFun.symm ![-82459437653, -6710703335, -3798352782]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS1 


noncomputable def E73RS1 : RelationCertificate Table 2 ![![73, 0, 0], ![-21, 1, 0]]
  ![-1069, 951, -690] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![146, 0, 0], ![-42, 2, 0]]
    hsu := by decide
    w := ![![-2138, 1902, -1380], ![-37950, 12992, 2592]]
    hw := by decide
    g := ![![![-60927007, -4343783, -2877447], ![-2171891, 0, -40158]], ![![15387729, 1105664, 728346], ![552834, 0, 11058]]]
    h := ![![![-3700, 214, -12], ![-12811, 93, 0]], ![![-66000, 3357, 4], ![-228525, 502, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {2} * I73N1 =  Ideal.span {B.equivFun.symm ![-1069, 951, -690]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS1 
