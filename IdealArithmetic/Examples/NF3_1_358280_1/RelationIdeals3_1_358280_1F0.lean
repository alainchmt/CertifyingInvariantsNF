import IdealArithmetic.Examples.NF3_1_358280_1.PrimesBelow3_1_358280_1F0
import IdealArithmetic.Examples.NF3_1_358280_1.ClassGroupData3_1_358280_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![1, 1, 0]]
  ![-52895868, 19096763, -2487387] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![4, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![-105791736, 38193526, -4974774], ![353208954, -127517478, 16609376]]
    hw := by decide
    g := ![![![6807, 946, 28], ![474, -7, 0]], ![![1664, 3490, 623], ![1745, -14, 0]]]
    h := ![![![-35263912, -5059701, -7035798], ![17631956, 11584209, 0]], ![![117736318, 16892920, 23490554], ![-58868159, -38676420, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![-52895868, 19096763, -2487387]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![3, 1, 0]]
  ![-234151361812621, 84534638180959, -11010785443628] ![![2, 0, 0], ![-20, 2, 1]] where
    su := ![![14, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![-468302723625242, 169069276361918, -22021570887256], ![-2630296786458230, 949604501253004, -123687658036908]]
    hw := by decide
    g := ![![![1270948, 4575262, 1581696], ![-7343313, 0, 0]], ![![1611415, 7808826, 2050349], ![-7280096, 0, 0]]]
    h := ![![![-572159693822503, -230486498493062, -22570650110237], ![1256988831648300, 146983765328031, 0]], ![![-3213625990368103, -1294564105062634, -126771648889100], ![7060077846449202, 825557713205246, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![-234151361812621, 84534638180959, -11010785443628]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 2 ![![7, 0, 0], ![-3, 1, 0]]
  ![-2478719, 93889, 69652] ![![2, 0, 0], ![-20, 2, 1]] where
    su := ![![14, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![-4957438, 187778, 139304], ![6570390, -7640452, -1291576]]
    hw := by decide
    g := ![![![4967911222, 117349421442, -44052285189], ![45644166761, 0, 0]], ![![-6868094247, -162234559526, 60901903015], ![-63102665510, 0, 0]]]
    h := ![![![-15634259, 5753449, -205600], ![-35653698, 1508852, 0]], ![![22600245, -8703247, 167919], ![51638840, -1821221, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![-2478719, 93889, 69652]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1 


noncomputable def E7RS2 : RelationCertificate Table 2 ![![7, 0, 0], ![-1, 1, 0]]
  ![147491429, -37264879, -8888572] ![![2, 0, 0], ![-20, 2, 1]] where
    su := ![![14, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![294982858, -74529758, -17777144], ![6128315910, 384539812, -79854644]]
    hw := by decide
    g := ![![![-77301366105732, -1825972769592898, 685459478222686], ![-710229369424075, 0, 0]], ![![84782365022265, 2002685045184450, -751796231015303], ![778963279454328, 0, 0]]]
    h := ![![![46271822, -30858827, -936141], ![176411325, -2335585, 0]], ![![961304458, -505333965, 3529584], ![3664973251, -64634410, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N2 : Ideal.span {2} * I7N2 =  Ideal.span {B.equivFun.symm ![147491429, -37264879, -8888572]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS2 


noncomputable def E17RS1 : RelationCertificate Table 2 ![![17, 0, 0], ![1, 1, 0]]
  ![854751, -308587, 40194] ![![2, 0, 0], ![-20, 2, 1]] where
    su := ![![34, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![1709502, -617174, 80388], ![9601690, -3466456, 451512]]
    hw := by decide
    g := ![![![152, 932, 196], ![-475, 0, 0]], ![![55, 300, 51], ![-58, 0, 0]]]
    h := ![![![99866, 31661, 2591], ![-842971, -3853, 0]], ![![560922, 177839, 14554], ![-4734829, -21662, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {2} * I17N1 =  Ideal.span {B.equivFun.symm ![854751, -308587, 40194]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![2, 1, 0]]
  ![179, -60, -13] ![![2, 0, 0], ![-20, 2, 1]] where
    su := ![![38, 0, 0], ![4, 2, 0]]
    hsu := by decide
    w := ![![358, -120, -26], ![10478, 434, -170]]
    hw := by decide
    g := ![![![204, 4523, -1699], ![1761, 0, 0]], ![![-45, -1114, 418], ![-433, 0, 0]]]
    h := ![![![491, 239, 0], ![-4575, -13, 0]], ![![14519, 7220, 39], ![-135311, -826, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![179, -60, -13]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![-5, 1, 0]]
  ![-37514, 1627, 1085] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![46, 0, 0], ![-10, 2, 0]]
    hsu := by decide
    w := ![![-75028, 3254, 2170], ![-154070, -4964, 2712]]
    hw := by decide
    g := ![![![52092112, -15045270, 2448044], ![-7522633, 3094, 0]], ![![-26447934, 7638705, -1243375], ![3819353, -637, 0]]]
    h := ![![![-352388, 72938, -496], ![-1613482, 12493, 0]], ![![-722790, 149370, -1059], ![-3309427, 25713, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![-37514, 1627, 1085]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 2 ![![29, 0, 0], ![14, 1, 0]]
  ![77460002872, -27965044771, 3642496313] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![58, 0, 0], ![28, 2, 0]]
    hsu := by decide
    w := ![![154920005744, -55930089542, 7284992626], ![-517234476446, 186734892262, -24322548458]]
    hw := by decide
    g := ![![![822865, -191067, -51117], ![-95533, -6210, 0]], ![![662746, -114413, -34729], ![-57206, -3105, 0]]]
    h := ![![![550209641716, 66569983849, 2155917266], ![-1134187114778, -58879104401, 0]], ![![-1836995774755, -222258517111, -7198003468], ![3786732873548, 196580826343, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {2} * I29N1 =  Ideal.span {B.equivFun.symm ![77460002872, -27965044771, 3642496313]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 
