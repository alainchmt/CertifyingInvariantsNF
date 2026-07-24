import IdealArithmetic.Examples.NF3_1_314847_3.PrimesBelow3_1_314847_3F2
import IdealArithmetic.Examples.NF3_1_314847_3.ClassGroupData3_1_314847_3

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 25 ![![83, 0, 0], ![-28, 1, 0]]
  ![-51011707, -8551810, -4120582] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![2075, 0, 0], ![-700, 25, 0]]
    hsu := by decide
    w := ![![-1275292675, -213795250, -103014550], ![-678535050, -113752375, -54810150]]
    hw := by decide
    g := ![![![3061, -592, -222], ![477, 1495, 0]], ![![-44904534044, -69348532607, -92995839298], ![-9958666737, 581223995459, 0]]]
    h := ![![![-1492983725, 25601977987, -3532720754], ![812114769, 73302925500, 0]], ![![-794360238, 13621845208, -1879627242], ![432095571, 39001717170, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {25} * I83N1 =  Ideal.span {B.equivFun.symm ![-51011707, -8551810, -4120582]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 10 ![![89, 0, 0], ![-4, 1, 0]]
  ![-1089, -125, 96] ![![10, 0, 0], ![4, 1, 0]] where
    su := ![![890, 0, 0], ![-40, 10, 0]]
    hsu := by decide
    w := ![![-10890, -1250, 960], ![6050, -600, -20]]
    hw := by decide
    g := ![![![52083878, 97873211, 134778218], ![30620879, -337298400, 281082]], ![![-1978493, -3716800, -5118218], ![-1163071, 12808798, -10674]]]
    h := ![![![10667, -26772, 21424], ![-717, -476660, 0]], ![![-5979, 15016, -12018], ![516, 267400, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {10} * I89N1 =  Ideal.span {B.equivFun.symm ![-1089, -125, 96]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 20 ![![97, 0, 0], ![47, 1, 0]]
  ![-25799, -4325, -2084] ![![20, 0, 0], ![-6, 1, 0]] where
    su := ![![1940, 0, 0], ![940, 20, 0]]
    hsu := by decide
    w := ![![-515980, -86500, -41680], ![-85180, -14280, -6880]]
    hw := by decide
    g := ![![![-6571907, 26283900, -15113251], ![3285783, 75566504, 164]], ![![-3205800, 12821415, -7372318], ![1602815, 36861709, 80]]]
    h := ![![![46903526, 1504519374, 130862032], ![38237059, -3173404797, 0]], ![![7743021, 248371942, 21603216], ![6312316, -523878074, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {20} * I97N1 =  Ideal.span {B.equivFun.symm ![-25799, -4325, -2084]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E97RS1 


noncomputable def E101RS0 : RelationCertificate Table 2 ![![101, 0, 0], ![1, 1, 0]]
  ![1, 1, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![202, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![2, 2, 0], ![2, 0, 4]]
    hw := by decide
    g := ![![![44724, 2901, 404], ![1451, 0, -806]], ![![44734, 2901, 403], ![1452, 0, -806]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![-3, 0, -6], ![0, 152, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {2} * I101N0 =  Ideal.span {B.equivFun.symm ![1, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 2 ![![101, 0, 0], ![15, 1, 0]]
  ![121707, -3109, -3956] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![202, 0, 0], ![30, 2, 0]]
    hsu := by decide
    w := ![![243414, -6218, -7912], ![-445334, 89212, -16392]]
    hw := by decide
    g := ![![![1252995515, 167838259, 100998351], ![83919131, 0, -54002]], ![![301208771, 40365712, 24298692], ![20182858, 0, -8060]]]
    h := ![![![-3026256, -21878002, -6252772], ![-665963, 157881504, 0]], ![![5572423, 40285776, 11513484], ![1226510, -290717520, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {2} * I101N1 =  Ideal.span {B.equivFun.symm ![121707, -3109, -3956]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E101RS1 


noncomputable def E101RS2 : RelationCertificate Table 2 ![![101, 0, 0], ![-16, 1, 0]]
  ![-315, -67, 40] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![202, 0, 0], ![-32, 2, 0]]
    hsu := by decide
    w := ![![-630, -134, 80], ![4306, 112, -228]]
    hw := by decide
    g := ![![![-4350421, -279876, -36795], ![-139937, 0, 78988]], ![![668779, 43226, 5866], ![21615, 0, -12090]]]
    h := ![![![-87403, 771656, -181616], ![21515, 4585814, 0]], ![![598797, -5286253, 1244166], ![-147131, -31415220, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {2} * I101N2 =  Ideal.span {B.equivFun.symm ![-315, -67, 40]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E101RS2 


noncomputable def E103RS1 : RelationCertificate Table 5 ![![103, 0, 0], ![16, 1, 0]]
  ![299, 50, 24] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![515, 0, 0], ![80, 5, 0]]
    hsu := by decide
    w := ![![1495, 250, 120], ![2465, 415, 200]]
    hw := by decide
    g := ![![![282102, -282083, 609288], ![-112835, -761608, 0]], ![![47654, -47649, 102920], ![-19058, -128650, 0]]]
    h := ![![![-16539, -128394, -34248], ![-3748, 881892, 0]], ![![-27259, -211695, -56468], ![-6247, 1454061, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {5} * I103N1 =  Ideal.span {B.equivFun.symm ![299, 50, 24]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 10 ![![107, 0, 0], ![8, 1, 0]]
  ![-603, 85, -8] ![![10, 0, 0], ![4, 1, 0]] where
    su := ![![1070, 0, 0], ![80, 10, 0]]
    hsu := by decide
    w := ![![-6030, 850, -80], ![-3130, -420, 300]]
    hw := by decide
    g := ![![![143552094, 264191792, 363743228], ![83840027, -909909416, 440634]], ![![11149480, 20519722, 28251885], ![6511767, -70672582, 34224]]]
    h := ![![![-12017, -42365, -24216], ![-1292, 647776, 0]], ![![-6219, -21902, -12518], ![-576, 334864, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {10} * I107N1 =  Ideal.span {B.equivFun.symm ![-603, 85, -8]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E107RS1 


noncomputable def E113RS1 : RelationCertificate Table 4 ![![113, 0, 0], ![34, 1, 0]]
  ![47, 5, -4] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![452, 0, 0], ![136, 4, 0]]
    hsu := by decide
    w := ![![188, 20, -16], ![-340, 16, 8]]
    hw := by decide
    g := ![![![7989, -187, 265], ![3951, 0, -362]], ![![2421, -58, 80], ![1201, 0, -110]]]
    h := ![![![3053, 57836, 7012], ![1507, -198090, 0]], ![![-5671, -106221, -12878], ![-2555, 363804, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {4} * I113N1 =  Ideal.span {B.equivFun.symm ![47, 5, -4]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E113RS1 


noncomputable def E127RS0 : RelationCertificate Table 10 ![![127, 0, 0], ![61, 1, 0]]
  ![37319, 315, -1716] ![![10, 0, 0], ![4, 1, 0]] where
    su := ![![1270, 0, 0], ![610, 10, 0]]
    hsu := by decide
    w := ![![373190, 3150, -17160], ![-40570, 22820, -7320]]
    hw := by decide
    g := ![![![-1055160609171703, -1888182146600634, -2599027189693738], ![-610882458328734, 6497567974087407, -619516]], ![![-510282589956597, -913137267663225, -1256906591766703], ![-295426762748953, 3142266479281251, -299602]]]
    h := ![![![13035285, 542769233, 36190132], ![10534924, -1149037120, 0]], ![![-1449473, -60353132, -4024164], ![-1171394, 127767024, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {10} * I127N0 =  Ideal.span {B.equivFun.symm ![37319, 315, -1716]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E127RS0 


noncomputable def E127RS1 : RelationCertificate Table 10 ![![127, 0, 0], ![-37, 1, 0]]
  ![36297, 6085, 2932] ![![10, 0, 0], ![4, 1, 0]] where
    su := ![![1270, 0, 0], ![-370, 10, 0]]
    hsu := by decide
    w := ![![362970, 60850, 29320], ![482810, 80940, 39000]]
    hw := by decide
    g := ![![![797450834692255, 1427017280103016, 1964247314927616], ![461682061887208, -4910618287090557, -182808]], ![![-221514120745221, -396393688912792, -545624254140068], ![-128245017189364, 1364060635286706, 50780]]]
    h := ![![![-14879743, 320638589, -33757088], ![6859808, 1071788277, 0]], ![![-19792529, 426502258, -44902500], ![9124628, 1425655350, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {10} * I127N1 =  Ideal.span {B.equivFun.symm ![36297, 6085, 2932]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E127RS1 


noncomputable def E127RS2 : RelationCertificate Table 10 ![![127, 0, 0], ![-24, 1, 0]]
  ![70119, 11755, 5664] ![![10, 0, 0], ![4, 1, 0]] where
    su := ![![1270, 0, 0], ![-240, 10, 0]]
    hsu := by decide
    w := ![![701190, 117550, 56640], ![932690, 156360, 75340]]
    hw := by decide
    g := ![![![839460089762, 1502185087921, 2067713509054], ![486002544697, -5169283271216, -401162]], ![![-148765079218, -266210015579, -366430242113], ![-86127033235, 916075516422, 71092]]]
    h := ![![![-46670135, 615559161, -98506624], ![13666508, 3127586728, 0]], ![![-62078415, 818787868, -131028882], ![18178575, 4160168887, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {10} * I127N2 =  Ideal.span {B.equivFun.symm ![70119, 11755, 5664]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E127RS2 


noncomputable def E137RS1 : RelationCertificate Table 20 ![![137, 0, 0], ![-63, 1, 0]]
  ![39, 5, 4] ![![20, 0, 0], ![-6, 1, 0]] where
    su := ![![2740, 0, 0], ![-1260, 20, 0]]
    hsu := by decide
    w := ![![780, 100, 80], ![220, 40, 0]]
    hw := by decide
    g := ![![![62179304, -248716184, 143011808], ![-31089589, -715059102, -48]], ![![-25931467, 103725455, -59642138], ![12965726, 298210716, 20]]]
    h := ![![![55987, -2429315, 151852], ![-43360, -5200930, 0]], ![![15786, -684455, 42784], ![-12191, -1465352, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {20} * I137N1 =  Ideal.span {B.equivFun.symm ![39, 5, 4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E137RS1 
