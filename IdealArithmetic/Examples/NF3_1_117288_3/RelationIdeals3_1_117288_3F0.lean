import IdealArithmetic.Examples.NF3_1_117288_3.PrimesBelow3_1_117288_3F0
import IdealArithmetic.Examples.NF3_1_117288_3.ClassGroupData3_1_117288_3

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 80000 ![![2, 0, 0], ![0, 1, 0]]
  ![-4731, 198, 551] ![![160000, 0, 0], ![43702, 1, 0]] where
    su := ![![160000, 0, 0], ![0, 80000, 0]]
    hsu := by decide
    w := ![![-756960000, 31680000, 88160000], ![-206720000, 8640000, 24080000]]
    hw := by decide
    g := ![![![-11719201, 7359416406463, 168399991], ![42905866, -26943998560180, 0]], ![![65288757575, -41098484365825671, -940425709746], ![-239032566290, 150468113559359753, 0]]]
    h := ![![![-4731, 316, 440], ![-236, 222, 0]], ![![-1292, 86, 120], ![-64, 61, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {80000} * I2N0 =  Ideal.span {B.equivFun.symm ![-4731, 198, 551]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 20 ![![2, 0, 0], ![1, 1, 0]]
  ![-1, -2, 1] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![40, 0, 0], ![20, 20, 0]]
    hsu := by decide
    w := ![![-20, -40, 20], ![60, -20, 0]]
    hw := by decide
    g := ![![![7, -1345, -674], ![-59, 13481, 0]], ![![6, -1108, -555], ![-39, 11102, 0]]]
    h := ![![![0, 0, 1], ![-1, -1, 0]], ![![2, 0, 0], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {20} * I2N1 =  Ideal.span {B.equivFun.symm ![-1, -2, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 20 ![![5, 0, 0], ![9, 3, 1]]
  ![19, -2, 1] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![100, 0, 0], ![180, 60, 20]]
    hsu := by decide
    w := ![![380, -40, 20], ![100, 0, 0]]
    hw := by decide
    g := ![![![48, -9766, -4895], ![-479, 97900, 0]], ![![87, -17539, -8791], ![-862, 175821, 0]]]
    h := ![![![-7, -4, -1], ![6, 0, 0]], ![![-8, -3, -1], ![5, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {20} * I5N0 =  Ideal.span {B.equivFun.symm ![19, -2, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 640000 ![![5, 0, 0], ![2, 1, 0]]
  ![18274049, 2226958, 810171] ![![3200000, 0, 0], ![-916298, 1, 0]] where
    su := ![![3200000, 0, 0], ![1280000, 640000, 0]]
    hsu := by decide
    w := ![![58476956800000, 7126265600000, 2592547200000], ![-16744424320000, -2040551040000, -742355840000]]
    hw := by decide
    g := ![![![148702251825252996041, 1798063261532800804086759559, -1962312764551448426160], ![519314901746822089900, 6279400846564634963711999165, 0]], ![![58129062077628138597, 702879274968667967126216898, -767085898876491497485], ![203004916139083620733, 2454674876404772791951999412, 0]]]
    h := ![![![72072653711945, 43833242295220, 3898461984828], ![-180181588594740, -19492305873285, 0]], ![![-20637446981831, -12551309925749, -1116294438725], ![51593604372996, 5581471033694, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {640000} * I5N1 =  Ideal.span {B.equivFun.symm ![18274049, 2226958, 810171]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E5RS1 


noncomputable def E13RS1 : RelationCertificate Table 3200000 ![![13, 0, 0], ![1, 1, 0]]
  ![-26957, -3894, 2497] ![![3200000, 0, 0], ![-916298, 1, 0]] where
    su := ![![41600000, 0, 0], ![3200000, 3200000, 0]]
    hsu := by decide
    w := ![![-86262400000, -12460800000, 7990400000], ![24700800000, 3568000000, -2288000000]]
    hw := by decide
    g := ![![![230083, 3561650310, -3887], ![803522, 12438399945, 0]], ![![779042, 444404526, -485], ![2720659, 1551999989, 0]]]
    h := ![![![-2050, -2050, -1582], ![-307, 23063, 0]], ![![586, 586, 453], ![101, -6604, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {3200000} * I13N1 =  Ideal.span {B.equivFun.symm ![-26957, -3894, 2497]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E13RS1 


noncomputable def E19RS1 : RelationCertificate Table 8000 ![![19, 0, 0], ![-8, 1, 0]]
  ![1579, 218, 41] ![![8000, 0, 0], ![3702, 1, 0]] where
    su := ![![152000, 0, 0], ![-64000, 8000, 0]]
    hsu := by decide
    w := ![![12632000, 1744000, 328000], ![5848000, 808000, 152000]]
    hw := by decide
    g := ![![![-1975, 8159207, 2204], ![4268, -17631999, 0]], ![![-3435, -3328098, -899], ![7423, 7191998, 0]]]
    h := ![![![127094913, -17784521, 237212], ![301850221, -4506987, 0]], ![![58838561, -8233338, 109817], ![139741491, -2086504, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {8000} * I19N1 =  Ideal.span {B.equivFun.symm ![1579, 218, 41]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E19RS1 


noncomputable def E23RS0 : RelationCertificate Table 400 ![![23, 0, 0], ![6, 1, 0]]
  ![-4959, 1422, 139] ![![400, 0, 0], ![102, 1, 0]] where
    su := ![![9200, 0, 0], ![2400, 400, 0]]
    hsu := by decide
    w := ![![-1983600, 568800, 55600], ![-497200, 138000, 15600]]
    hw := by decide
    g := ![![![-495, 140785, 1362], ![282, -552303, 0]], ![![-177, 39060, 376], ![63, -153254, 0]]]
    h := ![![![-4905, -780, -4], ![17976, 231, 0]], ![![-1229, -197, -1], ![4504, 62, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {400} * I23N0 =  Ideal.span {B.equivFun.symm ![-4959, 1422, 139]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 3200000 ![![23, 0, 0], ![-5, 1, 0]]
  ![-36701, 20458, -4079] ![![3200000, 0, 0], ![-916298, 1, 0]] where
    su := ![![73600000, 0, 0], ![-16000000, 3200000, 0]]
    hsu := by decide
    w := ![![-117443200000, 65465600000, -13052800000], ![33628800000, -18745600000, 3737600000]]
    hw := by decide
    g := ![![![-5592254505704687804887856, -67619872950311963109665247298344, 73796813864395716465056539], ![-19529906666013677838040833, -236149804366066292688180924800162, 0]], ![![1256231084614556222307636, 15189971459849483652163780530859, -16577545143447715303819967], ![4387152946712292192479341, 53048144459032688972223894400011, 0]]]
    h := ![![![-688337935282, 142957821175, -1058046887], ![-3166354494957, 24335074322, 0]], ![![197099363698, -40934683514, 302962173], ![906657070909, -6968128811, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {3200000} * I23N1 =  Ideal.span {B.equivFun.symm ![-36701, 20458, -4079]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 3200000 ![![23, 0, 0], ![-1, 1, 0]]
  ![813149, -100842, -70929] ![![3200000, 0, 0], ![-916298, 1, 0]] where
    su := ![![73600000, 0, 0], ![-3200000, 3200000, 0]]
    hsu := by decide
    w := ![![2602076800000, -322694400000, -226972800000], ![-745091200000, 92403200000, 64992000000]]
    hw := by decide
    g := ![![![576332, -2502322776867, 2730905], ![2012731, -8738895955216, 0]], ![![50897510678619848, 615437513091565988772689, -671656505952890365], ![177750070579204051, 2149300819049249168003405, 0]]]
    h := ![![![73506, -42600, -3020], ![877489, -1469, 0]], ![![-21046, 12197, 864], ![-251217, 438, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {3200000} * I23N2 =  Ideal.span {B.equivFun.symm ![813149, -100842, -70929]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E23RS2 


noncomputable def E29RS1 : RelationCertificate Table 20 ![![29, 0, 0], ![14, 1, 0]]
  ![2279, 278, 101] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![580, 0, 0], ![280, 20, 0]]
    hsu := by decide
    w := ![![45580, 5560, 2020], ![10820, 1320, 480]]
    hw := by decide
    g := ![![![-945720, 191036240, 95754553], ![9457253, -1915091054, 0]], ![![-440256, 88932239, 44576185], ![4402592, -891523699, 0]]]
    h := ![![![174899, 21058, 615], ![-362128, -17734, 0]], ![![41505, 4998, 146], ![-85936, -4210, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {20} * I29N1 =  Ideal.span {B.equivFun.symm ![2279, 278, 101]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 


noncomputable def E31RS0 : RelationCertificate Table 400 ![![31, 0, 0], ![0, 1, 0]]
  ![-403, -26, 63] ![![400, 0, 0], ![102, 1, 0]] where
    su := ![![12400, 0, 0], ![0, 400, 0]]
    hsu := by decide
    w := ![![-161200, -10400, 25200], ![-37200, -4000, 6400]]
    hw := by decide
    g := ![![![-163509140, 273162735314, 2678081749], ![641212361, -1071232699386, 0]], ![![81755114, -136582366926, -1339050671], ![-320608286, 535620268419, 0]]]
    h := ![![![-13, -2, 2], ![36, 1, 0]], ![![-3, 0, 0], ![-10, 16, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {400} * I31N0 =  Ideal.span {B.equivFun.symm ![-403, -26, 63]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 400 ![![31, 0, 0], ![4, 1, 0]]
  ![437, 54, 23] ![![400, 0, 0], ![102, 1, 0]] where
    su := ![![12400, 0, 0], ![1600, 400, 0]]
    hsu := by decide
    w := ![![174800, 21600, 9200], ![46000, 5600, 2400]]
    hw := by decide
    g := ![![![-532133138, 888996094778, 8715699135], ![2086796619, -3486279653998, 0]], ![![-60091132, 100389783959, 984219344], ![235651498, -393687737599, 0]]]
    h := ![![![435, 108, 1], ![-3262, -8, 0]], ![![109, 26, 0], ![-816, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {400} * I31N1 =  Ideal.span {B.equivFun.symm ![437, 54, 23]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 400 ![![31, 0, 0], ![-4, 1, 0]]
  ![91, -278, 89] ![![400, 0, 0], ![102, 1, 0]] where
    su := ![![12400, 0, 0], ![-1600, 400, 0]]
    hsu := by decide
    w := ![![36400, -111200, 35600], ![14800, -29600, 8800]]
    hw := by decide
    g := ![![![-43615102521138, 72864587549047476, 714362893608742], ![171039617729849, -285745157443497270, 0]], ![![5728250792054, -9569773019414698, -93821854693492], ![-22463728596286, 37528741877396819, 0]]]
    h := ![![![117, -34, 2], ![884, 27, 0]], ![![51, -12, 0], ![386, 22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {400} * I31N2 =  Ideal.span {B.equivFun.symm ![91, -278, 89]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS2 
