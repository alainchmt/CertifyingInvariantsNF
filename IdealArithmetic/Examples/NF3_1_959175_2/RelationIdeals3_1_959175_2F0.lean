import IdealArithmetic.Examples.NF3_1_959175_2.PrimesBelow3_1_959175_2F0
import IdealArithmetic.Examples.NF3_1_959175_2.ClassGroupData3_1_959175_2

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 61009 ![![3, 0, 0], ![0, 1, 0]]
  ![-25442, -1059, -1508] ![![61009, 0, 0], ![16293, 1, 0]] where
    su := ![![183027, 0, 0], ![0, 61009, 0]]
    hsu := by decide
    w := ![![-1552190978, -64608531, -92001572], ![-414800191, -17265547, -24586627]]
    hw := by decide
    g := ![![![1076054201799840, -3703232631343131962, -2955130081588695], ![226670138517878, 13868425472895647864, 78]], ![![2735208621, -9413204312628, -7511611070], ![576174492, 35251990751516, 0]]]
    h := ![![![-7594, -31166, -2808], ![93503, 532, 0]], ![![-2028, -8330, -754], ![24993, 143, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {61009} * I3N0 =  Ideal.span {B.equivFun.symm ![-25442, -1059, -1508]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 3211 ![![5, 0, 0], ![0, 1, 0]]
  ![115, 14, 26] ![![3211, 0, 0], ![238, 1, 0]] where
    su := ![![16055, 0, 0], ![0, 3211, 0]]
    hsu := by decide
    w := ![![369265, 44954, 83486], ![32110, 3211, 6422]]
    hw := by decide
    g := ![![![-25221549561059, 1195695003142373, 65864529585274], ![-1497051943397, -16268538805250924, -125220]], ![![-75664644734912, 3587084822251525, 197593578445306], ![-4491155596542, -48805613869055320, -375660]]]
    h := ![![![-417355, -160528, 1085188], ![-32102, -417378, 0]], ![![-32104, -12349, 83476], ![-2466, -32106, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3211} * I5N0 =  Ideal.span {B.equivFun.symm ![115, 14, 26]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 4693 ![![7, 0, 0], ![0, 1, 0]]
  ![-837, 100, -26] ![![4693, 0, 0], ![2214, 1, 0]] where
    su := ![![32851, 0, 0], ![0, 4693, 0]]
    hsu := by decide
    w := ![![-3928041, 469300, -122018], ![-1858428, 220571, -56316]]
    hw := by decide
    g := ![![![12367901788629, -6404506246396491, -37639497658526], ![4470067831815, 13587858654733680, -34]], ![![2182522573173, -1130181957503524, -6642117207255], ![788818032159, 2397804311820075, -6]]]
    h := ![![![1674, 717, -4667], ![103, 2511, 0]], ![![792, 339, -2208], ![50, 1188, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {4693} * I7N0 =  Ideal.span {B.equivFun.symm ![-837, 100, -26]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E7RS0 


noncomputable def E13RS0 : RelationCertificate Table 1 ![![13, 0, 0], ![4, 1, 0]]
  ![1, 0, 0] ![![13, 0, 0], ![4, 1, 0]] where
    su := ![![13, 0, 0], ![4, 1, 0]]
    hsu := by decide
    w := ![![13, 0, 0], ![4, 1, 0]]
    hw := by decide
    g := ![![![1691, -120, 60], ![520, 0, -130]], ![![507, -36, 18], ![157, 0, -39]]]
    h := ![![![1691, -120, 60], ![520, 0, -130]], ![![507, -36, 18], ![157, 0, -39]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {1} * I13N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 13 ![![13, 0, 0], ![9, 6, 1]]
  ![-32, 3, 0] ![![13, 0, 0], ![4, 1, 0]] where
    su := ![![169, 0, 0], ![117, 78, 13]]
    hsu := by decide
    w := ![![-416, 39, 0], ![-143, -26, 39]]
    hw := by decide
    g := ![![![-4231548, 298394, -150003], ![-1279052, 0, 325008]], ![![-4431628, 312509, -157094], ![-1339538, 0, 340380]]]
    h := ![![![-2781, 1015, -1883], ![-1601, 326, 0]], ![![-913, 324, -613], ![-508, 106, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {13} * I13N1 =  Ideal.span {B.equivFun.symm ![-32, 3, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 13 ![![13, 0, 0], ![-1, 0, 1]]
  ![-2, 1, 0] ![![13, 0, 0], ![4, 1, 0]] where
    su := ![![169, 0, 0], ![-13, 0, 13]]
    hsu := by decide
    w := ![![-26, 13, 0], ![-13, 0, 13]]
    hw := by decide
    g := ![![![4801200, -338564, 170197], ![1451252, 0, -368760]], ![![-371523, 26198, -13170], ![-112293, 0, 28535]]]
    h := ![![![43, -2, 0], ![6, -3, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {13} * I13N2 =  Ideal.span {B.equivFun.symm ![-2, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E13RS2 


noncomputable def E19RS1 : RelationCertificate Table 1 ![![19, 0, 0], ![-9, 1, 0]]
  ![1, 0, 0] ![![19, 0, 0], ![-9, 1, 0]] where
    su := ![![19, 0, 0], ![-9, 1, 0]]
    hsu := by decide
    w := ![![19, 0, 0], ![-9, 1, 0]]
    hw := by decide
    g := ![![![11, 22, -26], ![0, 38, 0]], ![![4, -12, 13], ![20, -19, 0]]]
    h := ![![![11, 22, -26], ![0, 38, 0]], ![![4, -12, 13], ![20, -19, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {1} * I19N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E19RS1 


noncomputable def E23RS0 : RelationCertificate Table 247 ![![23, 0, 0], ![0, 1, 0]]
  ![-28, -12, 13] ![![247, 0, 0], ![-9, 1, 0]] where
    su := ![![5681, 0, 0], ![0, 247, 0]]
    hsu := by decide
    w := ![![-6916, -2964, 3211], ![2717, 0, -247]]
    hw := by decide
    g := ![![![333302476582093, 734037915966639, -867455465382463], ![-9172811227618, 16481653848748466, 12037387]], ![![8179201724205, 18013200050210, -21287250280533], ![-225099657660, 404457755489186, 295396]]]
    h := ![![![34524, 13783, -89765], ![611, 158816, 0]], ![![-13563, -5416, 35265], ![-216, -62392, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {247} * I23N0 =  Ideal.span {B.equivFun.symm ![-28, -12, 13]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS0 


noncomputable def E29RS0 : RelationCertificate Table 13 ![![29, 0, 0], ![9, 1, 0]]
  ![216, 9, 13] ![![13, 0, 0], ![4, 1, 0]] where
    su := ![![377, 0, 0], ![117, 13, 0]]
    hsu := by decide
    w := ![![2808, 117, 169], ![3224, 130, 195]]
    hw := by decide
    g := ![![![4020, -284, 143], ![1218, 0, -309]], ![![1380, -98, 49], ![423, 0, -106]]]
    h := ![![![900, -1359, -2509], ![234, 5598, 0]], ![![1029, -1561, -2881], ![283, 6428, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {13} * I29N0 =  Ideal.span {B.equivFun.symm ![216, 9, 13]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 13 ![![29, 0, 0], ![11, 1, 0]]
  ![11, 1, 0] ![![13, 0, 0], ![4, 1, 0]] where
    su := ![![377, 0, 0], ![143, 13, 0]]
    hsu := by decide
    w := ![![143, 13, 0], ![39, 13, 13]]
    hw := by decide
    g := ![![![2997247, -211356, 106249], ![905979, 0, -230206]], ![![1658049, -116921, 58776], ![501189, 0, -127348]]]
    h := ![![![173, -353, -507], ![59, 1131, 0]], ![![38, -94, -134], ![36, 299, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {13} * I29N1 =  Ideal.span {B.equivFun.symm ![11, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 4693 ![![31, 0, 0], ![-13, 1, 0]]
  ![-1789, -61, -78] ![![4693, 0, 0], ![2214, 1, 0]] where
    su := ![![145483, 0, 0], ![-61009, 4693, 0]]
    hsu := by decide
    w := ![![-8395777, -286273, -366054], ![-3974971, -136097, -173641]]
    hw := by decide
    g := ![![![123343154059302, -63871141122056105, -375372835035479], ![44579288725678, 135509593447794112, 81]], ![![-45682937985189, 23656127500521085, 139027853422286], ![-16510951880173, -50189055085440132, -30]]]
    h := ![![![-58161, -197597, 170742], ![18046, -407160, 0]], ![![-27541, -93551, 80837], ![8532, -192768, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {4693} * I31N1 =  Ideal.span {B.equivFun.symm ![-1789, -61, -78]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E31RS1 
