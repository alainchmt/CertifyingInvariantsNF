import IdealArithmetic.Examples.NF3_1_564300_3.PrimesBelow3_1_564300_3F0
import IdealArithmetic.Examples.NF3_1_564300_3.ClassGroupData3_1_564300_3

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 352947 ![![2, 0, 0], ![0, 1, 0]]
  ![-1809, 951, -86] ![![705894, 0, 0], ![-151794, 1, 0]] where
    su := ![![705894, 0, 0], ![0, 352947, 0]]
    hsu := by decide
    w := ![![-1276962246, 671305194, -60706884], ![274592766, -144355323, 13059039]]
    hw := by decide
    g := ![![![-1050143, -3714541441331, 122354686], ![-4883524, -17273887743862, 0]], ![![1202938, 3700255774041, -121884125], ![5594073, 17207454506545, 0]]]
    h := ![![![-1809, 1520, -16], ![-1138, -28, 0]], ![![389, -328, 1], ![247, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {352947} * I2N0 =  Ideal.span {B.equivFun.symm ![-1809, 951, -86]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 343 ![![3, 0, 0], ![0, 1, 0]]
  ![-363, -2, -11] ![![343, 0, 0], ![155, 1, 0]] where
    su := ![![1029, 0, 0], ![0, 343, 0]]
    hsu := by decide
    w := ![![-124509, -686, -3773], ![-56595, -343, -1715]]
    hw := by decide
    g := ![![![9004, -8284165, -267233], ![-19925, 18332184, 0]], ![![5, 0, 0], ![-11, 0, 0]]]
    h := ![![![-121, -2, -2], ![4, -1, 0]], ![![-55, -2, -5], ![5, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {343} * I3N0 =  Ideal.span {B.equivFun.symm ![-363, -2, -11]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 6 ![![5, 0, 0], ![20, 0, 1]]
  ![-30, 0, -1] ![![6, 0, 0], ![0, 1, 0]] where
    su := ![![30, 0, 0], ![120, 0, 6]]
    hsu := by decide
    w := ![![-180, 0, -6], ![-30, 0, 0]]
    hw := by decide
    g := ![![![0, 0, 0], ![-1, 0, 0]], ![![-1, 0, 0], ![2, 0, 0]]]
    h := ![![![-2, 0, 0], ![-1, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {6} * I5N0 =  Ideal.span {B.equivFun.symm ![-30, 0, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 5764801 ![![7, 0, 0], ![19, -3, 1]]
  ![115999, -9083, 4409] ![![5764801, 0, 0], ![-740039, 1, 0]] where
    su := ![![40353607, 0, 0], ![109531219, -17294403, 5764801]]
    hsu := by decide
    w := ![![668711151199, -52361687483, 25417007609], ![-85843651691, 6721757966, -3262877366]]
    hw := by decide
    g := ![![![10205108732460, 465832959713396794166, -3147354123994888], ![79496379280003, 3628774040271970867460, 0]], ![![26843869625950, 1225343108453114609851, -8278909006506082], ![209110015098591, 9545252583923053603930, 0]]]
    h := ![![![2115, 985, -131], ![5326, 0, 0]], ![![-287, -124, 16], ![-678, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {5764801} * I7N0 =  Ideal.span {B.equivFun.symm ![115999, -9083, 4409]} * (J0 ^ 8*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1 ![![7, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![7, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![7, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![7, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1} * I7N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 34588806 ![![11, 0, 0], ![3, 1, 0]]
  ![259356, 19350, 9013] ![![34588806, 0, 0], ![-6504840, 1, 0]] where
    su := ![![380476866, 0, 0], ![103766418, 34588806, 0]]
    hsu := by decide
    w := ![![8970814368936, 669293396100, 311748908478], ![-1687069012650, -125868665034, -58628026170]]
    hw := by decide
    g := ![![![586371666, 110871766999486136, -85222516618], ![3117969973, 589549018826355633, 0]], ![![145350993, 26878773338444568, -20660595294], ![772888695, 142925064493735784, 0]]]
    h := ![![![252318, 83300, 9643], ![-838714, -19412, 0]], ![![-47453, -15667, -1815], ![157736, 3654, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {34588806} * I11N0 =  Ideal.span {B.equivFun.symm ![259356, 19350, 9013]} * (J0 ^ 8*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 100842 ![![11, 0, 0], ![4, 1, 0]]
  ![4194, -198, 283] ![![100842, 0, 0], ![49890, 1, 0]] where
    su := ![![1109262, 0, 0], ![403368, 100842, 0]]
    hsu := by decide
    w := ![![422931348, -19966716, 28538286], ![209247150, -9882516, 14117880]]
    hw := by decide
    g := ![![![-31652371827466, 8030858969205885243, 804856581463252], ![63978522345667, -16232669477583451634, 0]], ![![-10071209233134, 2555273308458104868, 256090730473038], ![20356802595464, -5164940288472419597, 0]]]
    h := ![![![4054, 1010, 163], ![-10100, -302, 0]], ![![2005, 499, 80], ![-4995, -148, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {100842} * I11N1 =  Ideal.span {B.equivFun.symm ![4194, -198, 283]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E11RS1 


noncomputable def E19RS0 : RelationCertificate Table 4941258 ![![19, 0, 0], ![3, 1, 0]]
  ![-409656, -1795, -13817] ![![4941258, 0, 0], ![-2466516, 0, 1]] where
    su := ![![93883902, 0, 0], ![14823774, 4941258, 0]]
    hsu := by decide
    w := ![![-2024215987248, -8869558110, -68273361786], ![1010423024646, 4427367168, 34079856426]]
    hw := by decide
    g := ![![![1958984, -161068283411, 0], ![-101, -322669815990, 0]], ![![494873, -40693600268, 0], ![-147, -81521924940, 0]]]
    h := ![![![-4796348783628, -1644904294732, -76868957308], ![30376875493092, 292102035007, 0]], ![![2394181882219, 821082919141, 38370492488], ![-15163151852558, -145807870075, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {4941258} * I19N0 =  Ideal.span {B.equivFun.symm ![-409656, -1795, -13817]} * (J0 ^ 7*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_2 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 42 ![![19, 0, 0], ![8, 1, 0]]
  ![-66, -1, -2] ![![42, 0, 0], ![18, 0, 1]] where
    su := ![![798, 0, 0], ![336, 42, 0]]
    hsu := by decide
    w := ![![-2772, -42, -84], ![-1218, 0, -42]]
    hw := by decide
    g := ![![![-150, 67, 1], ![-41, 234, 0]], ![![-76, 30, 0], ![2, 105, 0]]]
    h := ![![![-12102, -1909, -248], ![28734, 942, 0]], ![![-5319, -839, -109], ![12629, 414, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {42} * I19N1 =  Ideal.span {B.equivFun.symm ![-66, -1, -2]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 34588806 ![![23, 0, 0], ![-6, 1, 0]]
  ![80532, -5461, 10267] ![![34588806, 0, 0], ![12357258, 0, 1]] where
    su := ![![795542538, 0, 0], ![-207532836, 34588806, 0]]
    hsu := by decide
    w := ![![2785505724792, -188889469566, 355123271202], ![995154537426, -67482760506, 126871740408]]
    hw := by decide
    g := ![![![-36128054, -14881356590471, 0], ![431, 41654030833179, 0]], ![![-8901520, 1423434150397, -1], ![34588734, -3984298718277, 0]]]
    h := ![![![121068, -20645, 1124], ![450672, -3117, 0]], ![![43253, -7375, 401], ![161008, -1111, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {34588806} * I23N1 =  Ideal.span {B.equivFun.symm ![80532, -5461, 10267]} * (J0 ^ 8*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_2 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 6 ![![29, 0, 0], ![-5, 1, 0]]
  ![-24, 0, -1] ![![6, 0, 0], ![0, 1, 0]] where
    su := ![![174, 0, 0], ![-30, 6, 0]]
    hsu := by decide
    w := ![![-144, 0, -6], ![-30, 6, 0]]
    hw := by decide
    g := ![![![-1, -171, -1], ![1025, 1, 0]], ![![0, 29, 0], ![-173, 0, 0]]]
    h := ![![![-26, 9, -4], ![-146, 23, 0]], ![![-5, 6, -5], ![-28, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {6} * I29N1 =  Ideal.span {B.equivFun.symm ![-24, 0, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 49 ![![31, 0, 0], ![11, 1, 0]]
  ![-1, -5, -3] ![![49, 0, 0], ![8, 1, 0]] where
    su := ![![1519, 0, 0], ![539, 49, 0]]
    hsu := by decide
    w := ![![-49, -245, -147], ![-98, 49, -49]]
    hw := by decide
    g := ![![![-13, 812, 508], ![51, -4980, 0]], ![![-9, 340, 213], ![44, -2088, 0]]]
    h := ![![![-412, -44, -3], ![1161, 18, 0]], ![![-692, -76, -6], ![1950, 37, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {49} * I31N1 =  Ideal.span {B.equivFun.symm ![-1, -5, -3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E31RS1 
