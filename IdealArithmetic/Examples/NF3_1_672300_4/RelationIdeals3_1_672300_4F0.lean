import IdealArithmetic.Examples.NF3_1_672300_4.PrimesBelow3_1_672300_4F0
import IdealArithmetic.Examples.NF3_1_672300_4.ClassGroupData3_1_672300_4

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 7 ![![2, 0, 0], ![0, 1, 0]]
  ![-8, 1, 0] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![14, 0, 0], ![0, 7, 0]]
    hsu := by decide
    w := ![![-56, 7, 0], ![-14, -7, 7]]
    hw := by decide
    g := ![![![-246, 25, -5], ![-66, 0, 12]], ![![-115, 12, -2], ![-26, 0, 6]]]
    h := ![![![-4, 0, 0], ![1, 0, 0]], ![![-2, -12, -3], ![24, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {7} * I2N0 =  Ideal.span {B.equivFun.symm ![-8, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 49 ![![3, 0, 0], ![-1, 1, 0]]
  ![-157, 7, 9] ![![49, 0, 0], ![-11, 4, 1]] where
    su := ![![147, 0, 0], ![-49, 49, 0]]
    hsu := by decide
    w := ![![-7693, 343, 441], ![8869, -931, -98]]
    hw := by decide
    g := ![![![-12872, 1765, -2476], ![3029, 4092, 0]], ![![3592, -414, 641], ![-825, -1023, 0]]]
    h := ![![![670, -720, 3069], ![-461, -1314, 0]], ![![-105, 159, -682], ![88, 292, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {49} * I3N0 =  Ideal.span {B.equivFun.symm ![-157, 7, 9]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 49 ![![5, 0, 0], ![0, 1, 0]]
  ![-243, -14, -13] ![![49, 0, 0], ![-7, 0, 1]] where
    su := ![![245, 0, 0], ![0, 49, 0]]
    hsu := by decide
    w := ![![-11907, -686, -637], ![-1029, -49, -49]]
    hw := by decide
    g := ![![![-4131, 433, -40], ![632, 1326, 0]], ![![-54, 6, -1], ![32, 18, 0]]]
    h := ![![![23571, -11359, 82666], ![-2268, -59049, 0]], ![![2037, -982, 7144], ![-194, -5103, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {49} * I5N0 =  Ideal.span {B.equivFun.symm ![-243, -14, -13]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 1 ![![7, 0, 0], ![2, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![7, 0, 0], ![2, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![2, 1, 0]]
    hw := by decide
    g := ![![![1159, -117, 24], ![315, 0, -56]], ![![288, -30, 6], ![85, 0, -14]]]
    h := ![![![1159, -117, 24], ![315, 0, -56]], ![![288, -30, 6], ![85, 0, -14]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {1} * I7N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1 ![![7, 0, 0], ![7, 0, 1]]
  ![1, 0, 0] ![![7, 0, 0], ![7, 0, 1]] where
    su := ![![7, 0, 0], ![7, 0, 1]]
    hsu := by decide
    w := ![![7, 0, 0], ![7, 0, 1]]
    hw := by decide
    g := ![![![231, -6, -31], ![238, -21, 0]], ![![230, -6, -31], ![239, -21, 0]]]
    h := ![![![231, -6, -31], ![238, -21, 0]], ![![230, -6, -31], ![239, -21, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1} * I7N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS1 


noncomputable def E7RS2 : RelationCertificate Table 49 ![![7, 0, 0], ![-6, -3, -1]]
  ![14083, 786, 746] ![![49, 0, 0], ![3, -10, 1]] where
    su := ![![343, 0, 0], ![-294, -147, -49]]
    hsu := by decide
    w := ![![690067, 38514, 36554], ![-983283, -54880, -52087]]
    hw := by decide
    g := ![![![31, -2, 0], ![10, 0, 0]], ![![51, -15, 8], ![9, 0, 0]]]
    h := ![![![1593931, -584643, 186075], ![-1142245, 111092, 0]], ![![-2271201, 833066, -265139], ![1627602, -158296, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N2 : Ideal.span {49} * I7N2 =  Ideal.span {B.equivFun.symm ![14083, 786, 746]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E7RS2 


noncomputable def E13RS0 : RelationCertificate Table 49 ![![13, 0, 0], ![2, 2, 1]]
  ![29, 3, -5] ![![49, 0, 0], ![3, -10, 1]] where
    su := ![![637, 0, 0], ![98, 98, 49]]
    hsu := by decide
    w := ![![1421, 147, -245], ![8085, -833, -98]]
    hw := by decide
    g := ![![![-13, 3, -1], ![18, 0, 0]], ![![-29, 4, -2], ![27, 0, 0]]]
    h := ![![![1, -1, -1], ![8, 0, 0]], ![![11, -3, -1], ![11, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {49} * I13N0 =  Ideal.span {B.equivFun.symm ![29, 3, -5]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 7 ![![13, 0, 0], ![-2, 1, 0]]
  ![85, -48, 29] ![![7, 0, 0], ![3, -3, 1]] where
    su := ![![91, 0, 0], ![-14, 7, 0]]
    hsu := by decide
    w := ![![595, -336, 203], ![-19299, 1281, 784]]
    hw := by decide
    g := ![![![43417, 9111, 524], ![14780, 0, 0]], ![![21292, 4468, 257], ![7248, 0, 0]]]
    h := ![![![501, -766, 1805], ![-134, -3348, 0]], ![![-15023, 22858, -54026], ![4079, 100350, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {7} * I13N1 =  Ideal.span {B.equivFun.symm ![85, -48, 29]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS1 


noncomputable def E17RS0 : RelationCertificate Table 49 ![![17, 0, 0], ![4, 1, 0]]
  ![-9, 2, 0] ![![49, 0, 0], ![-18, 4, 1]] where
    su := ![![833, 0, 0], ![196, 49, 0]]
    hsu := by decide
    w := ![![-441, 98, 0], ![490, -98, 49]]
    hw := by decide
    g := ![![![69791, 310, -2212], ![-25652, 0, -5828]], ![![279156, 1241, -8848], ![-102622, 0, -23312]]]
    h := ![![![-10789, -17222, -40670], ![-3534, 98770, 0]], ![![11962, 19102, 45113], ![3944, -109560, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {49} * I17N0 =  Ideal.span {B.equivFun.symm ![-9, 2, 0]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E17RS0 


noncomputable def E17RS2 : RelationCertificate Table 49 ![![17, 0, 0], ![7, 1, 0]]
  ![-5645, -315, -299] ![![49, 0, 0], ![-11, 4, 1]] where
    su := ![![833, 0, 0], ![343, 49, 0]]
    hsu := by decide
    w := ![![-276605, -15435, -14651], ![-188699, -10535, -9996]]
    hw := by decide
    g := ![![![-1502403, 202885, -286585], ![348038, 472230, 0]], ![![-723375, 97686, -137985], ![167554, 227370, 0]]]
    h := ![![![2159683, 8085829, 9527143], ![1364932, -23137390, 0]], ![![1473320, 5516094, 6499348], ![931147, -15784160, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {49} * I17N2 =  Ideal.span {B.equivFun.symm ![-5645, -315, -299]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E17RS2 


noncomputable def E19RS1 : RelationCertificate Table 49 ![![19, 0, 0], ![-5, 1, 0]]
  ![663, 37, 35] ![![49, 0, 0], ![-18, 4, 1]] where
    su := ![![931, 0, 0], ![-245, 49, 0]]
    hsu := by decide
    w := ![![32487, 1813, 1715], ![17444, 980, 931]]
    hw := by decide
    g := ![![![5539931, 24631, -175592], ![-2036621, 0, -462636]], ![![-936321, -4164, 29677], ![344234, 0, 78192]]]
    h := ![![![862245, -2864913, 3365593], ![-377672, -9135176, 0]], ![![462974, -1538286, 1807121], ![-202786, -4905040, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {49} * I19N1 =  Ideal.span {B.equivFun.symm ![663, 37, 35]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E19RS1 


noncomputable def E29RS0 : RelationCertificate Table 7 ![![29, 0, 0], ![2, 1, 0]]
  ![15, -7, 4] ![![7, 0, 0], ![7, 0, 1]] where
    su := ![![203, 0, 0], ![14, 7, 0]]
    hsu := by decide
    w := ![![105, -49, 28], ![-819, 98, 0]]
    hw := by decide
    g := ![![![1586407, 10, 226638], ![-1586420, 7, 0]], ![![109084, 4, 15591], ![-109122, 4, 0]]]
    h := ![![![-55, -28, -192], ![9, 796, 0]], ![![-5, 0, 0], ![14, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {7} * I29N0 =  Ideal.span {B.equivFun.symm ![15, -7, 4]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 49 ![![29, 0, 0], ![12, 1, 0]]
  ![-59, -3, -3] ![![49, 0, 0], ![3, -10, 1]] where
    su := ![![1421, 0, 0], ![588, 49, 0]]
    hsu := by decide
    w := ![![-2891, -147, -147], ![3969, 245, 196]]
    hw := by decide
    g := ![![![-4, 3, 0], ![15, 0, 0]], ![![0, 1, 0], ![6, 0, 0]]]
    h := ![![![76853, 535370, 341793], ![50267, -1416000, 0]], ![![-105447, -734528, -468940], ![-68955, 1942752, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {49} * I29N1 =  Ideal.span {B.equivFun.symm ![-59, -3, -3]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E29RS1 


noncomputable def E29RS2 : RelationCertificate Table 7 ![![29, 0, 0], ![-14, 1, 0]]
  ![-246847, -13777, -13076] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![203, 0, 0], ![-98, 7, 0]]
    hsu := by decide
    w := ![![-1727929, -96439, -91532], ![-2561104, -142940, -135667]]
    hw := by decide
    g := ![![![-691, 75, -36], ![-184, 0, 45]], ![![170, -12, 13], ![54, 0, -18]]]
    h := ![![![4693099, -49510066, 23167956], ![-3972863, -95983400, 0]], ![![6956028, -73382894, 34339111], ![-5888494, -142264800, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {7} * I29N2 =  Ideal.span {B.equivFun.symm ![-246847, -13777, -13076]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E29RS2 
