import IdealArithmetic.Examples.NF3_1_888300_3.PrimesBelow3_1_888300_3F2
import IdealArithmetic.Examples.NF3_1_888300_3.ClassGroupData3_1_888300_3

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 49 ![![83, 0, 0], ![1, 1, 0]]
  ![-3127, -864, -61] ![![49, 0, 0], ![-23, 1, 0]] where
    su := ![![4067, 0, 0], ![49, 49, 0]]
    hsu := by decide
    w := ![![-153223, -42336, -2989], ![27391, 7595, 539]]
    hw := by decide
    g := ![![![-791340, -100799767, 4384095], ![-1685653, -214820606, 0]], ![![-17589, -2244151, 97605], ![-37488, -4782648, 0]]]
    h := ![![![-38, -38, -28], ![27, 2263, 0]], ![![6, 6, 5], ![61, -404, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {49} * I83N0 =  Ideal.span {B.equivFun.symm ![-3127, -864, -61]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E83RS0 


noncomputable def E83RS2 : RelationCertificate Table 7 ![![83, 0, 0], ![-40, 1, 0]]
  ![-423, -27, 4] ![![7, 0, 0], ![-2, 1, 0]] where
    su := ![![581, 0, 0], ![-280, 7, 0]]
    hsu := by decide
    w := ![![-2961, -189, 28], ![3766, 231, -35]]
    hw := by decide
    g := ![![![67, 2182, -1115], ![293, 7802, 0]], ![![-36, -1066, 544], ![-141, -3807, 0]]]
    h := ![![![-8341, 250, -1], ![-17297, 87, 0]], ![![10766, -271, 0], ![22326, -5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N2 : Ideal.span {7} * I83N2 =  Ideal.span {B.equivFun.symm ![-423, -27, 4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E83RS2 


noncomputable def E97RS1 : RelationCertificate Table 21 ![![97, 0, 0], ![4, 1, 0]]
  ![-193, -16, 2] ![![21, 0, 0], ![8, 1, 0]] where
    su := ![![2037, 0, 0], ![84, 21, 0]]
    hsu := by decide
    w := ![![-4053, -336, 42], ![-84, -21, 0]]
    hw := by decide
    g := ![![![-505, 32041, 4013], ![1347, -84275, 0]], ![![-24, 989, 124], ![62, -2604, 0]]]
    h := ![![![-15037, -3767, -2], ![364599, 196, 0]], ![![-316, -83, -1], ![7662, 97, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {21} * I97N1 =  Ideal.span {B.equivFun.symm ![-193, -16, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E97RS1 


noncomputable def E101RS0 : RelationCertificate Table 21 ![![101, 0, 0], ![30, 1, 0]]
  ![-201, -56, -4] ![![21, 0, 0], ![-104, -5, 1]] where
    su := ![![2121, 0, 0], ![630, 21, 0]]
    hsu := by decide
    w := ![![-4221, -1176, -84], ![-5376, -1491, -105]]
    hw := by decide
    g := ![![![75, 1, -1], ![89, 0, 0]], ![![98, 4, -1], ![37, 0, 0]]]
    h := ![![![-81621, -3080, -12], ![274784, 1208, 0]], ![![-103916, -3913, -15], ![349842, 1510, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {21} * I101N0 =  Ideal.span {B.equivFun.symm ![-201, -56, -4]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 7 ![![101, 0, 0], ![-24, 1, 0]]
  ![291, 22, -3] ![![7, 0, 0], ![-2, 1, 0]] where
    su := ![![707, 0, 0], ![-168, 7, 0]]
    hsu := by decide
    w := ![![2037, 154, -21], ![-2772, -203, 28]]
    hw := by decide
    g := ![![![-119, -2723, 1385], ![-355, -9696, 0]], ![![28, 660, -336], ![87, 2352, 0]]]
    h := ![![![51879, -2258, 4], ![218312, -407, 0]], ![![-70524, 3083, -6], ![-296772, 610, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {7} * I101N1 =  Ideal.span {B.equivFun.symm ![291, 22, -3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E101RS1 


noncomputable def E101RS2 : RelationCertificate Table 147 ![![101, 0, 0], ![-6, 1, 0]]
  ![173, 59, 5] ![![147, 0, 0], ![-114, -1, 1]] where
    su := ![![14847, 0, 0], ![-882, 147, 0]]
    hsu := by decide
    w := ![![25431, 8673, 735], ![19698, 4851, 294]]
    hw := by decide
    g := ![![![404036669, 29782940, 1246297], ![-313528499, -130322786, 0]], ![![-5799504, -427506, -17890], ![4500499, 1870662, 0]]]
    h := ![![![199, -32, 0], ![3321, 5, 0]], ![![154, -25, 0], ![2570, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {147} * I101N2 =  Ideal.span {B.equivFun.symm ![173, 59, 5]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E101RS2 


noncomputable def E103RS1 : RelationCertificate Table 147 ![![103, 0, 0], ![-31, 1, 0]]
  ![159, 17, -2] ![![147, 0, 0], ![-644, -35, 7]] where
    su := ![![15141, 0, 0], ![-4557, 147, 0]]
    hsu := by decide
    w := ![![23373, 2499, -294], ![35574, 1617, -294]]
    hw := by decide
    g := ![![![-110110299, -63420556, -8001133], ![497107217, 65816685, 0]], ![![32625371, 18791281, 2370705], ![-147291005, -19501240, 0]]]
    h := ![![![763, -25, 0], ![2530, -2, 0]], ![![1134, -37, 0], ![3760, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {147} * I103N1 =  Ideal.span {B.equivFun.symm ![159, 17, -2]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E103RS1 


noncomputable def E127RS1 : RelationCertificate Table 7 ![![127, 0, 0], ![43, 1, 0]]
  ![-1367, -74, 12] ![![7, 0, 0], ![-2, 1, 0]] where
    su := ![![889, 0, 0], ![301, 7, 0]]
    hsu := by decide
    w := ![![-9569, -518, 84], ![11494, 581, -98]]
    hw := by decide
    g := ![![![22567, 605158, -308340], ![80008, 2158340, 0]], ![![7645, 205778, -104854], ![27219, 733960, 0]]]
    h := ![![![-263874, -7087, -22], ![779317, 2806, 0]], ![![316906, 8450, 25], ![-935940, -3189, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {7} * I127N1 =  Ideal.span {B.equivFun.symm ![-1367, -74, 12]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E127RS1 


noncomputable def E137RS0 : RelationCertificate Table 21 ![![137, 0, 0], ![11, 1, 0]]
  ![11, 1, 0] ![![21, 0, 0], ![-707, -56, 7]] where
    su := ![![2877, 0, 0], ![231, 21, 0]]
    hsu := by decide
    w := ![![231, 21, 0], ![-2667, -273, 21]]
    hw := by decide
    g := ![![![24, -1, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![-252, -34, -1], ![3127, 138, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {21} * I137N0 =  Ideal.span {B.equivFun.symm ![11, 1, 0]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 21 ![![137, 0, 0], ![58, 1, 0]]
  ![-51, -14, -1] ![![21, 0, 0], ![-707, -56, 7]] where
    su := ![![2877, 0, 0], ![1218, 21, 0]]
    hsu := by decide
    w := ![![-1071, -294, -21], ![5397, 1344, 84]]
    hw := by decide
    g := ![![![9, 16, -1], ![8, 0, 0]], ![![67, 11, -1], ![5, 0, 0]]]
    h := ![![![-599, -68, -1], ![1414, 136, 0]], ![![2393, 40, 0], ![-5648, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {21} * I137N1 =  Ideal.span {B.equivFun.symm ![-51, -14, -1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E137RS1 


noncomputable def E137RS2 : RelationCertificate Table 21 ![![137, 0, 0], ![68, 1, 0]]
  ![71, -5, 0] ![![21, 0, 0], ![-707, -56, 7]] where
    su := ![![2877, 0, 0], ![1428, 21, 0]]
    hsu := by decide
    w := ![![1491, -105, 0], ![-75747, -5691, 777]]
    hw := by decide
    g := ![![![60, 89, 12], ![-11, 0, 0]], ![![56, 55, 7], ![-6, 0, 0]]]
    h := ![![![21627, 590, 4], ![-43571, -548, 0]], ![![-1109899, -31302, -220], ![2236067, 30177, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N2 : Ideal.span {21} * I137N2 =  Ideal.span {B.equivFun.symm ![71, -5, 0]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E137RS2 
