import IdealArithmetic.Examples.NF3_1_649415_1.PrimesBelow3_1_649415_1F4
import IdealArithmetic.Examples.NF3_1_649415_1.ClassGroupData3_1_649415_1

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 729 ![![197, 0, 0], ![-36, 1, 0]]
  ![467, 93, -61] ![![729, 0, 0], ![-328, 1, 0]] where
    su := ![![143613, 0, 0], ![-26244, 729, 0]]
    hsu := by decide
    w := ![![340443, 67797, -44469], ![-162567, -30618, 20412]]
    hw := by decide
    g := ![![![71365978240656, -15711330950599036, 238775145297852], ![-53661689729923, -34813416184426830, 0]], ![![-13101873367062, 2884397770734922, -43836037759600], ![9851594286924, 6391294305349681, 0]]]
    h := ![![![22183, -431368, 58297], ![-6229, -2296914, 0]], ![![-10589, 206009, -27841], ![3002, 1096941, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {729} * I197N1 =  Ideal.span {B.equivFun.symm ![467, 93, -61]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E197RS1 


noncomputable def E223RS1 : RelationCertificate Table 81 ![![223, 0, 0], ![-47, 1, 0]]
  ![-71, 15, -2] ![![81, 0, 0], ![-4, 1, 0]] where
    su := ![![18063, 0, 0], ![-3807, 81, 0]]
    hsu := by decide
    w := ![![-5751, 1215, -162], ![0, -162, 81]]
    hw := by decide
    g := ![![![517221242, -1297671145, 1298184261], ![-41562373, -21030585026, 0]], ![![-107553519, 269844097, -269950797], ![8642696, 4373202911, 0]]]
    h := ![![![-2189755, 56159815, -5850314], ![713462, 260924004, 0]], ![![315, -7747, 807], ![-37, -35992, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N1 : Ideal.span {81} * I223N1 =  Ideal.span {B.equivFun.symm ![-71, 15, -2]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E223RS1 


noncomputable def E227RS1 : RelationCertificate Table 243 ![![227, 0, 0], ![3, 1, 0]]
  ![-6851, -435, 463] ![![243, 0, 0], ![-85, 1, 0]] where
    su := ![![55161, 0, 0], ![729, 243, 0]]
    hsu := by decide
    w := ![![-1664793, -105705, 112509], ![654156, 34263, -41067]]
    hw := by decide
    g := ![![![-22952146729024, 1180732262456207, -68650307992606], ![12887509195396, 3336404968442298, 0]], ![![-286480882541, 14737498180177, -856869775882], ![160857502953, 41643871107965, 0]]]
    h := ![![![256590, 256660, 641709], ![4737, -29133496, 0]], ![![-100842, -100867, -252187], ![-1562, 11449256, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {243} * I227N1 =  Ideal.span {B.equivFun.symm ![-6851, -435, 463]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E227RS1 
