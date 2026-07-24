import IdealArithmetic.Examples.NF3_1_172019_1.PrimesBelow3_1_172019_1F1
import IdealArithmetic.Examples.NF3_1_172019_1.ClassGroupData3_1_172019_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 7 ![![37, 0, 0], ![-17, 1, 0]]
  ![-79, -22, 4] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![259, 0, 0], ![-119, 7, 0]]
    hsu := by decide
    w := ![![-553, -154, 28], ![385, 63, -14]]
    hw := by decide
    g := ![![![-15, -54, -48], ![-4, 328, 0]], ![![3, 21, 20], ![4, -138, 0]]]
    h := ![![![-11235, 764, -6], ![-24448, 226, 0]], ![![7861, -514, 3], ![17106, -113, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {7} * I37N1 =  Ideal.span {B.equivFun.symm ![-79, -22, 4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 49 ![![41, 0, 0], ![-15, 1, 0]]
  ![-4805, -2301, -330] ![![49, 0, 0], ![-20, 1, 0]] where
    su := ![![2009, 0, 0], ![-735, 49, 0]]
    hsu := by decide
    w := ![![-235445, -112749, -16170], ![57820, 27685, 3969]]
    hw := by decide
    g := ![![![-317969, -44538282, 2227708], ![-779138, -109157761, 0]], ![![104659, 14658676, -733195], ![256466, 35926585, 0]]]
    h := ![![![-28390, 1993, -19], ![-77279, 449, 0]], ![![6980, -480, 4], ![19000, -83, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {49} * I41N1 =  Ideal.span {B.equivFun.symm ![-4805, -2301, -330]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E41RS1 


noncomputable def E53RS1 : RelationCertificate Table 49 ![![53, 0, 0], ![21, 1, 0]]
  ![-2451, -1159, 184] ![![49, 0, 0], ![-20, 1, 0]] where
    su := ![![2597, 0, 0], ![1029, 49, 0]]
    hsu := by decide
    w := ![![-120099, -56791, 9016], ![70364, 28273, -4655]]
    hw := by decide
    g := ![![![31049, 4206173, -210275], ![73205, 10307412, 0]], ![![20209, 2752126, -137596], ![47946, 6744356, 0]]]
    h := ![![![-971679, -62554, -771], ![2452216, 41047, 0]], ![![567898, 36561, 451], ![-1433198, -23998, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {49} * I53N1 =  Ideal.span {B.equivFun.symm ![-2451, -1159, 184]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS1 


noncomputable def E59RS0 : RelationCertificate Table 7 ![![59, 0, 0], ![-29, 1, 0]]
  ![-88475, -42372, -6079] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![413, 0, 0], ![-203, 7, 0]]
    hsu := by decide
    w := ![![-619325, -296604, -42553], ![-793639, -380086, -54530]]
    hw := by decide
    g := ![![![987, 199, -82], ![176, 236, 0]], ![![-579, -113, 44], ![-94, -117, 0]]]
    h := ![![![-18239082, 748223, -4243], ![-37104047, 244258, 0]], ![![-23372682, 958812, -5437], ![-47547409, 312993, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {7} * I59N0 =  Ideal.span {B.equivFun.symm ![-88475, -42372, -6079]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 7 ![![59, 0, 0], ![-16, 1, 0]]
  ![-135, -15, 4] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![413, 0, 0], ![-112, 7, 0]]
    hsu := by decide
    w := ![![-945, -105, 28], ![329, 14, -7]]
    hw := by decide
    g := ![![![-14, -15, -9], ![3, 56, 0]], ![![1, 2, 2], ![5, -13, 0]]]
    h := ![![![-16069, 1069, -4], ![-59246, 240, 0]], ![![5629, -368, 1], ![20754, -60, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {7} * I59N1 =  Ideal.span {B.equivFun.symm ![-135, -15, 4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 7 ![![59, 0, 0], ![-15, 1, 0]]
  ![955, -72, -6] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![413, 0, 0], ![-105, 7, 0]]
    hsu := by decide
    w := ![![6685, -504, -42], ![259, 637, -84]]
    hw := by decide
    g := ![![![-2499, -18712, -17942], ![-3028, 124184, 0]], ![![282, 2988, 2912], ![471, -20216, 0]]]
    h := ![![![1445, -98, 0], ![5620, -6, 0]], ![![83, 8, -1], ![324, 47, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {7} * I59N2 =  Ideal.span {B.equivFun.symm ![955, -72, -6]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS2 


noncomputable def E71RS1 : RelationCertificate Table 49 ![![71, 0, 0], ![-23, 1, 0]]
  ![823, 72, -22] ![![49, 0, 0], ![-20, 1, 0]] where
    su := ![![3479, 0, 0], ![-1127, 49, 0]]
    hsu := by decide
    w := ![![40327, 3528, -1078], ![-19012, -1519, 490]]
    hw := by decide
    g := ![![![-1083051, -151680249, 7586719], ![-2653447, -371749269, 0]], ![![347131, 48612788, -2431507], ![850465, 119143851, 0]]]
    h := ![![![11877, -545, 1], ![36628, -93, 0]], ![![-5576, 268, -1], ![-17196, 81, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {49} * I71N1 =  Ideal.span {B.equivFun.symm ![823, 72, -22]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 49 ![![73, 0, 0], ![14, 1, 0]]
  ![257, -8, -3] ![![49, 0, 0], ![-20, 1, 0]] where
    su := ![![3577, 0, 0], ![686, 49, 0]]
    hsu := by decide
    w := ![![12593, -392, -147], ![-5488, 294, 49]]
    hw := by decide
    g := ![![![-47, -9312, 466], ![-123, -22824, 0]], ![![-6, -1858, 93], ![-17, -4554, 0]]]
    h := ![![![133291, 9955, 31], ![-694999, -2266, 0]], ![![-58100, -4346, -14], ![302942, 1023, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {49} * I73N1 =  Ideal.span {B.equivFun.symm ![257, -8, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 7 ![![79, 0, 0], ![19, 1, 0]]
  ![159, 76, 11] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![553, 0, 0], ![133, 7, 0]]
    hsu := by decide
    w := ![![1113, 532, 77], ![1435, 686, 98]]
    hw := by decide
    g := ![![![76, 6, 0], ![15, -14, 0]], ![![15, 2, 1], ![6, -10, 0]]]
    h := ![![![794, 40, 0], ![-3293, 11, 0]], ![![1050, 53, 0], ![-4355, 14, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {7} * I79N1 =  Ideal.span {B.equivFun.symm ![159, 76, 11]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS1 
